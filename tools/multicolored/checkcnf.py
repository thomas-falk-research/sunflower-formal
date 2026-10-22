#!/usr/bin/env python3
"""Independent check that every clause of a satmaster.py CNF is valid.

docs/roadmap.md section 83. A clause is valid when every free face Phi of
S_D^(n) with at most K uses per word per leg, |Phi| >= s, in run class r
satisfies it (with suitable values of the auxiliary variables). Then an
unsatisfiability proof of the CNF (DRAT, checked by drat-trim) shows that no
such Phi exists in run class r.

This file shares no code with benders.py or satmaster.py. It rebuilds
S_D^(n) and its variable numbering from the definitions and checks each
clause on its own:
  unit       the one positive unit is a triple with r monochromatic
             coordinates; each negative unit is a triple with more
  pair       two triples in one fibre, or a Lemma 81.A pair, or a
             Lemma 83.A pair
  three-set  some leg-permutation relation sum_P v = sum_Q v with Q in S
             makes P u Q unfree, or contain a Lemma 81.A or 83.A pair, or
             use a word more than K times (Corollary 82.B)
  Horn       (not p1, not p2, not p3, q): some leg-permutation relation with
             Q in S has q in Q (Lemma 82.A)
  Farkas     negative literals L, positive literals M: an exact rational
             x != 0 with sum_t x_t v_t = 0, x >= 0 on M, sum_M x > 0
             (then no face contains L and avoids M)
  auxiliary  clauses with auxiliary variables must equal, as a multiset,
             PySAT's encodings regenerated with satmaster.py's parameters,
             and the encodings are tested semantically on random assignments
             with a different SAT solver (Glucose 4). That PySAT's
             encoders are correct is an assumption, recorded in section 83.
The run-class argument (the union of the run classes covers every Phi) is
section 81.1's, not something a per-clause check can establish.

    python3 -I tools/multicolored/checkcnf.py CNF D n K s r [samples]

Requires numpy and python-sat==1.9.dev15 (for the encodings only).
"""
import itertools, json, random, sys
from collections import Counter
from fractions import Fraction

import numpy as np


def support(D, n):
    s1 = [t for t in itertools.product(range(D), repeat=3) if len(set(t)) in (1, 3)]
    T = []
    for combo in itertools.product(s1, repeat=n):
        w = [0, 0, 0]
        for t in combo:
            for i in range(3):
                w[i] = w[i] * D + t[i]
        T.append(tuple(w))
    mono = [sum(1 for t in combo if t[0] == t[1] == t[2]) for combo in itertools.product(s1, repeat=n)]
    return T, mono


def main():
    path = sys.argv[1]
    D, n, K, s, r = (int(x) for x in sys.argv[2:7])
    samples = int(sys.argv[7]) if len(sys.argv) > 7 else 200
    T, mono = support(D, n)
    N, A = len(T), D ** n
    Tn = np.array(T)
    idx = -np.ones((A, A, A), np.int64)
    idx[Tn[:, 0], Tn[:, 1], Tn[:, 2]] = np.arange(N)
    inS = idx >= 0
    # pair relations, computed from the definitions
    agree = sum((Tn[:, None, i] == Tn[None, :, i]).astype(int) for i in range(3))
    fibre = agree == 2
    rect = np.zeros((N, N), bool)
    for i in range(3):
        sw_a = [Tn[:, None, j] if j != i else Tn[None, :, j] for j in range(3)]    # a with leg i from b
        sw_b = [Tn[None, :, j] if j != i else Tn[:, None, j] for j in range(3)]    # b with leg i from a
        ca = inS[np.broadcast_to(sw_a[0], (N, N)), np.broadcast_to(sw_a[1], (N, N)), np.broadcast_to(sw_a[2], (N, N))]
        cb = inS[np.broadcast_to(sw_b[0], (N, N)), np.broadcast_to(sw_b[1], (N, N)), np.broadcast_to(sw_b[2], (N, N))]
        rect |= ca & cb & (Tn[:, None, i] != Tn[None, :, i])
    tpo = agree == 0
    for i in range(3):
        sw = [Tn[:, None, j] if j != i else Tn[None, :, j] for j in range(3)]
        tpo &= inS[np.broadcast_to(sw[0], (N, N)), np.broadcast_to(sw[1], (N, N)), np.broadcast_to(sw[2], (N, N))]
    tpo |= tpo.T
    badpair = fibre | rect | tpo
    np.fill_diagonal(badpair, False)

    with open(path) as f:
        header = f.readline().split()
        nv, ncl = int(header[2]), int(header[3])
        clauses = [list(map(int, line.split()[:-1])) for line in f]
    assert len(clauses) == ncl, (len(clauses), ncl)
    # the cardinality encodings, regenerated with satmaster.py's parameters
    from pysat.card import CardEnc, EncType
    from pysat.solvers import Solver
    top = N
    regen, groups = [], []
    for i in range(3):
        use = {}
        for k, t in enumerate(T):
            use.setdefault(t[i], []).append(k + 1)
        for lits in use.values():
            if len(lits) > K:
                enc = CardEnc.atmost(lits, bound=K, top_id=top, encoding=EncType.seqcounter)
                top = max(top, enc.nv)
                regen += enc.clauses
                groups.append(("cap", lits, enc.clauses))
    if s <= N:
        enc = CardEnc.atleast(list(range(1, N + 1)), bound=s, top_id=top, encoding=EncType.cardnetwrk)
        top = max(top, enc.nv)
        regen += enc.clauses
        groups.append(("size", list(range(1, N + 1)), enc.clauses))
    pending = Counter(tuple(sorted(c)) for c in regen)
    kinds = Counter()
    fails = []
    pos_units = []
    tern, horn, other = [], [], []
    for cl in clauses:
        key = tuple(sorted(cl))
        if pending[key] > 0:
            pending[key] -= 1
            kinds["encoding"] += 1
            continue
        if not cl:
            kinds["empty (s > |S|)"] += 1
            if s <= N:
                fails.append(("empty clause", cl))
            continue
        if any(abs(l) > N for l in cl):
            fails.append(("auxiliary clause not in the regenerated encodings", cl))
            continue
        neg = [-l - 1 for l in cl if l < 0]
        pos = [l - 1 for l in cl if l > 0]
        if len(cl) == 1:
            if pos:
                pos_units.append(pos[0])
                ok = mono[pos[0]] == r
            else:
                ok = mono[neg[0]] > r
            kinds["unit"] += 1
            if not ok:
                fails.append(("unit", cl))
        elif not pos and len(neg) == 2 and badpair[neg[0], neg[1]]:
            kinds["pair"] += 1
        elif not pos and len(neg) == 3:
            tern.append(sorted(neg))
        elif len(pos) == 1 and len(neg) == 3:
            horn.append((sorted(neg), pos[0], cl))
        else:
            other.append(cl)
    if len(pos_units) != 1:
        fails.append(("positive units", pos_units))

    perms = list(itertools.permutations(range(3)))
    st = [(a, b) for a in perms for b in perms if a != (0, 1, 2) or b != (0, 1, 2)]

    def images(P):
        """For each (sigma, tau): the indices of Q (or -1 where outside S)."""
        X, Y, Z = Tn[P, 0], Tn[P, 1], Tn[P, 2]          # M x 3
        for a, b in st:
            yield idx[X, Y[:, list(a)], Z[:, list(b)]]

    # three-set conflicts
    if tern:
        P = np.array(tern)
        ok = np.zeros(len(P), bool)
        for Q in images(P):
            inq = (Q >= 0).all(1)
            U = np.concatenate([P, np.where(Q >= 0, Q, 0)], 1)
            c = np.zeros(len(P), bool)
            for u in range(6):
                for w in range(u + 1, 6):
                    c |= (U[:, u] != U[:, w]) & badpair[U[:, u], U[:, w]]
            first = np.ones((len(P), 6), bool)
            for w in range(1, 6):
                for u in range(w):
                    first[:, w] &= U[:, w] != U[:, u]
            for leg in range(3):
                W = Tn[U, leg]
                for u in range(6):
                    c |= ((W == W[:, u:u + 1]) & first).sum(1) > K
            ok |= inq & c
        kinds["three-set"] += int(ok.sum())
        for k in np.where(~ok)[0]:
            other.append([-(x + 1) for x in tern[k]])          # retried below (it fails: no positive literal)
    # Horn
    if horn:
        P = np.array([h[0] for h in horn])
        q = np.array([h[1] for h in horn])
        ok = np.zeros(len(P), bool)
        for Q in images(P):
            ok |= (Q >= 0).all(1) & (Q == q[:, None]).any(1)
        kinds["Horn"] += int(ok.sum())
        for k in np.where(~ok)[0]:
            other.append(horn[k][2])

    # Farkas clauses, exactly
    def exact(L, M):
        cols = L + M
        rows = []
        for i in range(3):
            for wd in range(A):
                row = [Fraction(int(T[t][i] == wd)) for t in cols]
                if any(row):
                    rows.append(row)
        m = len(cols)
        pivots, rk = [], 0
        for c in range(m):
            p = next((j for j in range(rk, len(rows)) if rows[j][c] != 0), None)
            if p is None:
                continue
            rows[rk], rows[p] = rows[p], rows[rk]
            rows[rk] = [x / rows[rk][c] for x in rows[rk]]
            for j in range(len(rows)):
                if j != rk and rows[j][c] != 0:
                    f = rows[j][c]
                    rows[j] = [x - f * y for x, y in zip(rows[j], rows[rk])]
            pivots.append(c)
            rk += 1
        free = [c for c in range(m) if c not in pivots]
        for fc in free:                                  # try each kernel basis vector
            x = [Fraction(0)] * m
            x[fc] = Fraction(1)
            for j, c in enumerate(pivots):
                x[c] = -rows[j][fc]
            xm = x[len(L):]
            for sgn in (1, -1):
                if all(sgn * v >= 0 for v in xm) and sgn * sum(xm) > 0:
                    return True
        return False
    for cl in other:
        L = sorted(-l - 1 for l in cl if l < 0)
        M = sorted(l - 1 for l in cl if l > 0)
        if M and exact(L, M):
            kinds["Farkas"] += 1
        else:
            fails.append(("unexplained", cl))

    if +pending:
        fails.append(("regenerated encoding clauses missing from the CNF", sum(pending.values())))
    rng = random.Random(83)
    sem_fail = 0
    for kind, lits, cls in groups:
        bound = K if kind == "cap" else s
        for j in range(samples):
            # half the samples sit at the boundary (bound - 1, bound, bound + 1)
            want = (min(max(bound + rng.choice((-1, 0, 1)), 0), len(lits)) if j % 2
                    else rng.randint(0, len(lits)))
            on = set(rng.sample(lits, want))
            allowed = want <= K if kind == "cap" else want >= s
            with Solver(name="glucose4", bootstrap_with=cls) as g:
                sat = g.solve(assumptions=[l if l in on else -l for l in lits])
            if sat != allowed:
                sem_fail += 1
    if sem_fail:
        fails.append(("encoding semantics", sem_fail))
    print(json.dumps({"cnf": path, "D": D, "n": n, "K": K, "s": s, "run": r, "vars": nv, "clauses": ncl,
                      "checked": dict(kinds), "encoding_samples": samples * len(groups),
                      "ok": not fails, "failures": fails[:10]}))


if __name__ == "__main__":
    main()
