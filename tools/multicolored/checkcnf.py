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
             with a different SAT solver (Glucose 4): every assignment,
             both directions, when an encoding has at most 12 input
             literals; otherwise random and boundary samples. For a
             sampled encoding, that every allowed assignment extends to
             the auxiliary variables (the direction an unsatisfiability
             verdict needs) is an assumption, recorded in section 83.
The run-class argument (the union of the run classes covers every Phi) is
section 81.1's, not something a per-clause check can establish.

    python3 -I tools/multicolored/checkcnf.py CNF D n K s r [samples]
    python3 -I tools/multicolored/checkcnf.py cover LEAVES.json
    python3 -I tools/multicolored/checkcnf.py delta DELTA.cnf D n K r LEAVES.json k

cover (section 84) recomputes cubes.py's cube tree from the definitions,
with its own implementation of the symmetry group, compares it with the
leaf list, and checks that every expanded node fixes fewer than s triples
(the hypothesis of Lemma 84.A). delta checks one cube's delta file: Farkas clauses exactly,
plus exactly the leaf's units. Together with the base CNF's check, these
make every clause of a cube's full CNF (base + delta) checked.

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


def pairs(T, D, n):
    """The pairs no free face contains: one fibre, Lemma 81.A, Lemma 83.A."""
    N, A = len(T), D ** n
    Tn = np.array(T)
    idx = -np.ones((A, A, A), np.int64)
    idx[Tn[:, 0], Tn[:, 1], Tn[:, 2]] = np.arange(N)
    inS = idx >= 0
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
    return Tn, idx, badpair


def exact(T, A, L, M):
    """Is there a rational x != 0 on L + M with sum_t x_t v_t = 0, x >= 0 on M
    and sum_M x > 0? Tries each vector of an exact kernel basis."""
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
    for fc in free:
        x = [Fraction(0)] * m
        x[fc] = Fraction(1)
        for j, c in enumerate(pivots):
            x[c] = -rows[j][fc]
        xm = x[len(L):]
        for sgn in (1, -1):
            if all(sgn * v >= 0 for v in xm) and sgn * sum(xm) > 0:
                return True
    return False


def read_cnf(path):
    with open(path) as f:
        header = f.readline().split()
        nv, ncl = int(header[2]), int(header[3])
        clauses = []
        for line in f:
            toks = list(map(int, line.split()))
            assert toks and toks[-1] == 0 and 0 not in toks[:-1], line   # one clause per line
            clauses.append(toks[:-1])
    assert len(clauses) == ncl, (len(clauses), ncl)
    return nv, clauses


def group(D, n, T):
    """Sym(D)^n x| S_n x S_3 as permutations of the indices of T (each letter
    of each coordinate permuted, coordinates permuted, legs permuted)."""
    A = D ** n
    index = {t: k for k, t in enumerate(T)}
    digs = []
    for w in range(A):
        d = []
        for _ in range(n):
            d.append(w % D)
            w //= D
        digs.append(d[::-1])                    # most significant coordinate first
    out = []
    for sig in itertools.product(list(itertools.permutations(range(D))), repeat=n):
        for pi in itertools.permutations(range(n)):
            wm = []
            for w in range(A):
                x = 0
                for k in range(n):
                    x = x * D + sig[k][digs[w][pi[k]]]
                wm.append(x)
            for rho in itertools.permutations(range(3)):
                out.append([index[(wm[t[rho[0]]], wm[t[rho[1]]], wm[t[rho[2]]])] for t in T])
    return np.array(out, dtype=np.int64)


def mask(xs):
    m = 0
    for x in xs:
        m |= 1 << x
    return m


def forbidden_of(leaf):
    """A leaf's forbidden set: a list, or a hexadecimal bitmask (bit k = triple k)."""
    f = leaf["forbidden"]
    if isinstance(f, list):
        return set(f)
    m = int(f, 16)
    return {k for k in range(m.bit_length()) if m >> k & 1}


def canon(leaf):
    return (list(leaf["path"]), list(leaf["fixed"]), mask(forbidden_of(leaf)), leaf["group_order"])


def cover(path):
    """Recompute the cube tree of cubes.py from the definitions and compare."""
    spec = json.load(open(path))
    D, n, r = spec["D"], spec["n"], spec["run"]
    if spec.get("expand") is not None:
        expand = {tuple(p) for p in spec["expand"]}
        grow = lambda p: p in expand
    else:
        grow = lambda p: len(p) < spec["depth"]
    T, mono = support(D, n)
    N = len(T)
    _, _, bad = pairs(T, D, n)
    G = group(D, n, T)
    assert len({tuple(g) for g in G.tolist()}) == len(G), "group elements not distinct"
    rep = min(k for k in range(N) if mono[k] == r)
    allowed = [m <= r for m in mono]
    mine, stack, expanded, small = [], [((), (rep,), set(), G[G[:, rep] == rep])], 0, True
    while stack:
        p, fixed, forb, H = stack.pop(0)
        if not grow(p):
            mine.append({"path": list(p), "fixed": list(fixed), "forbidden": sorted(forb), "group_order": len(H)})
            continue
        expanded += 1
        small = small and len(fixed) < spec["s"]  # Lemma 84.A needs |F| < s at every expanded node
        cand = [k for k in range(N) if allowed[k] and k not in fixed and k not in forb
                and not any(bad[f, k] for f in fixed)]
        orbits, seen = [], set()
        for k in cand:
            if k not in seen:
                orb = set(H[:, k].tolist())
                assert orb <= set(cand), "candidates not invariant"
                seen |= orb
                orbits.append(orb)
        acc, kids = set(forb), []
        for j, orb in enumerate(orbits):
            o = min(orb)
            kids.append((p + (j,), fixed + (o,), set(acc), H[H[:, o] == o]))
            acc |= orb
        stack = kids + stack
    ok = len(mine) == len(spec["leaves"]) and small and all(
        canon(x) == canon(y) for x, y in zip(mine, spec["leaves"]))
    if spec.get("expand") is not None:          # every expanded node must exist in the tree
        ok = ok and expanded == len(spec["expand"])
    print(json.dumps({"leaves": path, "D": D, "n": n, "run": r, "group_order": len(G),
                      "root_stabiliser": int((G[:, rep] == rep).sum()), "expanded_nodes": expanded,
                      "fixed_below_s_at_every_expanded_node": small,
                      "leaf_count": len(mine), "ok": ok}))


def delta(path, D, n, K, r, leaves_path, k):
    """A cube's delta file: every clause must be an exact Farkas clause or one
    of the leaf's units, and every unit of the leaf must be present."""
    T, mono = support(D, n)
    N, A = len(T), D ** n
    leaf = json.load(open(leaves_path))["leaves"][k]
    want = {f + 1 for f in leaf["fixed"]} | {-(x + 1) for x in forbidden_of(leaf)}
    _, clauses = read_cnf(path)
    kinds, fails, got = Counter(), [], set()
    for cl in clauses:
        if len(cl) == 1 and cl[0] in want:
            got.add(cl[0])
            kinds["leaf unit"] += 1
            continue
        if not cl or any(abs(l) > N for l in cl):
            fails.append(("not a Farkas clause", cl))
            continue
        L = sorted(-l - 1 for l in cl if l < 0)
        M = sorted(l - 1 for l in cl if l > 0)
        if M and exact(T, A, L, M):
            kinds["Farkas"] += 1
        else:
            fails.append(("unexplained", cl))
    if got != want:
        fails.append(("leaf units missing", len(want - got)))
    print(json.dumps({"delta": path, "cube": k, "clauses": len(clauses), "checked": dict(kinds),
                      "ok": not fails, "failures": fails[:10]}))


def main():
    path = sys.argv[1]
    D, n, K, s, r = (int(x) for x in sys.argv[2:7])
    samples = int(sys.argv[7]) if len(sys.argv) > 7 else 200
    T, mono = support(D, n)
    N, A = len(T), D ** n
    Tn, idx, badpair = pairs(T, D, n)

    nv, clauses = read_cnf(path)
    ncl = len(clauses)
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

    for cl in other:
        L = sorted(-l - 1 for l in cl if l < 0)
        M = sorted(l - 1 for l in cl if l > 0)
        if M and exact(T, A, L, M):
            kinds["Farkas"] += 1
        else:
            fails.append(("unexplained", cl))

    if +pending:
        fails.append(("regenerated encoding clauses missing from the CNF", sum(pending.values())))
    rng = random.Random(83)
    sem_fail, exhaustive = 0, 0
    for kind, lits, cls in groups:
        bound = K if kind == "cap" else s
        if len(lits) <= 12:                     # small encodings: every assignment, both directions
            exhaustive += 1
            with Solver(name="glucose4", bootstrap_with=cls) as g:
                for bits in itertools.product((0, 1), repeat=len(lits)):
                    allowed = sum(bits) <= K if kind == "cap" else sum(bits) >= s
                    if g.solve(assumptions=[l if b else -l for l, b in zip(lits, bits)]) != allowed:
                        sem_fail += 1
            continue
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
                      "checked": dict(kinds), "encodings_exhaustive": exhaustive,
                      "encodings_sampled": len(groups) - exhaustive, "samples_each": samples,
                      "ok": not fails, "failures": fails[:10]}))


if __name__ == "__main__":
    if sys.argv[1] == "cover":
        cover(sys.argv[2])
    elif sys.argv[1] == "delta":
        delta(sys.argv[2], *(int(x) for x in sys.argv[3:7]), sys.argv[7], int(sys.argv[8]))
    else:
        main()
