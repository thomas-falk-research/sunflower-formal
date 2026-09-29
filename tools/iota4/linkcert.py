#!/usr/bin/env python3
"""Link certificates for the descent of docs/roadmap.md §64.

Setting. F is 4-uniform and 3-sunflower-free, R is a member whose link
D = {C in F : C disjoint from R} is as large as any link in F, Delta = |D|,
V = union of D. Every other member meets R. M0 = members missing V
(R is one), and every remaining member S has a nonempty trace T = S & V
with |T| <= 3 that is *unwitnessed* in D (no C1 != C2 in D with
T&C1 == T&C2 == C1&C2, else S, C1, C2 is a sunflower). With n_T the
number of members with trace T:

  (a) for each C in D:  m0 + sum_{T : T & C empty} n_T <= Delta
      (all of these are disjoint from C, and |link(C)| <= Delta);
  (b) n_T <= 2, 6, 26 for |T| = 3, 2, 1
      (the outer parts of the members with trace T form a sunflower-free
       family of (4-|T|)-sets: g(1) = 2, g(2) <= 6, g(3) <= 26, the last
       two kernel theorems in coq/PureLink.v);
  (c) 0 <= m0 <= 27 (M0 is intersecting: two disjoint members of it and
      any C in D would be pairwise disjoint).

So |F| - Delta = m0 + sum n_T is at most the LP maximum. A dual
certificate (y_C, z_T, w >= 0) with
  sum_C y_C + w >= 1,  sum_{C : T&C empty} y_C + z_T >= 1  (every T)
bounds it by Delta*sum y + sum cap_T z_T + 27 w (weak duality).

  linkcert.py solve CLASSES.gz CERTS.json.gz    find certificates (scipy/HiGHS)
  linkcert.py check CLASSES.gz CERTS.json.gz    verify them exactly (fractions only)

`check` needs no solver: it recomputes each class's unwitnessed traces and
checks every inequality in exact rational arithmetic.
"""
import sys, json, gzip, itertools
from fractions import Fraction as Fr

CAP = {1: 26, 2: 6, 3: 2}


def load(path):
    op = gzip.open if path.endswith(".gz") else open
    fams = []
    for line in op(path, "rt"):
        if "BIG" not in line:
            continue
        p = line.split()
        p = p[p.index("BIG"):]
        F = [frozenset(i for i in range(128) if int(h, 16) >> i & 1) for h in p[3:]]
        assert len(F) == int(p[1])
        fams.append(F)
    return fams


def validate(F):
    assert all(len(S) == 4 for S in F) and len(set(F)) == len(F)
    assert all(a & b for a, b in itertools.combinations(F, 2))
    assert not any((a & b) == (a & c) == (b & c) for a, b, c in itertools.combinations(F, 3))


def unwitnessed(F):
    V = sorted(set().union(*F))
    pairs = [(a, b, a & b) for a, b in itertools.combinations(F, 2)]
    return [frozenset(T) for t in (1, 2, 3) for T in itertools.combinations(V, t)
            if not any((frozenset(T) & a) == K and (frozenset(T) & b) == K for a, b, K in pairs)]


def solve(F, B):
    import numpy as np
    from scipy.optimize import linprog
    nC, nz = len(F), len(B)
    cost = [len(F)] * nC + [CAP[len(T)] for T in B] + [27]
    A = [[-1] * nC + [0] * nz + [-1]]
    for j, T in enumerate(B):
        row = [-1 if not (T & C) else 0 for C in F] + [0] * nz + [0]
        row[nC + j] = -1
        A.append(row)
    r = linprog(cost, A_ub=np.array(A), b_ub=[-1] * (1 + nz),
                bounds=[(0, None)] * (nC + nz + 1), method="highs")
    assert r.status == 0
    # round to small rationals; `check` decides whether the rounding survived
    x = [Fr(v).limit_denominator(1000) for v in r.x]
    return {"y": [str(v) for v in x[:nC]], "z": [str(v) for v in x[nC:nC + nz]], "w": str(x[-1])}


def check(F, B, cert):
    y = [Fr(v) for v in cert["y"]]
    z = [Fr(v) for v in cert["z"]]
    w = Fr(cert["w"])
    assert len(y) == len(F) and len(z) == len(B)
    assert min(y + z + [w]) >= 0
    assert sum(y) + w >= 1
    for j, T in enumerate(B):
        assert sum(y[i] for i, C in enumerate(F) if not (T & C)) + z[j] >= 1
    return len(F) * sum(y) + sum(CAP[len(T)] * z[j] for j, T in enumerate(B)) + 27 * w


if __name__ == "__main__":
    mode, cls, certs = sys.argv[1:4]
    fams = load(cls)
    if mode == "solve":
        out = []
        for F in fams:
            validate(F)
            out.append(solve(F, unwitnessed(F)))
        with gzip.open(certs, "wt") as f:
            json.dump(out, f)
        print("wrote", len(out), "certificates")
    else:
        C = json.load(gzip.open(certs, "rt"))
        assert len(C) == len(fams)
        worst, fail = {}, []
        for k, (F, c) in enumerate(zip(fams, C)):
            validate(F)
            bound = check(F, unwitnessed(F), c)
            d = len(F)
            if bound > 54 - d:
                fail.append((k, d, bound))
            worst[d] = max(worst.get(d, 0), bound)
        for d in sorted(worst, reverse=True):
            n = sum(len(F) == d for F in fams)
            nf = sum(f[1] == d for f in fail)
            print(f"Delta={d}: {n} classes, largest certified |F| - Delta = {worst[d]}"
                  f" (allowed {54 - d}), failing {nf}")
        if fail:
            print("CHECK FAIL:", len(fail), "classes not certified; first:", fail[:5])
            sys.exit(1)
        print("CHECK PASS: every class certifies |F| <= 54")
