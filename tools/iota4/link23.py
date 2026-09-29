#!/usr/bin/env python3
"""Type-level bound on |F| - Delta for link classes the LP of linkcert.py
cannot certify (docs/roadmap.md §65).

Setting as in linkcert.py: F 4-uniform, 3-sunflower-free; R has a link
D = D(R) of size Delta, the largest link in F; V = points of D. Every
member outside D meets R, and R misses V. Each such member S has
  trace   T = S & V   (empty, or an unwitnessed trace of D, |T| <= 3),
  profile P = S & R   (nonempty),
  extras  e = 4 - |T| - |P| points outside V and R.
M0 types: T empty, P a nonempty proper subset of R (P = R would be R).
M1 types: T unwitnessed, e >= 0.
n[type] = number of members of that type (R itself is counted apart).

Constraints (each is a consequence of sunflower-freeness, or of Delta being
the largest link; the argument for each is next to it):

 ub   n <= 1, 2, 6 for M1 types with e = 0, 1, 2; n <= 1, 3, 26 for M0 types
      with |P| = 3, 2, 1.
 capT sum over P of n[(T, P)] <= 2, 6, 26 for |T| = 3, 2, 1.
 C    for each C in D: sum of M0 types + M1 types with T & C empty <= Delta - 1.
 star for each r in R: sum of types with r in P <= 25.
 det  for a determined M1 type a (e = 0, so the member is T | P exactly):
      - link: a present => (members disjoint from a) <= Delta - #{C in D : C & T empty};
      - pairwise exclusions with any M1 or M0 type b, where the intersection
        with a is known exactly (see `exclusions`).

  link23.py solve CLASSES.gz INDEX...   integer optimum (scipy/HiGHS)
  link23.py cnf CLASSES.gz INDEX OUT    CNF satisfiable iff the model allows |F| >= 55
"""
import sys, itertools
sys.path.insert(0, __import__("os").path.dirname(__file__))
from linkcert import load, unwitnessed, validate

G3 = 26                       # kernel: PureLink.g_three_at_most_26
R = range(4)
PROFILES = [frozenset(p) for t in (1, 2, 3, 4) for p in itertools.combinations(R, t)]


def model(D):
    """Return (types, ub, cons). cons entries:
       ('le', [i...], k)            sum n_i <= k
       ('if_le', a, [i...], k)      n_a >= 1  =>  sum n_i <= k
       ('excl', a, b)               n_a >= 1  =>  n_b = 0     (a is determined)"""
    validate(D)                   # 4-uniform, distinct, intersecting, sunflower-free
    Delta = len(D)
    B = unwitnessed(D)
    types = [("M1", T, P) for T in B for P in PROFILES if len(T) + len(P) <= 4] + \
            [("M0", frozenset(), P) for P in PROFILES if len(P) < 4]
    def e(t): return 4 - len(t[1]) - len(t[2])
    ub = []
    for t in types:
        if t[0] == "M1":
            # same (T, P): members differ only in their e extras and pairwise meet
            # in T | P plus shared extras, so the extras form a sunflower-free
            # family of e-sets: g(0) = 1, g(1) = 2, g(2) <= 6.
            ub.append({0: 1, 1: 2, 2: 6}[e(t)])
        else:
            # u = P + extras, u & V empty. Two such u, u' meeting only in P
            # would make a sunflower with R (u & R = u' & R = P), so the extras
            # are also pairwise intersecting: |P| = 3: one extra point -> 1;
            # |P| = 2: an intersecting sunflower-free graph -> triangle, 3;
            # |P| = 1: sunflower-free 3-sets -> g(3) <= 26.
            ub.append({3: 1, 2: 3, 1: G3}[len(t[2])])
    idx = {t: i for i, t in enumerate(types)}
    transv = lambda X: all(X & C for C in D)
    cons = []
    # capT: outer parts of members with trace T are a sunflower-free family of
    # (4-|T|)-sets (they pairwise meet in T plus outer overlap).
    for T in B:
        cons.append(("le", [idx[t] for t in types if t[0] == "M1" and t[1] == T], {3: 2, 2: 6, 1: G3}[len(T)]))
    # C: every M0 member and every M1 member with T & C empty is disjoint from C
    # (C lies inside V), as is R; the link of C has at most Delta members.
    for C in D:
        cons.append(("le", [i for i, t in enumerate(types) if not (t[1] & C)], Delta - 1))
    # star: members through r, with r removed, are distinct 3-sets forming no
    # sunflower (one would lift, core + r); D has none through r; R is one.
    for r in R:
        cons.append(("le", [i for i, t in enumerate(types) if r in t[2]], G3 - 1))
    # determined members
    for a, ta in enumerate(types):
        if ta[0] != "M1" or e(ta) != 0:
            continue
        Ta, Pa = ta[1], ta[2]           # the member is exactly Ta | Pa, inside V | R
        # its link: C in D avoiding Ta, plus every type certainly disjoint from it
        # (a member's extras lie outside V | R, so they never meet Ta | Pa).
        avoid = sum(1 for C in D if not (Ta & C))
        dis = [i for i, t in enumerate(types) if i != a and not (t[1] & Ta) and not (t[2] & Pa)]
        cons.append(("if_le", a, dis, Delta - avoid))
        for b, tb in enumerate(types):
            if b == a:
                continue
            Tb, Pb = tb[1], tb[2]
            # the intersection of member a with any member of type b is exactly
            # (Ta & Tb) | (Pa & Pb): a has no extras, b's extras avoid V | R.
            K = (Ta & Tb) | (Pa & Pb)
            bad = False
            # sunflower with R: a & R = Pa, b & R = Pb; needs Pa == Pb == K.
            if Pa == Pb and K == Pa:
                bad = True
            # sunflower with C in D: a & C = Ta & C, b & C = Tb & C (C inside V).
            if any((Ta & C) == K and (Tb & C) == K for C in D):
                bad = True
            # three pairwise disjoint: a, b disjoint and some C avoids Ta | Tb.
            if not K and not transv(Ta | Tb):
                bad = True
            if bad:
                cons.append(("excl", a, b))
    return types, ub, cons


def solve(D, time_limit=600):
    import numpy as np
    from scipy.optimize import milp, LinearConstraint, Bounds
    types, ub, cons = model(D)
    n = len(types)
    big = sum(ub) + 1
    rows, lo, hi = [], [], []
    for c in cons:
        r = np.zeros(n)
        if c[0] == "le":
            for i in c[1]: r[i] += 1
            rows.append(r); lo.append(-np.inf); hi.append(c[2])
        elif c[0] == "if_le":            # sum + big * n_a <= k + big   (n_a in {0,1})
            for i in c[2]: r[i] += 1
            r[c[1]] += big
            rows.append(r); lo.append(-np.inf); hi.append(c[3] + big)
        else:                            # n_b + ub_b * n_a <= ub_b
            a, b = c[1], c[2]
            r[b] += 1; r[a] += ub[b]
            rows.append(r); lo.append(-np.inf); hi.append(ub[b])
    res = milp(-np.ones(n), constraints=LinearConstraint(np.array(rows), lo, hi),
               bounds=Bounds(np.zeros(n), np.array(ub, float)), integrality=np.ones(n),
               options={"time_limit": time_limit})
    assert res.status == 0, res.message
    return 1 + round(-res.fun)          # + R


def cnf(D, path):
    """CNF satisfiable iff some integer point of the model has |M| >= 55 - Delta.
    n_t is unary: slot literals s[t][0..ub-1] with s[t][j+1] -> s[t][j]."""
    from pysat.card import CardEnc, EncType
    from pysat.formula import IDPool
    types, ub, cons = model(D)
    Delta = len(D)
    pool = IDPool()
    s = [[pool.id(("s", t, j)) for j in range(ub[t])] for t in range(len(types))]
    cl = []
    for t in range(len(types)):
        for j in range(ub[t] - 1):
            cl.append([-s[t][j + 1], s[t][j]])
    def slots(ids): return [x for i in ids for x in s[i]]
    for c in cons:
        if c[0] == "le":
            lits = slots(c[1])
            if len(lits) > c[2]:
                cl += CardEnc.atmost(lits, bound=c[2], vpool=pool, encoding=EncType.seqcounter).clauses
        elif c[0] == "if_le":
            lits = slots(c[2]); k = c[3]
            if k < 0:
                cl.append([-s[c[1]][0]])
            elif len(lits) > k:
                for x in CardEnc.atmost(lits, bound=k, vpool=pool, encoding=EncType.seqcounter).clauses:
                    cl.append(x + [-s[c[1]][0]])
        else:
            cl.append([-s[c[1]][0], -s[c[2]][0]])
    need = 55 - Delta - 1                 # members other than D and R
    cl += CardEnc.atleast(slots(range(len(types))), bound=need, vpool=pool, encoding=EncType.seqcounter).clauses
    with open(path, "w") as f:
        f.write(f"p cnf {pool.top} {len(cl)}\n")
        for x in cl:
            f.write(" ".join(map(str, x)) + " 0\n")
    return pool.top, len(cl)


if __name__ == "__main__":
    mode, cls = sys.argv[1], sys.argv[2]
    fams = load(cls)
    if mode == "solve":
        for k in map(int, sys.argv[3:]):
            D = fams[k]
            v = solve(D)
            print(f"class {k}: Delta={len(D)} max |F| - Delta <= {v}, allowed {54 - len(D)}", flush=True)
    elif mode == "cnf":
        k, out = int(sys.argv[3]), sys.argv[4]
        print(cnf(fams[k], out))
