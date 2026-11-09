#!/usr/bin/env python3
"""Independent checker for the cubic-energy identity and its sunflower reading
(docs/roadmap.md section 93).

Claims checked (H a finite 3-uniform hypergraph, alpha = alpha(H)):

  (T1) min over the simplex of E_H(p) = sum_v p_v^3 + 6 sum_{abc in E} p_a p_b p_c
       equals alpha^-2.  This is [RBP09] Theorem 3 with k = 3, tau = 1/6
       (E_H = 6 h_G for G the complement of H).
  (C2) For a family F of distinct sets OF EQUAL SIZE and independent X, Y, Z ~ mu,
       Pr[X^Y = X^Z = Y^Z] = E_{H_F}(mu), H_F the 3-sunflower hypergraph on F.
  (PL) The pair-link formula of the external note.

Every check that asserts uses exact rational arithmetic (fractions.Fraction),
except section 3, which is a float local search that can only fail to find
a counterexample; its tolerance is stated where it is used.  Section 7 prints
an exploratory measurement and asserts nothing about it.  No third-party
packages.  Exit 0 iff every assertion holds.  Seeds are fixed.
"""
from fractions import Fraction as F
from itertools import combinations, product
from random import Random
import sys


def edge_free(edges, S):
    S = set(S)
    return all(not set(e) <= S for e in edges)


def max_independent_sets(edges, n):
    for r in range(n, -1, -1):
        found = [s for s in combinations(range(n), r) if edge_free(edges, s)]
        if found:
            return r, found


def energy(edges, p, c=6):
    return sum(x ** 3 for x in p) + c * sum(p[a] * p[b] * p[d] for a, b, d in edges)


def curvature(edges, p, a, b):
    """The note's closed form for the t^2 coefficient along p_a+t, p_b-t."""
    return 3 * (p[a] + p[b]) - 6 * sum(p[(set(e) - {a, b}).pop()]
                                       for e in edges if {a, b} <= set(e))


def along(p, a, b, t):
    q = list(p)
    q[a] += t
    q[b] -= t
    return q


def compress(edges, p):
    """Support compression, written independently of the submitted script:
    for an edge in the support take a pair of nonpositive curvature and move
    to the cheaper endpoint.  Returns the trajectory of vectors."""
    traj = [list(p)]
    while True:
        e = next((e for e in edges if all(p[i] > 0 for i in e)), None)
        if e is None:
            return traj
        ks = {pr: curvature(edges, p, *pr) for pr in combinations(e, 2)}
        assert sum(ks.values()) <= 0, ("curvature sum positive", e, ks)
        a, b = next(pr for pr, k in ks.items() if k <= 0)
        p = min((along(p, a, b, -p[a]), along(p, a, b, p[b])),
                key=lambda q: energy(edges, q))
        traj.append(p)


def rand_simplex(rng, n, zero_prob=0.3, hi=12):
    raw = [0 if rng.random() < zero_prob else rng.randint(1, hi) for _ in range(n)]
    if not any(raw):
        raw[rng.randrange(n)] = 1
    s = sum(raw)
    return [F(x, s) for x in raw]


def rand_graph(rng, n):
    q = rng.random()
    return [e for e in combinations(range(n), 3) if rng.random() < q]


# 1. The t^2 coefficient, checked against the polynomial itself -------------
def check_curvature_formula(rng, trials=3000):
    """Energy along the line is a polynomial of degree <= 3 in t; its third
    finite difference must vanish (no t^3 term) and its second difference
    must equal 2K.  Uses only polynomial evaluation, not the derivation."""
    for _ in range(trials):
        n = rng.randint(3, 7)
        E = rand_graph(rng, n)
        p = rand_simplex(rng, n, zero_prob=0.2)
        a, b = rng.sample(range(n), 2)
        v = [energy(E, along(p, a, b, F(t))) for t in range(4)]
        d3 = v[3] - 3 * v[2] + 3 * v[1] - v[0]
        d2 = v[2] - 2 * v[1] + v[0]
        assert d3 == 0, ("cubic term survives", E, p, a, b)
        assert d2 == 2 * curvature(E, p, a, b), ("curvature formula", E, p, a, b)
    return trials


# 2. Every labelled 3-graph on at most 5 vertices ----------------------------
def check_exhaustive(rng, reps=4):
    graphs = trials = 0
    for n in range(1, 6):
        T = list(combinations(range(n), 3))
        for mask in range(1 << len(T)):
            E = [e for j, e in enumerate(T) if mask >> j & 1]
            a, maxsets = max_independent_sets(E, n)
            floor = F(1, a * a)
            graphs += 1
            # attainment: uniform on EVERY maximum independent set gives alpha^-2
            for I in maxsets:
                u = [F(1, a) if v in I else F(0) for v in range(n)]
                assert energy(E, u) == floor
            starts = [rand_simplex(rng, n) for _ in range(reps)] + [[F(1, n)] * n]
            for p in starts:
                traj = compress(E, p)
                hist = [energy(E, q) for q in traj]
                q = traj[-1]
                assert all(x >= y for x, y in zip(hist, hist[1:])), "energy increased"
                # each step kills a support vertex; a support of <= 2 has no edge
                assert len(traj) - 1 <= max(0, n - 2), "too many steps"
                assert sum(q) == 1 and all(x >= 0 for x in q)
                supp = [v for v in range(n) if q[v] > 0]
                assert edge_free(E, supp) and len(supp) <= a
                assert hist[-1] >= floor and hist[0] >= floor
                trials += 1
    return graphs, trials


# 3. Float local search for a counterexample (cannot prove, only refute) -----
def local_min(E, p, n, rng, sweeps, c=6.0):
    """Pairwise exact line search; energy along a pair line is quadratic."""
    def f(q):
        return energy(E, q, c)
    for _ in range(sweeps):
        a, b = rng.sample(range(n), 2)
        lo, hi = -p[a], p[b]
        f0, flo, fhi = f(p), f(along(p, a, b, lo)), f(along(p, a, b, hi))
        cands = [0.0, lo, hi]
        K = 3 * (p[a] + p[b]) - c * sum(p[(set(e) - {a, b}).pop()]
                                         for e in E if {a, b} <= set(e))
        if K > 0 and hi > lo:
            # minimiser of K t^2 + B t + f0 with B fitted from the endpoint values
            B = (fhi - f0 - K * hi * hi) / hi if hi else (flo - f0 - K * lo * lo) / lo
            cands.append(min(max(-B / (2 * K), lo), hi))
        t = min(cands, key=lambda s: f(along(p, a, b, s)))
        p = along(p, a, b, t)
    return f(p)


def check_float_search(rng, graphs=400):
    TOL = 1e-12  # absolute; energies are O(1) and computed in IEEE-754 double
    worst = float("inf")
    for _ in range(graphs):
        n = rng.randint(4, 7)
        E = rand_graph(rng, n)
        a, _ = max_independent_sets(E, n)
        for _ in range(3):
            raw = [rng.random() ** 3 for _ in range(n)]
            p = [x / sum(raw) for x in raw]
            worst = min(worst, local_min(E, p, n, rng, 400) - 1 / a ** 2)
    assert worst >= -TOL, ("float search found energy below alpha^-2", worst)
    return worst


# 4. The probability identity, by brute force over ordered triples ----------
def weak(X, Y, Z):
    return X & Y == X & Z == Y & Z


def sunflower_edges(fam):
    return [t for t in combinations(range(len(fam)), 3) if weak(*(fam[i] for i in t))]


def brute_pr(fam, mu):
    return sum(mu[i] * mu[j] * mu[k]
               for i, j, k in product(range(len(fam)), repeat=3)
               if weak(fam[i], fam[j], fam[k]))


def check_probability_identity(rng, trials=600):
    for _ in range(trials):
        k = rng.randint(1, 3)
        N = rng.randint(k, 7)
        pool = [frozenset(s) for s in combinations(range(N), k)]
        fam = rng.sample(pool, rng.randint(1, min(len(pool), 9)))
        mu = rand_simplex(rng, len(fam), zero_prob=0.2)
        assert brute_pr(fam, mu) == energy(sunflower_edges(fam), mu), (fam, mu)
        # coordinate form: weak sunflower iff no element lies in exactly two
        for X, Y, Z in product(fam, repeat=3):
            two = any((x in X) + (x in Y) + (x in Z) == 2 for x in range(N))
            assert weak(X, Y, Z) == (not two)
    # negative control: without equal sizes the identity is false
    fam = [frozenset({0}), frozenset({0, 1})]
    mu = [F(1, 2), F(1, 2)]
    assert sunflower_edges(fam) == []
    # successes: AAA, BBB and the 3 orderings of AAB (A = A^A = A^B), so 5/8
    assert brute_pr(fam, mu) == F(5, 8) > energy([], mu) == F(1, 4)
    return trials


# 5. Pair-link formula --------------------------------------------------------
def check_pair_link(rng, trials=400):
    for _ in range(trials):
        k = rng.randint(1, 3)
        N = rng.randint(k, 7)
        pool = [frozenset(s) for s in combinations(range(N), k)]
        fam = rng.sample(pool, rng.randint(1, min(len(pool), 8)))
        mu = rand_simplex(rng, len(fam), zero_prob=0.2)
        m = len(fam)
        rhs = sum(x ** 3 for x in mu) + sum(
            mu[i] * mu[j] * sum(mu[c] for c in range(m)
                                if fam[c] & (fam[i] | fam[j]) == fam[i] & fam[j])
            for i in range(m) for j in range(m) if i != j)
        assert brute_pr(fam, mu) == rhs
    return trials


# 6. The uniformity-2 instance ------------------------------------------------
def check_rank_two():
    fam = [frozenset(s) for s in combinations(range(6), 2)]
    E = sunflower_edges(fam)
    stars = sum(1 for t in E if len(fam[t[0]] & fam[t[1]]) == 1)
    assert (len(fam), len(E), stars, len(E) - stars) == (15, 75, 60, 15)
    a, _ = max_independent_sets(E, len(fam))
    assert a == 6
    tri = [frozenset(s) for s in ([0, 1], [1, 2], [0, 2], [3, 4], [4, 5], [3, 5])]
    assert sunflower_edges(tri) == []
    assert brute_pr(tri, [F(1, 6)] * 6) == F(1, 36)
    return a


# 7. The coefficient: sharp control at 15/4, and an exploratory measurement --
def check_coefficient(rng):
    one = [(0, 1, 2)]
    u = [F(1, 3)] * 3
    # single edge, alpha = 2: (3 + c)/27 >= 1/4 iff c >= 15/4
    assert energy(one, u, F(15, 4)) == F(1, 4)
    assert energy(one, u, F(37, 10)) < F(1, 4)
    assert energy(one, u, 1) == F(4, 27) < F(1, 4)  # the note's control
    # Exploratory, asserts nothing.  E_c is increasing in c (edge terms are
    # >= 0), so c = 15/4 is the worst case of [15/4, 6): search there, over
    # every labelled 3-graph on <= 5 vertices and 300 random ones on 6-7.
    c = 3.75
    worst = float("inf")
    graphs = []
    for n in range(3, 6):
        T = list(combinations(range(n), 3))
        graphs += [(n, [e for j, e in enumerate(T) if mask >> j & 1])
                   for mask in range(1, 1 << len(T))]
    for _ in range(300):
        n = rng.randint(6, 7)
        graphs.append((n, rand_graph(rng, n)))
    for n, E in graphs:
        a, _ = max_independent_sets(E, n)
        for _ in range(3):
            raw = [rng.random() ** 3 for _ in range(n)]
            p = [x / sum(raw) for x in raw]
            worst = min(worst, local_min(E, p, n, rng, 150, c) - 1 / a ** 2)
    return c, len(graphs), worst


if __name__ == "__main__":
    rng = Random(20261109)
    print("1. t^2 coefficient vs polynomial (exact):", check_curvature_formula(rng), "trials, pass")
    g, t = check_exhaustive(rng)
    print(f"2. all labelled 3-graphs on <= 5 vertices: {g} graphs, {t} compressions, attainment on every maximum independent set, pass")
    print(f"3. float local search, 400 graphs on 4-7 vertices: min(energy - alpha^-2) = {check_float_search(rng):.3e}, pass")
    print("4. Pr identity by brute force over ordered triples (exact):", check_probability_identity(rng), "families, pass; unequal-size control rejected")
    print("5. pair-link formula (exact):", check_pair_link(rng), "families, pass")
    print("6. 2-sets of [6]: alpha =", check_rank_two(), ", 75 = 60 stars + 15 matchings, two triangles Pr = 1/36, pass")
    c, ng, w = check_coefficient(rng)
    print(f"7. coefficient: one edge fails below 15/4 (exact), pass; EXPLORATORY c = {c}, {ng} graphs: min(energy - alpha^-2) = {w:.3e} (asserts nothing)")
    sys.exit(0)
