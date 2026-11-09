#!/usr/bin/env python3
"""Verify the finite evidence about hypothesis D4 (docs/roadmap.md section 94).

D4 (external note, 2026-11-09): every distinct 3-sunflower-free n-uniform
family F, n >= 2, has a subfamily G with |G| >= |F|/4 and a point p(A) in A
for each A in G such that the sets A - p(A) are distinct and 3-sunflower-free.
Call such a (G, p) a *safe deletion*, and m(F) the largest |G|.

A single star (all members through one point x, deleting x) is always a safe
deletion, so D4 is only tested by families whose maximum degree is below
|F|/4.  This script rebuilds each test family from its definition, checks it
is uniform, distinct and sunflower-free, computes its maximum degree, and
checks the stored safe deletion (tools/d4/witnesses.json) member by member.
It also checks the external note's two adaptive certificates.

Standard library only; integer and set arithmetic; no solver.  The upper
bounds quoted in the roadmap (m_int(iota4) = 9, m(iota4) = 14,
m(doubled_iota4) = 18) are SAT results and are reproduced by
tools/d4_sat.py, not here.  Exit 0 iff every check passes.
"""
import json
import os
import random
import sys
from collections import Counter
from itertools import combinations, permutations, product

# coq/Intersecting.v iota3, coq/Product.v iota4
IOTA3 = [(0, 1, 2), (0, 1, 3), (0, 2, 4), (1, 3, 4), (2, 3, 4),
         (1, 2, 5), (0, 3, 5), (2, 3, 5), (0, 4, 5), (1, 4, 5)]
IOTA4 = [(0, 1, 2, 3), (0, 1, 2, 4), (0, 1, 3, 4), (0, 2, 3, 5), (1, 2, 3, 5),
         (0, 2, 4, 5), (1, 2, 4, 5), (0, 3, 4, 5), (1, 3, 4, 5),
         (0, 1, 6, 7), (2, 3, 6, 7), (2, 4, 6, 7), (3, 4, 6, 7), (0, 5, 6, 7), (1, 5, 6, 7),
         (0, 1, 6, 8), (2, 3, 6, 8), (2, 4, 6, 8), (3, 4, 6, 8), (0, 5, 6, 8), (1, 5, 6, 8),
         (0, 1, 7, 8), (2, 3, 7, 8), (2, 4, 7, 8), (3, 4, 7, 8), (0, 5, 7, 8), (1, 5, 7, 8)]
TRI = [(0, 1), (0, 2), (1, 2)]


def double(H):
    """Intersecting.double: two copies on even and odd points."""
    return [tuple(2 * x for x in A) for A in H] + [tuple(2 * x + 1 for x in A) for A in H]


def substitute(outer, inner, w):
    """[AHS72] substitution (SubstitutionFree.substitute up to relabelling):
    outer point u carries a copy of the inner ground, point (u, y) -> u*w + y."""
    return [frozenset(u * w + y for u, I in zip(O, ch) for y in I)
            for O in outer for ch in product(inner, repeat=len(O))]


def bits(S):
    return sum(1 << x for x in S)


def sunflower_free(sets):
    m = [bits(s) for s in sets]
    for i in range(len(m)):
        for j in range(i + 1, len(m)):
            core, union = m[i] & m[j], m[i] | m[j]
            for k in range(j + 1, len(m)):
                if m[k] & union == core:
                    return False
    return True


FAMILIES = {
    # rank 4: the repository's StarDefect.doubled_iota4
    "doubled_iota4": lambda: [frozenset(A) for A in double(IOTA4)],
    # rank 6: double(triangle[iota3]) = (two disjoint triangles)[iota3]
    "double_tri_iota3": lambda: [frozenset(A) for A in double(
        [tuple(sorted(A)) for A in substitute(TRI, IOTA3, 6)])],
    # rank 6: double(iota3[triangle]) = (the 20-member g(3) family)[triangle]
    "double_iota3_tri": lambda: [frozenset(A) for A in double(
        [tuple(sorted(A)) for A in substitute(IOTA3, TRI, 3)])],
}


def check_family(name, witness):
    F = FAMILIES[name]()
    n = len(F[0])
    assert all(len(A) == n for A in F), "not uniform"
    assert len(set(F)) == len(F), "not distinct"
    assert sunflower_free(F), "input has a sunflower"
    maxdeg = max(Counter(x for A in F for x in A).values())
    need = -(-len(F) // 4)
    assert maxdeg < need, "a star already meets |F|/4: not a D4 test"
    assert len({i for i, _ in witness}) == len(witness), "a member used twice"
    assert all(x in F[i] for i, x in witness), "deleted point not in member"
    P = [F[i] - {x} for i, x in witness]
    assert len(set(P)) == len(P), "images not distinct"
    assert sunflower_free(P), "images contain a sunflower"
    assert len(P) >= need, "witness below |F|/4"
    return len(F), n, maxdeg, need, len(P)


def check_note_certificates():
    seed = [frozenset(A) for A in IOTA3]
    c6 = [(0, 0), (1, 0), (2, 2), (4, 4), (6, 3), (8, 0)]
    P = [seed[i] - {x} for i, x in c6]
    assert all(x in seed[i] for i, x in c6) and len(set(P)) == 6 and sunflower_free(P)
    F20 = [A | {6} for A in seed] + [A | {7} for A in seed]
    assert len(set(F20)) == 20 and sunflower_free(F20)
    c12 = [(11, 3), (5, 5), (17, 3), (19, 4), (9, 4), (0, 6),
           (16, 5), (1, 1), (6, 0), (14, 4), (7, 6), (2, 4)]
    P = [F20[i] - {x} for i, x in c12]
    assert all(x in F20[i] for i, x in c12) and len(set(P)) == 12 and sunflower_free(P)
    maxdeg = max(Counter(x for A in F20 for x in A).values())
    return maxdeg


def automorphisms(fam, n):
    S = {frozenset(A) for A in fam}
    return [p for p in permutations(range(n)) if {frozenset(p[x] for x in A) for A in S} == S]


def substitution_generators(outer, inner, w, n_outer):
    """Outer automorphisms acting on blocks, and inner automorphisms on one block."""
    gens = [{u * w + y: p[u] * w + y for u in range(n_outer) for y in range(w)}
            for p in automorphisms(outer, n_outer)]
    for u in range(n_outer):
        for q in automorphisms(inner, w):
            g = {v * w + y: v * w + y for v in range(n_outer) for y in range(w)}
            g.update({u * w + y: u * w + q[y] for y in range(w)})
            gens.append(g)
    return gens


def safe(H, w, intersecting):
    P = [H[i] - {x} for i, x in w]
    return (len({i for i, _ in w}) == len(w) and all(x in H[i] for i, x in w)
            and len(set(P)) == len(P) and sunflower_free(P)
            and (not intersecting or all(a & b for a, b in combinations(P, 2))))


def check_section_95(W):
    """Section 95: orbit averaging and hereditary products, validated on the
    stored witnesses (the proofs are written; these are instances)."""
    rng = random.Random(20261109)

    def word(gens):
        g = rng.choice(gens)
        for _ in range(39):
            h = rng.choice(gens)
            g = {x: h[g[x]] for x in g}
        return g

    blocks = [(0, 1, 5), (2, 3, 4), (6, 7, 8)]
    tt = {frozenset((blocks[a][e[0]], blocks[a][e[1]], blocks[b][f[0]], blocks[b][f[1]]))
          for a, b in TRI for e in TRI for f in TRI}
    assert tt == {frozenset(A) for A in IOTA4}, "iota4 is not triangle[triangle]"
    relabel = {v: u * 3 + k for u, blk in enumerate(blocks) for k, v in enumerate(blk)}

    def half(name, n):  # copy-1 part of a doubled witness, in H's own labels
        return [(i, x // 2) for i, x in W[name] if i < n]
    cases = [
        ("iota4", [frozenset(relabel[x] for x in A) for A in IOTA4], substitution_generators(TRI, TRI, 3, 3),
         [(i, relabel[x]) for i, x in half("doubled_iota4", 27)]),
        ("triangle[iota3]", substitute(TRI, IOTA3, 6), substitution_generators(TRI, IOTA3, 6, 3),
         half("double_tri_iota3", 300)),
        ("iota3[triangle]", substitute(IOTA3, TRI, 3), substitution_generators(IOTA3, TRI, 3, 6),
         half("double_iota3_tri", 270)),
    ]
    out = []
    for name, H, gens, w in cases:
        idx = {A: i for i, A in enumerate(H)}
        assert all({frozenset(g[x] for x in A) for A in H} == set(H) for g in gens)
        seen, todo = {0}, [0]
        while todo:
            i = todo.pop()
            for g in gens:
                j = idx[frozenset(g[x] for x in H[i])]
                if j not in seen:
                    seen.add(j)
                    todo.append(j)
        assert len(seen) == len(H), f"{name}: not member-transitive"
        assert safe(H, w, True), f"{name}: half-witness not an intersecting safe deletion"
        r, n = len(w), len(H)
        for _ in range(40):
            S = set(rng.sample(range(n), rng.randint(1, n)))
            need = -(-r * len(S) // n)
            for _ in range(300):
                g = word(gens)
                sub = [(j, g[x]) for j, x in ((idx[frozenset(g[z] for z in H[i])], x) for i, x in w) if j in S]
                if len(sub) >= need:
                    break
            assert len(sub) >= need and safe(H, sub, True), f"{name}: averaging instance failed"
        out.append(f"{name} {r}/{n}")
    # hereditary product: iota3 (q = 3/10) times two disjoint triangles
    F3 = [frozenset(A) for A in IOTA3]
    gF = [{x: p[x] for x in range(6)} for p in automorphisms(IOTA3, 6)]
    wF = [(0, 0), (1, 3), (2, 4)]
    assert safe(F3, wF, True)
    idxF = {A: i for i, A in enumerate(F3)}
    Hh = [frozenset({10 + a, 10 + b}) for a, b in [(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)]]
    P3 = [A | B for A in F3 for B in Hh]
    assert sunflower_free(P3)
    for _ in range(60):
        S = rng.sample(P3, rng.randint(1, len(P3)))
        imgs = []
        for B in Hh:
            fib = {idxF[A - B] for A in S if B <= A}
            need = -(-3 * len(fib) // 10)
            for _ in range(500):
                g = word(gF)
                sub = [(j, g[x]) for j, x in ((idxF[frozenset(g[z] for z in F3[i])], x) for i, x in wF) if j in fib]
                if len(sub) >= need:
                    break
            assert len(sub) >= need
            imgs += [(F3[i] | B) - {x} for i, x in sub]
        assert len(set(imgs)) == len(imgs) and sunflower_free(imgs) and 10 * len(imgs) >= 3 * len(S)
    return out


def check_dichotomy_counterexample():
    """The note's F_1 = iota3 (x) binary-tree paths of depth 3: rank 6,
    80 members, support 20, minimum degree 10, sunflower-free."""
    paths = []
    for leaf in range(8):
        paths.append(frozenset(100 + (1 << d) - 2 + (leaf >> (3 - d)) for d in range(1, 4)))
    assert len(set().union(*paths)) == 14 and sunflower_free(paths)
    F1 = [frozenset(A) | B for A in IOTA3 for B in paths]
    deg = Counter(x for A in F1 for x in A)
    assert (len(set(F1)), len(F1[0]), len(deg), min(deg.values())) == (80, 6, 20, 10)
    assert sunflower_free(F1)


if __name__ == "__main__":
    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "d4", "witnesses.json")) as fh:
        W = json.load(fh)
    md = check_note_certificates()
    check_dichotomy_counterexample()
    print("note's F_1 (rank 6, 80 members, support 20, min degree 10): sunflower-free, pass")
    print(f"note certificates 6/10 and 12/20: pass (the 20-member family's largest star is {md}, already >= 20/4)")
    for name in FAMILIES:
        if name not in W:
            print(f"{name}: no witness stored")
            continue
        size, n, maxdeg, need, got = check_family(name, [tuple(p) for p in W[name]])
        print(f"{name}: |F| = {size}, rank {n}, largest star {maxdeg} (< {need} = ceil(|F|/4)), "
              f"verified safe deletion of {got}: D4 holds here")
    q = check_section_95(W)
    print("section 95: iota4 = triangle[triangle]; member-transitive; orbit averaging met ceil(q|S|) on 40 random"
          " subfamilies each (" + ", ".join(q) + "); hereditary product iota3 x two-triangles on 60: pass")
    sys.exit(0)
