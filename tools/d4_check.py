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
import sys
from collections import Counter
from itertools import combinations, product

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


if __name__ == "__main__":
    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "d4", "witnesses.json")) as fh:
        W = json.load(fh)
    md = check_note_certificates()
    print(f"note certificates 6/10 and 12/20: pass (the 20-member family's largest star is {md}, already >= 20/4)")
    for name in FAMILIES:
        if name not in W:
            print(f"{name}: no witness stored")
            continue
        size, n, maxdeg, need, got = check_family(name, [tuple(p) for p in W[name]])
        print(f"{name}: |F| = {size}, rank {n}, largest star {maxdeg} (< {need} = ceil(|F|/4)), "
              f"verified safe deletion of {got}: D4 holds here")
    sys.exit(0)
