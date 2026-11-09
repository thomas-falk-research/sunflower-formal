#!/usr/bin/env python3
"""Exact SAT computations behind docs/roadmap.md section 94 (hypothesis D4).

Requires python-sat==1.9.dev15 (the version tools/multicolored/ pins);
solver CaDiCaL 1.9.5 as bundled ("cadical195").  Family definitions and the
witness checker are imported from tools/d4_check.py, so a witness found here
is re-checked by the solver-free code before it is reported.

    m(F)      largest safe deletion: members G, one deleted point each,
              images distinct and 3-sunflower-free
    m_int(F)  the same with the images also pairwise intersecting

For a family H on its own ground, double(H) (two disjoint copies) satisfies
    m(double(H)) = max(m(H), 2 m_int(H))
because a sunflower-free image family split over two disjoint grounds with
both parts nonempty must be intersecting on each part (two disjoint images
plus any image from the other part are a sunflower with empty core).

Usage:  d4_sat.py QUERY K      QUERY in the table below; prints SAT (with a
        verified witness size) or UNSAT for "value >= K".
"""
import sys
import time
from itertools import combinations

from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from pysat.solvers import Solver

sys.path.insert(0, __import__("os").path.dirname(__file__))
import d4_check as D  # noqa: E402

BASE = {
    "iota4": lambda: [frozenset(A) for A in D.IOTA4],
    "doubled_iota4": D.FAMILIES["doubled_iota4"],
    "tri_iota3": lambda: D.substitute(D.TRI, D.IOTA3, 6),
    "iota3_tri": lambda: D.substitute(D.IOTA3, D.TRI, 3),
}
QUERIES = {  # name -> (family, intersecting images?)
    "m_iota4": ("iota4", False), "mint_iota4": ("iota4", True),
    "m_doubled_iota4": ("doubled_iota4", False),
    "mint_tri_iota3": ("tri_iota3", True), "m_tri_iota3": ("tri_iota3", False),
    "mint_iota3_tri": ("iota3_tri", True), "m_iota3_tri": ("iota3_tri", False),
}


def sunflower_triples(T):
    """All index triples i<j<k of T forming a sunflower (element -> bitset index)."""
    n = len(T)
    idx = {}
    for i, t in enumerate(T):
        for x in t:
            idx[x] = idx.get(x, 0) | (1 << i)
    full = (1 << n) - 1
    out = []
    for i in range(n):
        for j in range(i + 1, n):
            cand = full
            for x in T[i] & T[j]:
                cand &= idx[x]
            for x in T[i] ^ T[j]:
                cand &= ~idx[x]
            cand >>= j + 1
            k = j + 1
            while cand:
                s = (cand & -cand).bit_length() - 1
                k += s
                out.append((i, j, k))
                cand >>= s + 1
                k += 1
    return out


def encode(F, intersecting):
    pool = IDPool()
    cl = []
    y = {(i, x): pool.id((i, x)) for i, A in enumerate(F) for x in sorted(A)}
    img = {}
    for (i, x), v in y.items():
        img.setdefault(F[i] - {x}, []).append(v)
    T = list(img)
    z = [pool.id(("z", t)) for t in T]
    for i, A in enumerate(F):  # at most one deleted point per member
        cl += CardEnc.atmost([y[(i, x)] for x in A], 1, vpool=pool,
                             encoding=EncType.seqcounter).clauses
    for t, vs in enumerate(img.values()):  # distinct images; z_t <-> OR vs
        if len(vs) > 1:
            cl += CardEnc.atmost(vs, 1, vpool=pool, encoding=EncType.seqcounter).clauses
        cl += [[-v, z[t]] for v in vs] + [[-z[t]] + vs]
    cl += [[-z[a], -z[b], -z[c]] for a, b, c in sunflower_triples(T)]
    if intersecting:
        cl += [[-z[a], -z[b]] for a, b in combinations(range(len(T)), 2) if not T[a] & T[b]]
    return pool, y, cl


def query(name, K):
    fam, inter = QUERIES[name]
    F = [frozenset(A) for A in BASE[fam]()]
    pool, y, cl = encode(F, inter)
    cl += CardEnc.atleast(list(y.values()), K, top_id=pool.top,
                          encoding=EncType.seqcounter).clauses
    t0 = time.time()
    with Solver(name="cadical195", bootstrap_with=cl) as s:
        if not s.solve():
            return f"{name} >= {K}: UNSAT ({time.time() - t0:.0f} s)"
        model = {v for v in s.get_model() if v > 0}
    w = [(i, x) for (i, x), v in y.items() if v in model]
    P = [F[i] - {x} for i, x in w]
    assert len({i for i, _ in w}) == len(w) and all(x in F[i] for i, x in w)
    assert len(set(P)) == len(P) and D.sunflower_free(P)
    if inter:
        assert all(a & b for a, b in combinations(P, 2))
    return f"{name} >= {K}: SAT, verified witness of size {len(P)} ({time.time() - t0:.0f} s)"


if __name__ == "__main__":
    if len(sys.argv) != 3 or sys.argv[1] not in QUERIES:
        sys.exit(__doc__)
    print(query(sys.argv[1], int(sys.argv[2])))
