#!/usr/bin/env python3
"""Exact branch-and-bound certificates for the link23.py model (docs/roadmap.md §65).

The model (tools/iota4/link23.py) is an integer program over type counts
x >= 0, with rows A x <= b and bounds x <= ub, whose optimum bounds
|F| - Delta - 1. The claim to certify for a class D is

        sum x <= 54 - Delta - 1        (so |F| <= 54).

A certificate is a binary tree. Every node carries integer bounds lo <= x <= hi;
the root has lo = 0, hi = ub; an internal node splits one variable i at an
integer f into children with hi_i = f and lo_i = f + 1 (so the children cover
every integer point of the parent). Every leaf carries rationals y >= 0 (rows),
u >= 0, v >= 0 (upper and lower bounds) with, componentwise,

        w = A^T y + u - v >= c,        b.y + hi.u - lo.v < T,

where c = 1 and T = (54 - Delta - 1) + 1 for a bounding leaf, or c = 0 and T = 0
for an infeasibility leaf. For every integer x in the leaf, x >= 0 gives
c.x <= w.x <= b.y + hi.u - lo.v < T, i.e. sum x <= 54 - Delta - 1 (resp. no x).

  bnbcert.py solve CLASSES.gz INDEX OUT.json.gz     build tree + certificates (scipy/HiGHS)
  bnbcert.py check CLASSES.gz INDEX CERT.json.gz    verify exactly (fractions; rebuilds the model)
"""
import sys, os, json, gzip
from fractions import Fraction as Fr
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import link23
from linkcert import load


def matrix(D):
    """Rows (sparse: list of (col, coef)), rhs, ub — the same linearisation as link23.solve."""
    types, ub, cons = link23.model(D)
    big = sum(ub) + 1
    rows, rhs = [], []
    for c in cons:
        if c[0] == "le":
            rows.append([(i, 1) for i in c[1]]); rhs.append(c[2])
        elif c[0] == "if_le":
            rows.append([(i, 1) for i in c[2]] + [(c[1], big)]); rhs.append(c[3] + big)
        else:
            a, bb = c[1], c[2]
            rows.append([(bb, 1), (a, ub[bb])]); rhs.append(ub[bb])
    # merge duplicate columns within a row (a type can appear once per row; keep it general)
    merged = []
    for r in rows:
        d = {}
        for i, v in r:
            d[i] = d.get(i, 0) + v
        merged.append(sorted(d.items()))
    return len(types), merged, rhs, ub


def solve(D, out):
    import numpy as np
    from scipy.optimize import linprog
    from scipy.sparse import csr_matrix
    n, rows, rhs, ub = matrix(D)
    goal = int(os.environ.get("BNB_GOAL", 54 - len(D) - 1))   # need sum x <= goal (override: controls only)
    m = len(rows)
    data, ri, ci = [], [], []
    for r, row in enumerate(rows):
        for i, v in row:
            ri.append(r); ci.append(i); data.append(v)
    A = csr_matrix((data, (ri, ci)), shape=(m, n))
    AT = A.T.tocsr()
    b = np.array(rhs, float)

    def leaf_cert(lo, hi, c):
        # dual LP: min b.y + hi.u - lo.v  s.t.  A^T y + u - v >= c, 0 <= y,u,v <= CAP
        from scipy.sparse import hstack, identity
        I = identity(n, format="csr")
        M = hstack([AT, I, -I]).tocsr()
        cost = np.concatenate([b, np.array(hi, float), -np.array(lo, float)])
        r = linprog(cost, A_ub=-M, b_ub=-np.full(n, float(c)),
                    bounds=[(0, 1e4)] * (m + 2 * n), method="highs")
        assert r.status == 0, r.message
        x = r.x
        y = {j: Fr(x[j]).limit_denominator(10**6) for j in range(m) if x[j] > 1e-9}
        u = {i: Fr(x[m + i]).limit_denominator(10**6) for i in range(n) if x[m + i] > 1e-9}
        v = {i: Fr(x[m + n + i]).limit_denominator(10**6) for i in range(n) if x[m + n + i] > 1e-9}
        # exact repair: raise u where w falls short of c after rounding
        w = [Fr(0)] * n
        for j, yj in y.items():
            for i, a in rows[j]:
                w[i] += yj * a
        for i in range(n):
            w[i] += u.get(i, 0) - v.get(i, 0)
            if w[i] < c:
                u[i] = u.get(i, 0) + (c - w[i])
        return {"y": {str(k): str(q) for k, q in y.items()},
                "u": {str(k): str(q) for k, q in u.items()},
                "v": {str(k): str(q) for k, q in v.items()}}

    stats = {"nodes": 0, "leaves": 0}

    def rec(lo, hi):
        stats["nodes"] += 1
        r = linprog(-np.ones(n), A_ub=A, b_ub=b, bounds=list(zip(lo, hi)), method="highs")
        if r.status == 2:
            stats["leaves"] += 1
            return {"leaf": "infeasible", "cert": leaf_cert(lo, hi, 0)}
        assert r.status == 0, r.message
        val = -r.fun
        if val < goal + 1 - 1e-6:
            stats["leaves"] += 1
            return {"leaf": "bound", "cert": leaf_cert(lo, hi, 1)}
        x = r.x
        frac = [(abs(x[i] - round(x[i])), i) for i in range(n) if abs(x[i] - round(x[i])) > 1e-6]
        if not frac:
            raise SystemExit(f"integer point with sum {val}: the class is NOT certified")
        _, i = max(frac)
        f = int(np.floor(x[i]))
        h2 = list(hi); h2[i] = f
        l2 = list(lo); l2[i] = f + 1
        return {"var": i, "f": f, "le": rec(lo, h2), "ge": rec(l2, hi)}

    tree = rec([0] * n, list(ub))
    with gzip.open(out, "wt") as fh:
        json.dump({"n": n, "goal": goal, "tree": tree}, fh)
    return stats


class CertError(Exception):
    pass


def need(cond, *why):
    # explicit check: survives `python3 -O`, unlike assert
    if not cond:
        raise CertError(*why)


def index(key, bound, what):
    """A multiplier key must be a decimal index in range(bound)."""
    need(isinstance(key, str) and key.isdigit(), what, "bad key", key)
    k = int(key)
    need(0 <= k < bound, what, "key out of range", key)
    return k


def rational(q, what):
    need(isinstance(q, str), what, "multiplier not a string", q)
    x = Fr(q)
    need(x >= 0, what, "negative multiplier", q)
    return x


def check(D, path):
    n, rows, rhs, ub = matrix(D)
    m = len(rows)
    goal = int(os.environ.get("BNB_GOAL", 54 - len(D) - 1))
    C = json.load(gzip.open(path, "rt"))
    need(C.get("n") == n and C.get("goal") == goal, "header mismatch", C.get("n"), C.get("goal"), n, goal)
    cnt = {"leaves": 0, "nodes": 0}

    def leaf(node, lo, hi):
        need(node["leaf"] in ("bound", "infeasible"), "unknown leaf kind", node["leaf"])
        c = 1 if node["leaf"] == "bound" else 0
        T = Fr(goal + 1) if c == 1 else Fr(0)
        cert = node["cert"]
        need(set(cert) == {"y", "u", "v"}, "certificate keys", sorted(cert))
        y = {index(k, m, "y"): rational(q, "y") for k, q in cert["y"].items()}
        u = {index(k, n, "u"): rational(q, "u") for k, q in cert["u"].items()}
        v = {index(k, n, "v"): rational(q, "v") for k, q in cert["v"].items()}
        w = [Fr(0)] * n
        for j, yj in y.items():
            for i, a in rows[j]:
                w[i] += yj * a
        for i in range(n):
            w[i] += u.get(i, 0) - v.get(i, 0)
            need(w[i] >= c, "dual infeasible at column", i, w[i])
        bound = sum(yj * rhs[j] for j, yj in y.items()) + \
            sum(q * hi[i] for i, q in u.items()) - sum(q * lo[i] for i, q in v.items())
        need(bound < T, "bound not below target", bound, T)

    def walk(node, lo, hi):
        cnt["nodes"] += 1
        if "leaf" in node:
            cnt["leaves"] += 1
            leaf(node, lo, hi)
            return
        i, f = node["var"], node["f"]
        need(type(i) is int and 0 <= i < n, "bad branching variable", i)
        need(type(f) is int, "non-integer split", f)
        need(lo[i] <= f < hi[i], "split outside range", i, f, lo[i], hi[i])   # both children nonempty
        h2 = list(hi); h2[i] = f
        l2 = list(lo); l2[i] = f + 1
        walk(node["le"], lo, h2)
        walk(node["ge"], l2, hi)

    walk(C["tree"], [0] * n, list(ub))
    return cnt


if __name__ == "__main__":
    mode, cls, k = sys.argv[1], sys.argv[2], int(sys.argv[3])
    D = load(cls)[k]
    if mode == "solve":
        print(k, solve(D, sys.argv[4]))
    else:
        c = check(D, sys.argv[4])
        print(f"class {k}: CHECK PASS, {c['nodes']} nodes, {c['leaves']} leaves: |F| <= 54 under the link23 model")
