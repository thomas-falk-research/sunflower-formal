#!/usr/bin/env python3
"""LPCert: certificates for bounds on integer linear programs, checked in
Coq's kernel by coq/LPCert.v (specification: docs/lpcert.md).

A problem is integer variables x_0 .. x_{n-1}, rows a·x <= b with integer
coefficients (bounds are rows too), an integer objective c and a target T.
A certificate is a tree proving c·x < T for every integer point satisfying
the rows (or, with c = [] and T = 0, that there is none).

  check(problem, tree)          exact checker, the Coq semantics line by line
  solve(problem)                branch-and-bound (scipy/HiGHS); exact duals
  to_coq(problem, tree, name)   a Coq module whose theorem is the bound

The Python checker is a convenience and a second implementation; the
trusted check is Coq's `LPCert.check`, decided by `vm_compute`.

JSON form (docs/lpcert.md):
  problem = {"n": int, "rows": [[[[j, a], ...], b], ...], "c": [[j, c], ...], "T": int}
  tree    = {"leaf": {"K": int, "y": [[["base", r] | ["br", k], y], ...]}}
          | {"branch": [[j, a], ...], "f": int, "le": tree, "ge": tree}
"""
from __future__ import annotations

import json
import sys
from fractions import Fraction


class CertError(Exception):
    pass


def _need(cond, *why):
    if not cond:
        raise CertError(*why)


# ---------------------------------------------------------------- the checker

def sget(v, j):
    """[LPCert.sget]: the coefficient of x_j; repeated indices add up."""
    return sum(a for (i, a) in v if i == j)


def idx_ok(n, v):
    return all(isinstance(i, int) and 0 <= i < n for (i, _) in v)


def _ints(v, what):
    _need(isinstance(v, list), what, "not a list")
    for p in v:
        _need(isinstance(p, list) and len(p) == 2 and type(p[0]) is int and type(p[1]) is int,
              what, "entry is not [int, int]", p)


def rget(rows, P, tag):
    _need(isinstance(tag, list) and len(tag) == 2 and tag[0] in ("base", "br") and type(tag[1]) is int,
          "bad row tag", tag)
    kind, k = tag
    src = rows if kind == "base" else P
    if 0 <= k < len(src):
        return src[k]
    return ([], 0)       # [LPCert.trivial_row]: 0 <= 0, which can only help nothing


def leafcheck(n, c, T, rows, P, K, ys):
    _need(type(K) is int, "K is not an integer", K)
    _need(isinstance(ys, list), "y is not a list")
    rs = []
    for q in ys:
        _need(isinstance(q, list) and len(q) == 2 and type(q[1]) is int, "bad multiplier", q)
        rs.append((rget(rows, P, q[0]), q[1]))
    if K < 0 or any(y < 0 for _, y in rs):
        return False
    if not idx_ok(n, c) or not all(idx_ok(n, r[0]) for r, _ in rs):
        return False
    for j in range(n):
        if K * sget(c, j) != sum(y * sget(r[0], j) for r, y in rs):
            return False
    return sum(y * r[1] for r, y in rs) < K * T


def check_tree(n, c, T, rows, P, node):
    _need(isinstance(node, dict), "node is not an object")
    if "leaf" in node:
        _need(set(node) == {"leaf"} and set(node["leaf"]) == {"K", "y"}, "bad leaf", sorted(node))
        return leafcheck(n, c, T, rows, P, node["leaf"]["K"], node["leaf"]["y"])
    _need(set(node) == {"branch", "f", "le", "ge"}, "bad node", sorted(node))
    a, f = node["branch"], node["f"]
    _ints(a, "branch"); _need(type(f) is int, "f is not an integer")
    neg = [[i, -x] for i, x in a]
    return (check_tree(n, c, T, rows, P + [(a, f)], node["le"])
            and check_tree(n, c, T, rows, P + [(neg, -f - 1)], node["ge"]))


def check(problem, tree):
    """True iff LPCert.check accepts: every integer x with all rows has c·x < T."""
    n, c, T = problem["n"], problem["c"], problem["T"]
    _need(type(n) is int and n >= 0 and type(T) is int, "bad n or T")
    _ints(c, "c")
    rows = []
    for r in problem["rows"]:
        _need(isinstance(r, list) and len(r) == 2 and type(r[1]) is int, "bad row", r)
        _ints(r[0], "row")
        rows.append((r[0], r[1]))
    return check_tree(n, c, T, rows, [], tree)


# ---------------------------------------------------------------- exact linear algebra

def _solve_exact(M, rhs):
    """A solution of M y = rhs over the rationals (M: list of rows), or None.
    Free variables are set to 0."""
    m = len(M)
    k = len(M[0]) if M else 0
    A = [[Fraction(v) for v in row] + [Fraction(b)] for row, b in zip(M, rhs)]
    piv_cols = []
    r = 0
    for col in range(k):
        p = next((i for i in range(r, m) if A[i][col] != 0), None)
        if p is None:
            continue
        A[r], A[p] = A[p], A[r]
        pv = A[r][col]
        A[r] = [v / pv for v in A[r]]
        for i in range(m):
            if i != r and A[i][col] != 0:
                f = A[i][col]
                A[i] = [vi - f * vr for vi, vr in zip(A[i], A[r])]
        piv_cols.append(col)
        r += 1
        if r == m:
            break
    for i in range(r, m):
        if A[i][k] != 0:
            return None
    y = [Fraction(0)] * k
    for i, col in enumerate(piv_cols):
        y[col] = A[i][k]
    return y


def _lcm(a, b):
    from math import gcd
    return a * b // gcd(a, b)


# ---------------------------------------------------------------- the solver

def _leaf(n, c, T, rows, P, infeasible):
    """An exact leaf for the rows in force, or None.  Solves the dual LP with
    HiGHS, then re-solves the equations exactly on the LP's support."""
    import numpy as np
    from scipy.optimize import linprog
    allrows = [("base", i, r) for i, r in enumerate(rows)] + [("br", k, r) for k, r in enumerate(P)]
    m = len(allrows)
    A = np.zeros((n, m))
    for col, (_, _, (a, _)) in enumerate(allrows):
        for i, v in a:
            A[i, col] += v
    b = np.array([float(r[1]) for _, _, r in allrows])
    cv = np.zeros(n)
    if not infeasible:
        for i, v in c:
            cv[i] += v
    # min b·y  s.t.  A y = c (K = 1), y >= 0   or   A y = 0, sum y = 1 (Farkas)
    Aeq, beq = A, cv
    if infeasible:
        Aeq = np.vstack([A, np.ones((1, m))])
        beq = np.concatenate([cv, [1.0]])
    res = linprog(b, A_eq=Aeq, b_eq=beq, bounds=[(0, None)] * m, method="highs")
    if res.status != 0:
        return None
    support = [i for i in range(m) if res.x[i] > 1e-9]
    if not support:
        support = []
    M = [[int(round(A[j, col])) for col in support] for j in range(n)]
    rhs = [sget(c, j) if not infeasible else 0 for j in range(n)]
    if infeasible:
        M.append([1] * len(support)); rhs.append(1)
    y = _solve_exact(M, rhs) if support else None
    if y is None or any(v < 0 for v in y):
        return None
    K = 1
    for v in y:
        K = _lcm(K, v.denominator)
    ys = [[[allrows[col][0], allrows[col][1]], int(v * K)] for col, v in zip(support, y) if v != 0]
    leaf = {"leaf": {"K": 0 if infeasible else K, "y": ys}}
    return leaf if leafcheck(n, [] if infeasible else c, T, rows, P, leaf["leaf"]["K"], ys) else None


def solve(problem, max_nodes=100000):
    """A tree proving c·x < T, by LP-based branch-and-bound on variables."""
    import numpy as np
    from scipy.optimize import linprog
    n, c, T = problem["n"], problem["c"], problem["T"]
    rows = [(r[0], r[1]) for r in problem["rows"]]
    count = [0]

    def rec(P):
        count[0] += 1
        if count[0] > max_nodes:
            raise CertError("node limit")
        allr = rows + P
        A = np.zeros((len(allr), n)); b = np.zeros(len(allr))
        for k, (a, bb) in enumerate(allr):
            for i, v in a:
                A[k, i] += v
            b[k] = bb
        cv = np.zeros(n)
        for i, v in c:
            cv[i] += v
        res = linprog(-cv, A_ub=A, b_ub=b, bounds=[(None, None)] * n, method="highs")
        if res.status == 2:
            leaf = _leaf(n, c, T, rows, P, infeasible=True)
            if leaf is not None:
                return leaf
            raise CertError("infeasible node without an exact Farkas leaf")
        if res.status == 3:
            raise CertError("unbounded relaxation: add bounds as rows")
        if res.status != 0:
            raise CertError("LP failed", res.message)
        val = -res.fun
        if val < T - 1e-9:
            leaf = _leaf(n, c, T, rows, P, infeasible=False)
            if leaf is not None:
                return leaf
        x = res.x
        frac = [i for i in range(n) if abs(x[i] - round(x[i])) > 1e-7]
        if not frac:
            raise CertError(f"integer point with c·x = {val:g} >= T: the claim is false or the LP is degenerate here")
        i = max(frac, key=lambda i: abs(x[i] - round(x[i])))
        f = int(np.floor(x[i]))
        return {"branch": [[i, 1]], "f": f, "le": rec(P + [([[i, 1]], f)]), "ge": rec(P + [([[i, -1]], -f - 1)])}

    return rec([])


# ---------------------------------------------------------------- Coq output

def _svec(v):
    return "[" + "; ".join(f"({i}%nat, {a})" for i, a in v) + "]"


def _tree(node):
    if "leaf" in node:
        K, ys = node["leaf"]["K"], node["leaf"]["y"]
        ent = "; ".join(f"({'Base' if t[0] == 'base' else 'Br'} {t[1]}%nat, {y})" for t, y in ys)
        return f"(Leaf ({K}) [{ent}])"
    return f"(Node {_svec(node['branch'])} ({node['f']}) {_tree(node['le'])} {_tree(node['ge'])})"


def to_coq(problem, tree, name):
    rows = "[" + ";\n   ".join(f"({_svec(a)}, ({b}))" for a, b in problem["rows"]) + "]"
    return "\n".join([
        "(* Generated by tools/lpcert/lpcert.py; do not edit. *)",
        "From Coq Require Import ZArith List.", "Import ListNotations.",
        "From Sunflower Require Import LPCert.", "Local Open Scope Z_scope.", "",
        f"Definition {name}_rows : list row :=\n  {rows}.",
        f"Definition {name}_c : svec := {_svec(problem['c'])}.",
        f"Definition {name}_tree : tree nat := {_tree(tree)}.", "",
        f"Lemma {name}_ok : check nat (list_rows {name}_rows) {problem['n']} {name}_c ({problem['T']}) [] {name}_tree = true.",
        "Proof. vm_compute. reflexivity. Qed.", "",
        f"Theorem {name} : forall x : nat -> Z, (forall r, In r {name}_rows -> sat r x) -> dot {name}_c x < {problem['T']}.",
        f"Proof. exact (tree_sound_list {name}_rows {problem['n']} {name}_c ({problem['T']}) {name}_tree {name}_ok). Qed.", ""])


if __name__ == "__main__":
    mode = sys.argv[1]
    prob = json.load(open(sys.argv[2]))
    if mode == "solve":
        json.dump(solve(prob), open(sys.argv[3], "w"))
    elif mode == "check":
        ok = check(prob, json.load(open(sys.argv[3])))
        print("CHECK PASS" if ok else "CHECK FAIL"); sys.exit(0 if ok else 1)
    elif mode == "coq":
        open(sys.argv[4], "w").write(to_coq(prob, json.load(open(sys.argv[3])), sys.argv[5]))
