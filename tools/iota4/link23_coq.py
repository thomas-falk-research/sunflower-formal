#!/usr/bin/env python3
"""Branch-and-bound certificates for coq/Link23.v (docs/roadmap.md §69).

Rebuilds, in Python, exactly the type list and the tagged rows that
[Link23.types] and [Link23.rowc] define in Coq (positional profiles, the
Coq enumeration orders), solves the §65 integer program by LP-based
branch-and-bound (scipy/HiGHS), scales every leaf's rational dual to
integers, re-checks each leaf in exact integer arithmetic with the
Coq semantics, and emits a Coq module whose single lemma is decided by
[vm_compute]:

  link23_coq.py solve CLASSES.gz INDEX OUT.json.gz        build the tree
  link23_coq.py check CLASSES.gz INDEX TREE.json.gz       re-check it (exact)
  link23_coq.py coq   CLASSES.gz INDEX TREE.json.gz OUT.v NAME   emit Coq
  link23_coq.py batch CLASSES.gz SIZE i/n OUT.json.gz          trees for shard i/n of one link size
  link23_coq.py coqshard CLASSES.gz TREES.json.gz OUT.v NAME   emit one module for a shard
  link23_coq.py coqshard_h CLASSES.gz TREES.json.gz OUT.v NAME emit one hinted module ([classcheck_h])

The checker here is only a convenience: the kernel check is
[Link23.classcheck] in Coq.
"""
import sys, os, json, gzip, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from linkcert import load, load_some, load_ks, validate


# ---------------------------------------------------------------- Coq mirror

def coq_points(D):
    """[nodup Nat.eq_dec (concat D)]: keeps the LAST occurrence of each point."""
    xs = [x for C in D for x in C]
    out = []
    for i, x in enumerate(xs):
        if x not in xs[i + 1:]:
            out.append(x)
    return out


def subs_le(k, l):
    if not l:
        return [[]]
    x, rest = l[0], l[1:]
    first = [[x] + s for s in subs_le(k - 1, rest)] if k > 0 else []
    return first + subs_le(k, rest)


def traces(V):
    return [T for T in subs_le(3, V) if len(T) >= 1]


def witnessed(T, D):
    sT = set(T)
    for C1 in D:
        for C2 in D:
            if set(C1) == set(C2):
                continue
            K = set(C1) & set(C2)
            if (sT & set(C1)) == K and (sT & set(C2)) == K:
                return True
    return False


def unwit(D):
    return [T for T in traces(coq_points(D)) if not witnessed(T, D)]


def pairw(D):
    """[Link23.pairw]: for each unordered pair (in Coq order), its core K and
    the rest W of its union (C1 ++ C2 order, K removed)."""
    out = []
    for a, C1 in enumerate(D):
        for C2 in D[a + 1:]:
            if set(C1) == set(C2):
                continue
            K = [x for x in C1 if x in C2]
            W = [x for x in C1 + C2 if x not in K]
            out.append((K, W))
    return out


def hints_fast(D):
    """[hints] with bitmasks; same result (first witnessing pair, in order)."""
    P = [(sum(1 << x for x in K), sum(1 << x for x in W)) for K, W in pairw(D)]
    hs = []
    for T in traces(coq_points(D)):
        t = sum(1 << x for x in T)
        j = next((i for i, (k, w) in enumerate(P) if k & t == k and not (t & w)), None)
        hs.append(0 if j is None else j + 1)
    return hs


def hints(D):
    """[Link23.unwith] hints: per trace of points D, 0 if unwitnessed, else
    1 + the index of the first witnessing pair."""
    P = pairw(D)
    hs = []
    for T in traces(coq_points(D)):
        j = next((i for i, (K, W) in enumerate(P) if all(x in T for x in K) and not any(x in W for x in T)), None)
        hs.append(0 if j is None else j + 1)
    # the hinted list must be exactly unwit(D), so the stored trees stay valid
    kept = [T for T, h in zip(traces(coq_points(D)), hs) if h == 0]
    assert kept == unwit(D), "hints disagree with unwit"
    return hs


POS = [0, 1, 2, 3]
PROF = [P for P in subs_le(4, POS) if len(P) >= 1]


def types(U):
    return [(T, P) for T in U for P in PROF if len(T) + len(P) <= 4] + \
           [([], P) for P in PROF if len(P) <= 3]


def ub_of(t):
    T, P = t
    if not T:
        return {3: 1, 2: 3}.get(len(P), 26)
    return {0: 1, 1: 2}.get(4 - (len(T) + len(P)), 6)


def cap(T):
    return {1: 26, 2: 6}.get(len(T), 2)


def interb(A, B):
    return [x for x in A if x in B]


def disjf(A, B):
    return not any(x in B for x in A)


def seteq(A, B):
    return set(A) == set(B)


def dett(t):
    return len(t[0]) + len(t[1]) == 4


def detdis(a, t):
    return disjf(t[0], a[0]) and disjf(t[1], a[1])


def exclb(D, a, b):
    TT = interb(a[0], b[0])
    PP = interb(a[1], b[1])
    if seteq(a[1], b[1]) and TT == []:
        return True
    if PP == [] and any(seteq(interb(a[0], C), TT) and seteq(interb(b[0], C), TT) for C in D):
        return True
    if TT == [] and PP == [] and any(disjf(a[0], C) and disjf(b[0], C) for C in D):
        return True
    return False


def _m(l):
    return sum(1 << x for x in l)


def rows_of(D, U, ts, big):
    return rows_of_fast(D, U, ts, big)


def rows_of_fast(D, U, ts, big):
    """[rows_of_ref] with bitmasks; the same rows in the same order."""
    n = len(ts)
    Delta = len(D)
    Cm = [_m(C) for C in D]
    Tm = [_m(t[0]) for t in ts]
    Pm = [_m(t[1]) for t in ts]
    out = []
    for T in U:
        out.append((("RCap", T), {i: 1 for i, t in enumerate(ts) if t[0] == T}, cap(T)))
    for T in U:
        tm = _m(T)
        if any(tm & c == tm for c in Cm):
            out.append((("RCapI", T), {i: 1 for i, t in enumerate(ts) if t[0] == T}, {1: 13, 2: 3}.get(len(T), 1)))
    for C, c in zip(D, Cm):
        out.append((("RLink", C), {i: 1 for i in range(n) if not Tm[i] & c}, Delta - 1))
    for k in POS:
        out.append((("RStar", k), {i: 1 for i, t in enumerate(ts) if k in t[1]}, 25))
    if Delta >= 1:
        out.append((("RIota",), {i: 1 for i, t in enumerate(ts) if t[0] == []}, 27))
    for i, a in enumerate(ts):
        if not dett(a):
            continue
        ta, pa = Tm[i], Pm[i]
        avoid = sum(1 for c in Cm if not ta & c)
        coef = {}
        for j in range(n):
            cj = (big if j == i else 0) + (1 if (not Tm[j] & ta and not Pm[j] & pa) else 0)
            if cj:
                coef[j] = cj
        out.append((("RDet", i), coef, Delta - avoid + big))
        for j in range(n):
            if j == i:
                continue
            tb, pb = Tm[j], Pm[j]
            TT, PP = ta & tb, pa & pb
            ex = (pa == pb and TT == 0) \
                or (PP == 0 and any((ta & c) == TT and (tb & c) == TT for c in Cm)) \
                or (TT == 0 and PP == 0 and any(not ta & c and not tb & c for c in Cm))
            if ex:
                out.append((("RExcl", i, j), {i: ub_of(ts[j]), j: 1}, ub_of(ts[j])))
    return out


def rows_of_ref(D, U, ts, big):
    """All tags with a nontrivial row, as (tag, {col: coef}, rhs)."""
    n = len(ts)
    Delta = len(D)
    out = []
    for T in U:
        out.append((("RCap", T), {i: 1 for i, t in enumerate(ts) if t[0] == T}, cap(T)))
    for T in U:      # trace inside a link member: outer parts pairwise intersect
        if any(all(x in C for x in T) for C in D):
            out.append((("RCapI", T), {i: 1 for i, t in enumerate(ts) if t[0] == T}, {1: 13, 2: 3}.get(len(T), 1)))
    for C in D:
        out.append((("RLink", C), {i: 1 for i, t in enumerate(ts) if disjf(t[0], C)}, Delta - 1))
    for k in POS:
        out.append((("RStar", k), {i: 1 for i, t in enumerate(ts) if k in t[1]}, 25))
    if Delta >= 1:   # [ι(4) ≤ 27]: members missing the link's points
        out.append((("RIota",), {i: 1 for i, t in enumerate(ts) if t[0] == []}, 27))
    for i, a in enumerate(ts):
        if not dett(a):
            continue
        avoid = sum(1 for C in D if disjf(a[0], C))
        coef = {}
        for j, t in enumerate(ts):
            c = (big if j == i else 0) + (1 if detdis(a, t) else 0)
            if c:
                coef[j] = c
        out.append((("RDet", i), coef, Delta - avoid + big))
        for j, b in enumerate(ts):
            if j == i or not exclb(D, a, b):
                continue
            out.append((("RExcl", i, j), {i: ub_of(b), j: 1}, ub_of(b)))
    return out


def model(D):
    validate([frozenset(C) for C in D])
    U = unwit(D)
    ts = types(U)
    ub = [ub_of(t) for t in ts]
    big = sum(ub) + 1
    return U, ts, ub, big, rows_of(D, U, ts, big)


def canon(F):
    """The class as Coq sees it: each member sorted, members in file order."""
    return [sorted(S) for S in F]


# ---------------------------------------------------------------- solving

def solve(D, out):
    import numpy as np
    from scipy.optimize import linprog
    from scipy.sparse import csr_matrix, hstack, identity
    U, ts, ub, big, rows = model(D)
    n, m = len(ts), len(rows)
    goal = 54 - len(D) - 1                      # need sum x <= goal;  T = goal + 1
    T = goal + 1
    data, ri, ci = [], [], []
    for r, (_, coef, _) in enumerate(rows):
        for i, v in coef.items():
            ri.append(r); ci.append(i); data.append(v)
    A = csr_matrix((data, (ri, ci)), shape=(m, n))
    AT = A.T.tocsr()
    b = np.array([rhs for _, _, rhs in rows], float)
    I = identity(n, format="csr")
    Mdual = hstack([AT, I, -I]).tocsr()

    def leaf_cert(lo, hi, c):
        cost = np.concatenate([b, np.array(hi, float), -np.array(lo, float)])
        r = linprog(cost, A_ub=-Mdual, b_ub=-np.full(n, float(c)),
                    bounds=[(0, 100)] * (m + 2 * n), method="highs")
        assert r.status == 0, r.message
        x = r.x
        # one common denominator D for the whole leaf (K = D·c): round, then
        # repair u upward where a column falls short, and check the bound
        for Dn in (10**3, 10**4, 10**6, 10**8, 10**10):
            ys = {j: int(round(x[j] * Dn)) for j in range(m) if x[j] > 1e-12}
            us = [int(round(x[m + i] * Dn)) for i in range(n)]
            vs = [int(round(x[m + n + i] * Dn)) for i in range(n)]
            w = [0] * n
            for j, yj in ys.items():
                for i, a in rows[j][1].items():
                    w[i] += yj * a
            for i in range(n):
                need = Dn * c + vs[i] - w[i]
                if us[i] < need:
                    us[i] = need
            bound = sum(yj * rows[j][2] for j, yj in ys.items()) + sum(us[i] * hi[i] for i in range(n))
            if bound < sum(vs[i] * lo[i] for i in range(n)) + Dn * c * T:
                break
        else:
            return None            # too close to the threshold: branch instead
        ys = {j: q for j, q in ys.items() if q}
        if c == 0:                # homogeneous: divide by the gcd
            g = 0
            for q in list(ys.values()) + us + vs:
                g = math.gcd(g, q)
            if g > 1:
                ys = {j: q // g for j, q in ys.items()}
                us = [q // g for q in us]
                vs = [q // g for q in vs]
        leaf = {"K": Dn * c, "y": [[rows[j][0], q] for j, q in sorted(ys.items())], "u": us, "v": vs}
        return leaf

    stats = {"nodes": 0, "leaves": 0}

    def rec(lo, hi):
        stats["nodes"] += 1
        r = linprog(-np.ones(n), A_ub=A, b_ub=b, bounds=list(zip(lo, hi)), method="highs")
        if r.status == 2:
            c = leaf_cert(lo, hi, 0)
            if c is not None:
                stats["leaves"] += 1
                return {"leaf": c}
            x = None
        else:
            assert r.status == 0, r.message
            val = -r.fun
            if val < goal + 1 - 1e-6:
                c = leaf_cert(lo, hi, 1)
                if c is not None:
                    stats["leaves"] += 1
                    return {"leaf": c}
            x = r.x
        if x is None:                 # infeasible but the Farkas certificate would not round: split anyway
            frac = [i for i in range(n) if lo[i] < hi[i]]
            if not frac:
                raise SystemExit("infeasible box with no room to split")
            i = frac[0]
            f = (lo[i] + hi[i]) // 2
            h2 = list(hi); h2[i] = f
            l2 = list(lo); l2[i] = f + 1
            return {"var": i, "f": f, "le": rec(lo, h2), "ge": rec(l2, hi)}
        frac = [i for i in range(n) if abs(x[i] - round(x[i])) > 1e-6]
        if not frac:
            if val < goal + 1 - 1e-6:   # integral LP optimum below the threshold, but the dual would not round
                frac = [i for i in range(n) if lo[i] < hi[i]]
                if not frac:
                    raise SystemExit("integral box that will not certify")
                i = frac[0]; f = int(round(x[i])) if lo[i] <= round(x[i]) < hi[i] else lo[i]
                h2 = list(hi); h2[i] = f
                l2 = list(lo); l2[i] = f + 1
                return {"var": i, "f": f, "le": rec(lo, h2), "ge": rec(l2, hi)}
            raise SystemExit(f"integer point with sum {val}: the class is NOT certified")
        # branch on a fractional determined type (cap 1) first: those switch the
        # big-M rows on and off, and the LP is weak until they are fixed
        dets = [i for i in frac if ub[i] == 1]
        i = max(dets if dets else frac, key=lambda i: abs(x[i] - round(x[i])))
        f = int(np.floor(x[i]))
        h2 = list(hi); h2[i] = min(f, hi[i])
        l2 = list(lo); l2[i] = max(f + 1, lo[i])
        return {"var": i, "f": f, "le": rec(lo, h2), "ge": rec(l2, hi)}

    tree = rec([0] * n, list(ub))
    doc = {"n": n, "Delta": len(D), "tree": tree}
    if out is not None:
        with gzip.open(out, "wt") as fh:
            json.dump(doc, fh)
    return stats, doc


# ---------------------------------------------------------------- exact check (Coq semantics)

def tagkey(tag):
    return json.dumps(tag)


def check(D, path):
    return check_doc(D, json.load(gzip.open(path, "rt")))


def check_doc(D, C):
    U, ts, ub, big, rows = model(D)
    n = len(ts)
    T = 54 - len(D)
    byt = {tagkey(tag): (coef, rhs) for tag, coef, rhs in rows}
    assert C["n"] == n and C["Delta"] == len(D)
    cnt = {"nodes": 0, "leaves": 0}

    def leaf(c, lo, hi):
        K = c["K"]; assert type(K) is int and K >= 0
        ys = [(tagkey(tag), y) for tag, y in c["y"]]
        u, v = c["u"], c["v"]
        assert len(u) == n and len(v) == n and all(type(q) is int and q >= 0 for q in u + v)
        for _, y in ys:
            assert type(y) is int and y >= 0
        # column conditions: K + v_j <= sum_r y_r a_rj + u_j   (trivial row for unknown tags)
        for j in range(n):
            s = sum(y * byt[k][0].get(j, 0) for k, y in ys if k in byt)
            assert K + v[j] <= s + u[j], ("column", j)
        lhs = sum(y * byt[k][1] for k, y in ys if k in byt) + sum(u[j] * hi[j] for j in range(n))
        rhs = sum(v[j] * lo[j] for j in range(n)) + K * T
        assert lhs < rhs, ("bound", lhs, rhs)

    def walk(node, lo, hi):
        cnt["nodes"] += 1
        if "leaf" in node:
            cnt["leaves"] += 1
            leaf(node["leaf"], lo, hi)
            return
        i, f = node["var"], node["f"]
        assert type(i) is int and type(f) is int and 0 <= i < n
        h2 = list(hi); h2[i] = min(f, hi[i])
        l2 = list(lo); l2[i] = max(f + 1, lo[i])
        walk(node["le"], lo, h2)
        walk(node["ge"], l2, hi)

    walk(C["tree"], [0] * n, list(ub))
    return cnt


# ---------------------------------------------------------------- LPCert form (coq/LPCert.v)
#
# [Link23.lpclass]: variables are the type counts (all nonnegative), rows
# are ["row", tag] (the tagged rows) and ["ub", j] (x_j <= ub_of t_j);
# a node ["branch"] on x_i at f; a leaf K, y on ["base", rowtag] and
# ["br", k] (the k-th branching row on the path: x_i <= f on the left,
# -x_i <= -f-1 on the right).

def lp_of_doc(doc, ub):
    """Convert a tree in the §69 form (bounds lo/hi, leaf u/v) to LPCert form.
    u_i goes onto the row that gives hi_i (["ub", i] or a branching row),
    v_i onto the branching row that gives lo_i; v_i with lo_i = 0 is
    dropped (the slack of x_i >= 0).  The leaf inequalities are then
    exactly the old ones, coefficient by coefficient."""
    n = doc["n"]

    def walk(node, depth, hi, his, lo, los):
        if "leaf" in node:
            c = node["leaf"]
            ys = [[["base", ["row", tag]], y] for tag, y in c["y"] if y]
            for i, u in enumerate(c["u"]):
                if u:
                    ys.append([["base", ["ub", i]] if his[i] is None else ["br", his[i]], u])
            for i, v in enumerate(c["v"]):
                if v and los[i] is not None:
                    ys.append([["br", los[i]], v])
            return {"leaf": {"K": c["K"], "y": ys}}
        i, f = node["var"], node["f"]
        h2, hs2, l2, ls2 = list(hi), list(his), list(lo), list(los)
        assert type(i) is int and 0 <= i < n and type(f) is int and f >= 0
        if f < hi[i]:
            h2[i], hs2[i] = f, depth
        if f + 1 > lo[i]:
            l2[i], ls2[i] = f + 1, depth
        return {"branch": i, "f": f,
                "le": walk(node["le"], depth + 1, h2, hs2, lo, los),
                "ge": walk(node["ge"], depth + 1, hi, his, l2, ls2)}

    assert len(ub) == n
    return walk(doc["tree"], 0, list(ub), [None] * n, [0] * n, [None] * n)


def lp_check(D, lt, mdl=None):
    """[Link23.lpclass D lt] with the LPCert semantics, exactly: every
    leaf has K >= 0, y >= 0, indices < n, K·c_j <= (Σ y·a)_j for every
    j (all variables are nonnegative, c = all ones), Σ y·b < K·T.
    Unknown tags are the trivial row 0 <= 0, as in Coq."""
    U, ts, ub, big, rows = model(D) if mdl is None else mdl
    n = len(ts)
    T = 54 - len(D) if len(D) <= 54 else 0
    byt = {tagkey(tag): (coef, rhs) for tag, coef, rhs in rows}
    cnt = {"nodes": 0, "leaves": 0}

    def rowof(rt, P):
        kind, t = rt
        if kind == "br":
            assert type(t) is int and t >= 0
            return P[t] if t < len(P) else ({}, 0)
        assert kind == "base"
        if t[0] == "ub":
            j = t[1]
            assert type(j) is int and j >= 0
            return ({j: 1}, ub[j]) if j < n else ({}, 0)
        assert t[0] == "row"
        return byt.get(tagkey(t[1]), ({}, 0))

    def leaf(c, P):
        K = c["K"]
        assert type(K) is int and K >= 0, "K"
        acc = {}
        rhs = 0
        for rt, y in c["y"]:
            assert type(y) is int and y >= 0, "y"
            coef, b = rowof(rt, P)
            for j, a in coef.items():
                assert 0 <= j < n, "index"
                acc[j] = acc.get(j, 0) + y * a
            rhs += y * b
        for j in range(n):
            assert K <= acc.get(j, 0), ("column", j)
        assert rhs < K * T, ("bound", rhs, K * T)

    def walk(node, P):
        cnt["nodes"] += 1
        if "leaf" in node:
            cnt["leaves"] += 1
            leaf(node["leaf"], P)
            return
        i, f = node["branch"], node["f"]
        assert type(i) is int and type(f) is int and 0 <= i and f >= 0
        walk(node["le"], P + [({i: 1}, f)])
        walk(node["ge"], P + [({i: -1}, -f - 1)])

    walk(lt, [])
    return cnt


def lp_problem(D, mdl=None):
    """The class as a generic tools/lpcert problem, with a map from the
    tags here to its row indices (for cross-checking with lpcert.py)."""
    U, ts, ub, big, rows = model(D) if mdl is None else mdl
    n = len(ts)
    prows, idx = [], {}
    for tag, coef, rhs in rows:
        idx[json.dumps(["row", tag])] = len(prows)
        prows.append([[[j, a] for j, a in sorted(coef.items())], rhs])
    for j in range(n):
        idx[json.dumps(["ub", j])] = len(prows)
        prows.append([[[j, 1]], ub[j]])
    prob = {"n": n, "rows": prows, "c": [[j, 1] for j in range(n)], "T": 54 - len(D), "nonneg": list(range(n))}

    def tr(node):
        if "leaf" in node:
            c = node["leaf"]
            return {"leaf": {"K": c["K"], "y": [[["base", idx[json.dumps(rt[1])]] if rt[0] == "base" else rt, y]
                                                for rt, y in c["y"]]}}
        return {"branch": [[node["branch"], 1]], "f": node["f"], "le": tr(node["le"]), "ge": tr(node["ge"])}
    return prob, tr


def coq_lp_tag(rt, y):
    if rt[0] == "br":
        return f"yB {rt[1]} {y}"
    t = rt[1]
    if t[0] == "ub":
        return f"yU {t[1]} {y}"
    return f"yR ({coq_tag(t[1])}) {y}"


def coq_lp_tree(node):
    if "leaf" in node:
        c = node["leaf"]
        return f"(lf {c['K']} {coq_list(coq_lp_tag(rt, y) for rt, y in c['y'])})"
    return f"(nd {node['branch']} {node['f']} {coq_lp_tree(node['le'])} {coq_lp_tree(node['ge'])})"


LPHEADER = ["(* Generated by tools/iota4/link23_coq.py; do not edit. *)",
            "From Coq Require Import List NArith.", "Import ListNotations.",
            "From Sunflower Require Import Sunflower Link23.", ""]


def emit_shard_lp(items, out, name):
    """One module: the class list as a definition; the LPCert trees only
    inside the opaque proof of [NAME_ok] ([Link23.checked_of_ltrees]),
    so that requiring the module does not load them.  items: (id, D, lptree)."""
    Ds = [coq_list(coq_list(C_) for C_ in D) for _, D, _ in items]
    lines = list(LPHEADER)
    lines.append(f"(** {len(Ds)} link classes; ids: {coq_list(k for k, _, _ in items)}. *)")
    lines.append(f"Definition {name}_classes : list Family :=")
    lines.append("  [" + ";\n   ".join(Ds) + "].")
    lines.append("")
    lines.append(f"Lemma {name}_ok : forall D, In D {name}_classes -> CheckedClass D.")
    lines.append("Proof.")
    lines.append("  apply (checked_of_ltrees")
    lines.append("    [" + ";\n     ".join(f"(nth {i} {name}_classes [], {coq_lp_tree(lt)})"
                                          for i, (_, _, lt) in enumerate(items)) + "]).")
    lines.append("  - vm_compute. reflexivity.")
    lines.append("  - vm_compute. reflexivity.")
    lines.append("Qed.")
    lines.append("")
    open(out, "w").write("\n".join(lines))


# ---------------------------------------------------------------- Coq output

def coq_list(items):
    return "[" + "; ".join(str(x) for x in items) + "]"


def coq_tag(tag):
    if tag[0] in ("RCap", "RCapI", "RLink"):
        return f"{tag[0]} {coq_list(tag[1])}"
    if tag[0] == "RStar" or tag[0] == "RDet":
        return f"{tag[0]} {tag[1]}"
    if tag[0] == "RIota":
        return "RIota"
    return f"RExcl {tag[1]} {tag[2]}"


def coq_tree(node):
    if "leaf" in node:
        c = node["leaf"]
        ys = coq_list(f"({coq_tag(tag)}, {y}%N)" for tag, y in c["y"])
        return f"(Leaf (mkleafN {c['K']}%N {ys} {coq_list(c['u'])}%N {coq_list(c['v'])}%N))"
    return f"(Node {node['var']} {node['f']} {coq_tree(node['le'])} {coq_tree(node['ge'])})"


HEADER = ["(* Generated by tools/iota4/link23_coq.py; do not edit. *)",
          "From Coq Require Import List NArith.", "Import ListNotations.",
          "From Sunflower Require Import Sunflower LinkLP Link23.", ""]


def emit(D, path, out, name):
    C = json.load(gzip.open(path, "rt"))
    lines = HEADER + [
             f"Definition {name}_D : Family := {coq_list(coq_list(C_) for C_ in D)}.", "",
             f"Definition {name}_t : tree :=", "  " + coq_tree(C["tree"]) + ".", "",
             f"(** [uniform4b], [setnodupb] and [Link23.classcheck] on this class, by computation. *)",
             f"Lemma {name}_ok : trees_okb [({name}_D, {name}_t)] = true.",
             "Proof. vm_compute. reflexivity. Qed.", ""]
    open(out, "w").write("\n".join(lines))


def batch(cls, size, shard, out):
    """Trees for every class of the given link size in shard i/n, as one JSON list."""
    i, n = map(int, shard.split("/"))
    fams = load_some(cls, size, lambda j: j % n == i)     # the same classes as keep[i::n] over [load]
    keep = sorted(fams)
    docs = []
    failed = []
    for k in keep:
        D = canon(fams[k])
        try:
            stats, doc = solve(D, None)
        except SystemExit as e:          # the model does not certify this class
            failed.append(k)
            print(k, "FAILED:", e, flush=True)
            continue
        check_doc(D, doc)
        doc["k"] = k
        docs.append(doc)
        print(k, stats, flush=True)
    with gzip.open(out, "wt") as fh:
        json.dump(docs, fh)
    print("wrote", out, len(docs), "classes; failed", len(failed), failed)


def emit_shard_h(cls, path, out, name, fams=None):
    """One module of hinted trees ([Link23.htrees_okb])."""
    fams = load(cls) if fams is None else fams
    docs = json.load(gzip.open(path, "rt"))
    lines = list(HEADER)
    names = []
    for doc in docs:
        k = doc["k"]; D = canon(fams[k]); nm = f"{name}_{k}"
        lines.append(f"Definition {nm}_D : Family := {coq_list(coq_list(C_) for C_ in D)}.")
        lines.append(f"Definition {nm}_h : list nat := {coq_list(hints_fast(D))}.")
        lines.append(f"Definition {nm}_t : tree := {coq_tree(doc['tree'])}.")
        names.append(nm)
    lines.append("")
    lines.append(f"Definition {name}_all : list (Family * (list nat * tree)) :=")
    lines.append("  [" + ";\n   ".join(f"({nm}_D, ({nm}_h, {nm}_t))" for nm in names) + "].")
    lines.append("")
    lines.append(f"Lemma {name}_all_ok : htrees_okb {name}_all = true.")
    lines.append("Proof. vm_compute. reflexivity. Qed.")
    lines.append("")
    open(out, "w").write("\n".join(lines))
    print("wrote", out, len(names), "classes")


def coq_tree_sparse(node):
    """[coq_tree] with [LeafS]: only the nonzero entries of u and v."""
    if "leaf" in node:
        c = node["leaf"]
        ys = coq_list(f"({coq_tag(tag)}, {y}%N)" for tag, y in c["y"])
        us = coq_list(f"({i}, {q}%N)" for i, q in enumerate(c["u"]) if q)
        vs = coq_list(f"({i}, {q}%N)" for i, q in enumerate(c["v"]) if q)
        return f"(LeafS (mkleafS {c['K']}%N {ys} {us} {vs}))"
    return f"(Node {node['var']} {node['f']} {coq_tree_sparse(node['le'])} {coq_tree_sparse(node['ge'])})"


def emit_shard_m(cls, docs, out, name, fams):
    """One module: the class list as a definition; the trees (sparse leaves,
    checked by [Link23.classcheck_m], no hints) only inside the opaque proof
    of [NAME_ok], so that requiring the module does not load them."""
    Ds = [coq_list(coq_list(C_) for C_ in canon(fams[doc["k"]])) for doc in docs]
    lines = list(HEADER)
    lines.append(f"(** {len(Ds)} link classes; ids in the class file: {coq_list(doc['k'] for doc in docs)}. *)")
    lines.append(f"Definition {name}_classes : list Family :=")
    lines.append("  [" + ";\n   ".join(Ds) + "].")
    lines.append("")
    lines.append(f"Lemma {name}_ok : forall D, In D {name}_classes -> CheckedClass D.")
    lines.append("Proof.")
    lines.append("  apply (checked_of_mtrees")
    lines.append("    [" + ";\n     ".join(f"(nth {i} {name}_classes [], {coq_tree_sparse(doc['tree'])})"
                                          for i, doc in enumerate(docs)) + "]).")
    lines.append("  - vm_compute. reflexivity.")
    lines.append("  - vm_compute. reflexivity.")
    lines.append("Qed.")
    lines.append("")
    open(out, "w").write("\n".join(lines))


def emit_shard_c(cls, path, out, name, fams=None):
    """One module: the class list as a definition; the hinted certificates
    as section-local [Let]s, so that only [NAME_classes] and [NAME_ok]
    survive the section and [Require] does not load the certificates."""
    fams = load(cls) if fams is None else fams
    docs = json.load(gzip.open(path, "rt"))
    Ds, ents = [], []
    lets = []
    for doc in docs:
        k = doc["k"]; D = canon(fams[k])
        d = coq_list(coq_list(C_) for C_ in D)
        Ds.append(d)
        lets.append(f"  Let h{k} : list nat := {coq_list(hints_fast(D))}.")
        lets.append(f"  Let t{k} : tree := {coq_tree(doc['tree'])}.")
        ents.append(f"(nth {len(ents)} {name}_classes [], (h{k}, t{k}))")
    lines = list(HEADER)
    lines.append(f"(** {len(Ds)} link classes; ids in the class file: {coq_list(doc['k'] for doc in docs)}. *)")
    lines.append(f"Definition {name}_classes : list Family :=")
    lines.append("  [" + ";\n   ".join(Ds) + "].")
    lines.append("")
    lines.append(f"Section {name.upper()}.")
    lines.extend(lets)
    lines.append(f"  Let all : list (Family * (list nat * tree)) :=")
    lines.append("    [" + ";\n     ".join(ents) + "].")
    lines.append(f"  Let all_ok : htrees_okb all = true. Proof. vm_compute. reflexivity. Qed.")
    lines.append(f"  Lemma {name}_ok : forall D, In D {name}_classes -> CheckedClass D.")
    lines.append(f"  Proof. apply (checked_of_htrees all); [exact all_ok | vm_compute; reflexivity]. Qed.")
    lines.append(f"End {name.upper()}.")
    lines.append("")
    open(out, "w").write("\n".join(lines))
    print("wrote", out, len(Ds), "classes")


def emit_shard(cls, path, out, name):
    fams = load(cls)
    docs = json.load(gzip.open(path, "rt"))
    lines = list(HEADER)
    names = []
    for doc in docs:
        k = doc["k"]; D = canon(fams[k]); nm = f"{name}_{k}"
        lines.append(f"Definition {nm}_D : Family := {coq_list(coq_list(C_) for C_ in D)}.")
        lines.append(f"Definition {nm}_t : tree := {coq_tree(doc['tree'])}.")
        names.append(nm)
    lines.append("")
    lines.append(f"Definition {name}_all : list (Family * tree) :=")
    lines.append("  [" + ";\n   ".join(f"({nm}_D, {nm}_t)" for nm in names) + "].")
    lines.append("")
    lines.append(f"Lemma {name}_all_ok : trees_okb {name}_all = true.")
    lines.append("Proof. vm_compute. reflexivity. Qed.")
    lines.append("")
    open(out, "w").write("\n".join(lines))
    print("wrote", out, len(names), "classes")


def lpconvert(cls, trees, out):
    """Every tree of TREES (§69 form) in LPCert form, each checked exactly
    with the LPCert semantics ([lp_check]) after conversion; one JSON list
    of {"k", "D", "lt"} with D the class as Coq sees it."""
    docs = []
    for f in trees.split(","):
        docs += json.load(gzip.open(f, "rt"))
    fams = load_ks(cls, [d["k"] for d in docs])
    res = []
    for d in docs:
        D = canon(fams[d["k"]])
        mdl = model(D)
        assert d["n"] == len(mdl[1]) and d["Delta"] == len(D)
        lt = lp_of_doc(d, mdl[2])
        lp_check(D, lt, mdl)
        res.append({"k": d["k"], "D": D, "lt": lt})
    with gzip.open(out + ".tmp", "wt") as fh:
        json.dump(res, fh)
    os.replace(out + ".tmp", out)
    print("converted", len(res), "->", out, flush=True)


def lpshards(inputs, prefix, budget):
    """Modules coq/PREFIXi.v of about BUDGET bytes of certificate text each,
    classes in increasing k; returns the module count."""
    items = []
    for f in inputs.split(","):
        items += [(e["k"], e["D"], e["lt"]) for e in json.load(gzip.open(f, "rt"))]
    items.sort(key=lambda e: e[0])
    assert len(set(k for k, _, _ in items)) == len(items), "a class twice"
    groups, cur, size = [], [], 0
    for it in items:
        c = len(coq_lp_tree(it[2])) + 300
        if cur and size + c > budget:
            groups.append(cur); cur, size = [], 0
        cur.append(it); size += c
    if cur:
        groups.append(cur)
    for n, g in enumerate(groups):
        emit_shard_lp(g, f"coq/{prefix}{n}.v", f"l{prefix[4:].lower()}{n}")
    print("wrote", len(groups), "modules for", len(items), "classes", flush=True)
    return len(groups)


if __name__ == "__main__":
    mode, cls = sys.argv[1], sys.argv[2]
    if mode == "lpconvert":      # lpconvert CLASSES.gz TREES1.json.gz,... OUT.json.gz
        lpconvert(cls, sys.argv[3], sys.argv[4]); sys.exit(0)
    if mode == "lpshards":       # lpshards - CONVERTED1.json.gz,... PREFIX BUDGET
        lpshards(sys.argv[3], sys.argv[4], int(sys.argv[5])); sys.exit(0)
    if mode == "batch":          # batch CLASSES.gz SIZE i/n OUT.json.gz
        batch(cls, int(sys.argv[3]), sys.argv[4], sys.argv[5]); sys.exit(0)
    if mode == "coqshard":       # coqshard CLASSES.gz TREES.json.gz OUT.v NAME
        emit_shard(cls, sys.argv[3], sys.argv[4], sys.argv[5]); sys.exit(0)
    if mode == "coqshard_h":     # coqshard_h CLASSES.gz TREES.json.gz OUT.v NAME   (with witness hints)
        emit_shard_h(cls, sys.argv[3], sys.argv[4], sys.argv[5]); sys.exit(0)
    if mode == "coqshards_m":    # coqshards_m CLASSES.gz TREES1.json.gz,... PREFIX BUDGET: modules of about BUDGET bytes of certificate
        fams = load(cls)
        docs = []
        for f in sys.argv[3].split(","):
            docs += json.load(gzip.open(f, "rt"))
        docs.sort(key=lambda d: d["k"])
        budget = int(sys.argv[5])       # compile memory grows with the certificate text (about 3 GB per MB)
        groups, cur, size = [], [], 0
        for d in docs:
            c = len(coq_tree_sparse(d["tree"])) + 300
            if cur and size + c > budget:
                groups.append(cur); cur, size = [], 0
            cur.append(d); size += c
        if cur:
            groups.append(cur)
        for n, g in enumerate(groups):
            emit_shard_m(cls, g, f"coq/{sys.argv[4]}{n}.v", f"l{sys.argv[4][4:].lower()}{n}", fams)
        print("wrote", len(groups), "modules for", len(docs), "classes")
        sys.exit(0)
    if mode == "coqshards_c":    # coqshards_c CLASSES.gz TREEDIR PREFIX FIRST LAST: opaque-certificate modules
        fams = load(cls)
        for i in range(int(sys.argv[5]), int(sys.argv[6]) + 1):
            emit_shard_c(cls, f"{sys.argv[3]}/shard_{i}.json.gz", f"coq/{sys.argv[4]}{i}.v",
                         f"l{sys.argv[4][4:].lower()}{i}", fams)
        sys.exit(0)
    if mode == "coqshards_h":    # coqshards_h CLASSES.gz TREEDIR PREFIX FIRST LAST: TREEDIR/shard_i.json.gz -> coq/PREFIXi.v
        fams = load(cls)
        for i in range(int(sys.argv[5]), int(sys.argv[6]) + 1):
            emit_shard_h(cls, f"{sys.argv[3]}/shard_{i}.json.gz", f"coq/{sys.argv[4]}{i}.v",
                         f"l{sys.argv[4][4:].lower()}{i}", fams)
        sys.exit(0)
    k = int(sys.argv[3])
    D = canon(load(cls)[k])
    if mode == "solve":
        print(k, solve(D, sys.argv[4])[0], flush=True)
    elif mode == "check":
        print(k, check(D, sys.argv[4]), flush=True)
    elif mode == "coq":
        emit(D, sys.argv[4], sys.argv[5], sys.argv[6])
        print("wrote", sys.argv[5])
    elif mode == "info":
        U, ts, ub, big, rows = model(D)
        print(k, "Delta", len(D), "V", len(coq_points(D)), "unwit", len(U), "types", len(ts), "rows", len(rows), "big", big)
