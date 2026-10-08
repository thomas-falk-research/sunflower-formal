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

The checker here is only a convenience: the kernel check is
[Link23.classcheck] in Coq.
"""
import sys, os, json, gzip, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from linkcert import load, validate


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


def rows_of(D, U, ts, big):
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
    fams = load(cls)
    keep = [k for k, F in enumerate(fams) if len(F) == size]
    i, n = map(int, shard.split("/"))
    keep = keep[i::n]
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


if __name__ == "__main__":
    mode, cls = sys.argv[1], sys.argv[2]
    if mode == "batch":          # batch CLASSES.gz SIZE i/n OUT.json.gz
        batch(cls, int(sys.argv[3]), sys.argv[4], sys.argv[5]); sys.exit(0)
    if mode == "coqshard":       # coqshard CLASSES.gz TREES.json.gz OUT.v NAME
        emit_shard(cls, sys.argv[3], sys.argv[4], sys.argv[5]); sys.exit(0)
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
