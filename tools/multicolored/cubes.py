#!/usr/bin/env python3
"""Cube-and-conquer for satmaster.py's search, one run class at a time.

docs/roadmap.md section 84. A cube is a set of fixed triples and a set of
forbidden triples. The root is the run class: its representative fixed,
nothing forbidden, symmetry group G_0 = the representative's stabiliser.
A node (F, X, G) is refined as follows. The candidates are the triples
allowed in the run class, not in F or X, and compatible with every element
of F (no fibre, Lemma 81.A or Lemma 83.A pair). Split them into G-orbits
O_1, O_2, ..., ordered by least index, with representatives o_j = min O_j.
Child j is (F + [o_j], X u O_1 u ... u O_{j-1}, Stab_G(o_j)). The leaves of
any tree built this way (each expanded node replaced by all its children)
cover the run class (Lemma 84.A): no face of the question in the run class
escapes every leaf, up to the symmetry group.

Every leaf is solved by satmaster.solve_loop under the assumptions "F true,
X false". All leaves of one worker share one incremental solver, so Farkas
clauses learned in one cube (valid for every face) help the next.

    python3 -I tools/multicolored/cubes.py D n K s r TREE worker workers cube_tl total_tl [prefix]

TREE is a depth d (every node above depth d is expanded) or a JSON file
{"expand": [path, ...]} naming the expanded nodes, a path being the list of
child indices from the root ([] is the root). Leaves are ordered easiest
first (most forbidden triples), and worker w solves those at positions
= w (mod workers) in that order. With prefix, worker
0 writes the base CNF to prefix_r<r>_base.cnf; every worker records the
SHA-256 of its own base clauses (so all workers can be checked to share it)
and, for every leaf it proves infeasible, writes
prefix_r<r>_cube_<path>.delta.cnf (path joined by "-", "root" for the root):
the Farkas clauses it had learned so far, plus the leaf's units. A leaf whose
delta file already exists is skipped, so a run can be resumed or refined. The base
plus a delta is the leaf's full CNF. The leaf list goes to
prefix_r<r>_leaves.json for tools/multicolored/checkcnf.py cover.
"""
import hashlib, json, os, sys, time

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import benders as B
import satmaster as S


def leaves(st, expand):
    """The leaves of the cube tree. expand is either an int d (expand every
    node at depth below d) or a set of node paths (tuples of child indices)
    to expand; the root is the path ()."""
    T, N, mono, r, rep, index = st["T"], st["N"], st["mono"], st["r"], st["rep"], st["index"]
    perms = np.array([[index[g(T[k])] for k in range(N)] for g in st["H"]], dtype=np.int64)
    bad = B.incompatible(T)
    for a, b in S.twoplusone(T):
        bad[a, b] = bad[b, a] = True
    allowed = np.array([m <= r for m in mono])
    grow = (lambda p: len(p) < expand) if isinstance(expand, int) else (lambda p: p in expand)
    out, stack = [], [((), (rep,), frozenset(), perms)]
    while stack:
        path, fixed, forb, G = stack.pop(0)
        if not grow(path):
            out.append({"path": list(path), "fixed": list(fixed), "forbidden": sorted(forb),
                        "group_order": len(G)})
            continue
        ok = allowed.copy()
        ok[list(fixed)] = False
        if forb:
            ok[list(forb)] = False
        for f in fixed:
            ok &= ~bad[f]
        seen, orbits = set(), []
        for k in np.where(ok)[0].tolist():
            if k in seen:
                continue
            orb = set(G[:, k].tolist())
            seen |= orb
            orbits.append(sorted(orb))
        acc, kids = set(forb), []
        for j, orb in enumerate(orbits):
            o = orb[0]
            kids.append((path + (j,), fixed + (o,), frozenset(acc), G[G[:, o] == o]))
            acc |= set(orb)
        stack = kids + stack                    # depth first, children in order
    return out


def name(leaf):
    return "-".join(map(str, leaf["path"])) or "root"


def main():
    D, n, K, s, r = (int(x) for x in sys.argv[1:6])
    tree = sys.argv[6]
    w, W = int(sys.argv[7]), int(sys.argv[8])
    expand = int(tree) if tree.isdigit() else {tuple(p) for p in json.load(open(tree))["expand"]}
    cube_tl, total_tl = float(sys.argv[9]), float(sys.argv[10])
    prefix = sys.argv[11] if len(sys.argv) > 11 else None
    t0 = time.time()
    st = S.build(D, n, K, s, r, keep=prefix is not None)
    base = st["C"].all[:st["nbase"]] if prefix else []
    sha = hashlib.sha256("\n".join(" ".join(map(str, c)) for c in base).encode()).hexdigest() if prefix else None
    if prefix and w == 0:                       # written atomically: a checker may be reading it
        S.write_cnf(f"{prefix}_r{r}_base.cnf.tmp", st["top"], base)
        os.replace(f"{prefix}_r{r}_base.cnf.tmp", f"{prefix}_r{r}_base.cnf")
    L = leaves(st, expand)
    spec = {"D": D, "n": n, "K": K, "s": s, "run": r,
            "expand": (sorted(list(p) for p in expand) if isinstance(expand, set) else None),
            "depth": expand if isinstance(expand, int) else None, "leaves": L}
    if prefix and w == 0:
        with open(f"{prefix}_r{r}_leaves.json", "w") as f:
            json.dump(spec, f)
    # easiest first: most forbidden triples, then most fixed
    order = sorted(range(len(L)), key=lambda k: (-len(L[k]["forbidden"]), -len(L[k]["fixed"]), k))
    out = {"D": D, "n": n, "K": K, "s": s, "run": r, "tree": tree, "worker": w, "workers": W,
           "leaves": len(L), "setup_s": st["setup"], "base_sha256": sha, "cubes": []}
    v = lambda k: k + 1
    for pos, k in enumerate(order):
        leaf = L[k]
        if pos % W != w:
            continue
        dpath = f"{prefix}_r{r}_cube_{name(leaf)}.delta.cnf" if prefix else None
        if dpath and os.path.exists(dpath):
            out["cubes"].append({"cube": name(leaf), "status": "infeasible (earlier run)"})
            continue
        left = total_tl - (time.time() - t0)
        if left <= 0:
            out["cubes"].append({"cube": name(leaf), "status": "not started"})
            continue
        units = [v(f) for f in leaf["fixed"]] + [-v(x) for x in leaf["forbidden"]]
        tc = time.time()
        res = S.solve_loop(st, units, min(cube_tl, left), tc, tag=name(leaf))
        res = {"cube": name(leaf), "forbidden": len(leaf["forbidden"]), "seconds": round(time.time() - tc, 1),
               **{x: res[x] for x in res if x != "clauses"}}
        if res["status"] == "infeasible" and prefix:
            delta = st["C"].all[st["nbase"]:] + [[u] for u in units]
            S.write_cnf(dpath + ".tmp", st["top"], delta)
            os.replace(dpath + ".tmp", dpath)   # a delta file exists only once complete
        out["cubes"].append(res)
        print(json.dumps({"cube": name(leaf), "status": res["status"], "seconds": res["seconds"]}),
              file=sys.stderr, flush=True)
        if res["status"].startswith(("found", "face")):
            break
    sts = [c["status"] for c in out["cubes"]]
    out["seconds"] = round(time.time() - t0, 1)
    out["verdict"] = ("found" if "found" in sts else
                      "all cubes infeasible" if sts and all(x.startswith("infeasible") for x in sts)
                      else "undecided")
    print(json.dumps(out))


if __name__ == "__main__":
    main()
