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

    python3 -I tools/multicolored/cubes.py D n K s r TREE worker workers cube_tl total_tl [prefix|-] [under]

TREE is a depth d (every node above depth d is expanded) or a JSON file
{"expand": [path, ...]} naming the expanded nodes, a path being the list of
child indices from the root ([] is the root). Leaves are ordered easiest
first (most forbidden triples), and worker w solves those at positions
= w (mod workers) in that order. With under (a path such as 5-48), only
the leaves below that node are solved. With prefix, worker
0 writes the base CNF to prefix_r<r>_base.cnf; every worker records the
SHA-256 of its own base clauses (so all workers can be checked to share it)
and, for every leaf it proves infeasible, appends a line to
prefix_r<r>_closed_w<w>.jsonl. If it had learned Farkas clauses by then, it
also writes prefix_r<r>_cube_<path>.delta.cnf (path joined by "-", "root" for
the root): those clauses plus the leaf's units. Otherwise the line says
"units_only", since the delta would be the leaf's units, which the leaf list
determines. A leaf with a delta file or a units-only line is skipped, so a
run can be resumed or refined. Forbidden sets are stored in the leaf list as
hexadecimal bitmasks (bit k = triple k). The base
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
            out.append({"path": list(path), "fixed": list(fixed), "forbidden": to_hex(forb),
                        "nforbidden": len(forb), "group_order": len(G)})
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


def to_hex(xs):
    """A set of triple indices as a hexadecimal bitmask (bit k = triple k)."""
    m = 0
    for x in xs:
        m |= 1 << x
    return format(m, "x")


def forbidden(leaf):
    """The forbidden indices of a leaf, from a bitmask or (older files) a list."""
    f = leaf["forbidden"]
    if isinstance(f, list):
        return f
    m = int(f, 16)
    return [k for k in range(m.bit_length()) if m >> k & 1]


def closed_cubes(prefix, r):
    """Leaves already closed: a delta file, or a units-only record in a
    worker's log (prefix_r<r>_closed_w<w>.jsonl)."""
    done = set()
    d = os.path.dirname(os.path.abspath(prefix))
    base = os.path.basename(prefix) + f"_r{r}_"
    for fn in os.listdir(d):
        if fn.startswith(base + "cube_") and fn.endswith(".delta.cnf"):
            done.add(fn[len(base + "cube_"):-len(".delta.cnf")])
        elif fn.startswith(base + "closed_w") and fn.endswith(".jsonl"):
            with open(os.path.join(d, fn)) as f:
                for line in f:
                    if line.endswith("\n"):          # a line cut by a crash is ignored
                        rec = json.loads(line)
                        if rec.get("units_only"):
                            done.add(rec["cube"])
    return done


def main():
    D, n, K, s, r = (int(x) for x in sys.argv[1:6])
    tree = sys.argv[6]
    w, W = int(sys.argv[7]), int(sys.argv[8])
    expand = int(tree) if tree.isdigit() else {tuple(p) for p in json.load(open(tree))["expand"]}
    cube_tl, total_tl = float(sys.argv[9]), float(sys.argv[10])
    prefix = sys.argv[11] if len(sys.argv) > 11 and sys.argv[11] != "-" else None
    under = [int(x) for x in sys.argv[12].split("-")] if len(sys.argv) > 12 else None
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
    assert all(len(l["fixed"]) <= s for l in L), "an expanded node fixes s or more triples (Lemma 84.A)"
    done = closed_cubes(prefix, r) if prefix else set()
    if prefix and w == 0:
        with open(f"{prefix}_r{r}_leaves.json.tmp", "w") as f:
            json.dump(spec, f)
        os.replace(f"{prefix}_r{r}_leaves.json.tmp", f"{prefix}_r{r}_leaves.json")
    # easiest first: most forbidden triples, then most fixed
    order = sorted(range(len(L)), key=lambda k: (-L[k]["nforbidden"], -len(L[k]["fixed"]), k))
    out = {"D": D, "n": n, "K": K, "s": s, "run": r, "tree": tree, "worker": w, "workers": W,
           "leaves": len(L), "setup_s": st["setup"], "base_sha256": sha, "closed_before": 0,
           "not_started": 0, "cubes": []}
    log = open(f"{prefix}_r{r}_closed_w{w}.jsonl", "a") if prefix else None
    v = lambda k: k + 1
    if under is not None:                       # only the leaves below one node
        order = [k for k in order if L[k]["path"][:len(under)] == under]
    for pos, k in enumerate(order):
        leaf = L[k]
        if pos % W != w:
            continue
        dpath = f"{prefix}_r{r}_cube_{name(leaf)}.delta.cnf" if prefix else None
        if name(leaf) in done:
            out["closed_before"] += 1
            continue
        left = total_tl - (time.time() - t0)
        if left <= 0:
            out["not_started"] += 1
            continue
        units = [v(f) for f in leaf["fixed"]] + [-v(x) for x in forbidden(leaf)]
        tc = time.time()
        res = S.solve_loop(st, units, min(cube_tl, left), tc, tag=name(leaf))
        res = {"cube": name(leaf), "forbidden": leaf["nforbidden"], "seconds": round(time.time() - tc, 1),
               **{x: res[x] for x in res if x != "clauses"}}
        if res["status"] == "infeasible" and prefix:
            farkas = st["C"].all[st["nbase"]:]
            if farkas:                          # the delta needs its Farkas clauses: write it out
                S.write_cnf(dpath + ".tmp", st["top"], farkas + [[u] for u in units])
                os.replace(dpath + ".tmp", dpath)   # a delta file exists only once complete
            # with no Farkas clause the delta is the leaf's units, which the leaf
            # list determines: record the closure in the worker's log instead
            log.write(json.dumps({"cube": name(leaf), "units_only": not farkas, "seconds": res["seconds"],
                                  "solves": res["solves"], "farkas_certs": res["farkas_certs"]}) + "\n")
            log.flush()
            os.fsync(log.fileno())
        out["cubes"].append(res)
        print(json.dumps({"cube": name(leaf), "status": res["status"], "seconds": res["seconds"]}),
              file=sys.stderr, flush=True)
        if res["status"].startswith(("found", "face")):
            break
    sts = [c["status"] for c in out["cubes"]]
    out["seconds"] = round(time.time() - t0, 1)
    # the verdict covers this worker's share of the leaves (or the "under" subtree) only
    out["verdict"] = ("found" if "found" in sts else
                      "all attempted cubes infeasible, none left" if all(x == "infeasible" for x in sts)
                      and out["not_started"] == 0 else "undecided")
    print(json.dumps(out))


if __name__ == "__main__":
    main()
