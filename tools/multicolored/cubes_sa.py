#!/usr/bin/env python3
"""Solve cubes.py leaves with the standalone cadical binary, one process per leaf.

docs/roadmap.md section 85. For each open leaf of the tree, base + the leaf's
units goes to cadical on standard input. cadical simplifies the formula under
the units before it searches, which the incremental solver of cubes.py
cannot do with assumptions; on three hard leaves of D = 4 run class 0 it was
4 to 40 times faster than PySAT times extrapolated from comparable leaves
(roadmap section 85.3; the cause is conjectured). If cadical finds a model, the Benders step of
satmaster.py runs on it: a face is reported, or the minimised Farkas
certificate is re-checked exactly and added as a clause, with its images
under the run class representative's stabiliser, for every later leaf of this
worker; the leaf is then solved again.

    python3 -I tools/multicolored/cubes_sa.py D n K s r TREE worker workers leaf_tl total_tl prefix [tag]

TREE is as for cubes.py. The base CNF is read from prefix_r<r>_base.cnf.
Leaves already closed (a delta file, or a units-only or pool line in any
prefix_r<r>_closed_*.jsonl) are skipped; the open ones are taken easiest
first, worker w taking positions = w (mod workers). A leaf proved
unsatisfiable is logged to prefix_r<r>_closed_w<tag>.jsonl (tag defaults to
sa<worker>), units_only when no Farkas clause was in the formula. The
Farkas clauses a worker learns are appended, in the order learned, to its
pool file prefix_r<r>_pool_w<tag>_<start>.cnf (one clause per line, no
header; start is the worker's start time in seconds), and a leaf closed with
Farkas clauses in the formula records the pool and the number of its clauses
used: its delta is those clauses plus its units, which certcubes.py rebuilds.
(A delta file per leaf, the earlier format, repeated the worker's clauses
in every file; certcubes.py reads both.) A leaf that runs past leaf_tl
seconds is logged to prefix_r<r>_timeout_w<tag>.jsonl and left open. A model
that is a face stops the worker: "found" with integer weights re-checked
exactly, or "face, no integer certificate".
"""
import json, os, subprocess, sys, time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import benders as B
import cubes
import satmaster as S


def model_of(out, N):
    lits = set()
    for line in out.splitlines():
        if line.startswith("v "):
            lits.update(int(x) for x in line[2:].split())
    return {k for k in range(N) if (k + 1) in lits}


def main():
    D, n, K, s, r = (int(x) for x in sys.argv[1:6])
    tree = sys.argv[6]
    w, W = int(sys.argv[7]), int(sys.argv[8])
    leaf_tl, total_tl = float(sys.argv[9]), float(sys.argv[10])
    prefix = sys.argv[11]
    tag = sys.argv[12] if len(sys.argv) > 12 else f"sa{w}"
    t0 = time.time()
    expand = int(tree) if tree.isdigit() else {tuple(p) for p in json.load(open(tree))["expand"]}
    T = B.Sn(D, n)
    A, N = D ** n, len(T)
    mono = [B.nmono(D, n, t) for t in T]
    rep = next(k for k in range(N) if mono[k] == r)
    index = {t: k for k, t in enumerate(T)}
    H = [g for g in B.group_maps(D, n) if g(T[rep]) == T[rep]]
    st = {"T": T, "N": N, "mono": mono, "r": r, "rep": rep, "index": index, "H": H}
    L = cubes.leaves(st, expand)
    assert all(len(l["fixed"]) <= s for l in L), "an expanded node fixes s or more triples (Lemma 84.A)"
    with open(f"{prefix}_r{r}_base.cnf", "rb") as f:
        head = f.readline().split()
        body = f.read()
    nv, nb = int(head[2]), int(head[3])
    d = os.path.dirname(os.path.abspath(prefix))
    stem = os.path.basename(prefix) + f"_r{r}_"
    done = set()
    for fn in os.listdir(d):
        if fn.startswith(stem + "cube_") and fn.endswith(".delta.cnf"):
            done.add(fn[len(stem + "cube_"):-len(".delta.cnf")])
        elif fn.startswith(stem + "closed_") and fn.endswith(".jsonl"):
            for line in open(os.path.join(d, fn)):
                if line.endswith("\n"):            # a line cut by a crash is ignored
                    rec = json.loads(line)
                    if rec.get("units_only") or "pool" in rec:
                        done.add(rec["cube"])
    todo = [l for l in L if cubes.name(l) not in done]
    todo.sort(key=lambda l: (-l["nforbidden"], -len(l["fixed"]), l["path"]))
    mine = todo[w::W]
    log = open(f"{prefix}_r{r}_closed_w{tag}.jsonl", "a")
    tlog = open(f"{prefix}_r{r}_timeout_w{tag}.jsonl", "a")
    pool_name = os.path.basename(prefix) + f"_r{r}_pool_w{tag}_{int(t0)}.cnf"
    pool = open(os.path.join(d, pool_name), "a")
    farkas, seen = [], set()
    out = {"D": D, "n": n, "K": K, "s": s, "run": r, "tree": tree, "worker": w, "workers": W,
           "leaves": len(L), "open": len(todo), "mine": len(mine), "closed": 0, "timeouts": 0,
           "not_started": 0, "farkas_certs": 0, "found": None}
    for leaf in mine:
        left = total_tl - (time.time() - t0)
        if left <= 0:
            out["not_started"] += 1
            continue
        nm = cubes.name(leaf)
        units = [x + 1 for x in leaf["fixed"]] + [-(x + 1) for x in cubes.forbidden(leaf)]
        tc, solves, status = time.time(), 0, None
        while status is None:
            extra = farkas + [[u] for u in units]
            cnf = (f"p cnf {nv} {nb + len(extra)}\n".encode() + body
                   + "".join(" ".join(map(str, c)) + " 0\n" for c in extra).encode())
            budget = min(leaf_tl - (time.time() - tc), left - (time.time() - tc))
            try:
                p = subprocess.run(["cadical", "-q"], input=cnf, capture_output=True, timeout=max(1.0, budget))
            except subprocess.TimeoutExpired:
                status = "time"
                break
            solves += 1
            if p.returncode == 20:
                status = "infeasible"
            elif p.returncode == 10:
                phi = model_of(p.stdout.decode(), N)
                cert = B.farkas(T, A, phi)
                if cert is None:
                    u = B.face_weights(T, A, phi)
                    status = "found" if u else "face, no integer certificate"
                    out["found"] = {"cube": nm, "phi": sorted(phi), "cert": {"D": D, "n": n, "u": u} if u else None}
                    break
                lam, mu = B.minimise(T, A, phi, *cert)
                if S.exact_farkas(T, A, lam, mu) is None:
                    status = "inexact certificate"
                    break
                out["farkas_certs"] += 1
                for g in H:
                    gl = frozenset(index[g(T[k])] for k in lam)
                    gm = frozenset(index[g(T[k])] for k in mu)
                    if (gl, gm) not in seen:
                        seen.add((gl, gm))
                        farkas.append([-(k + 1) for k in gl] + [k + 1 for k in gm])
                        pool.write(" ".join(map(str, farkas[-1])) + " 0\n")
                pool.flush()
                os.fsync(pool.fileno())             # on disk before any log line uses it
            else:
                status = f"cadical exit {p.returncode}"
        secs = round(time.time() - tc, 1)
        if status == "infeasible":
            rec = {"cube": nm, "units_only": not farkas, "seconds": secs, "solves": solves,
                   "farkas_certs": out["farkas_certs"], "engine": "cadical"}
            if farkas:
                rec.update(pool=pool_name, pool_clauses=len(farkas))
            log.write(json.dumps(rec) + "\n")
            log.flush()
            os.fsync(log.fileno())
            out["closed"] += 1
        elif status == "time":
            tlog.write(json.dumps({"cube": nm, "seconds": secs, "nforbidden": leaf["nforbidden"]}) + "\n")
            tlog.flush()
            out["timeouts"] += 1
        else:
            out["status_of_" + nm] = status
            print(json.dumps({"cube": nm, "status": status}), file=sys.stderr, flush=True)
            break
    out["seconds"] = round(time.time() - t0, 1)
    print(json.dumps(out))


if __name__ == "__main__":
    main()
