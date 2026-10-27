#!/usr/bin/env python3
"""Certify one run class's cubes.py result.

docs/roadmap.md section 84. For prefix P and run class r:
  1. checkcnf.py on P_r<r>_base.cnf (every base clause valid);
  2. checkcnf.py cover on P_r<r>_leaves.json (the leaves cover the class);
  3. for each leaf: its delta (P_r<r>_cube_<path>.delta.cnf; for a leaf a
     worker's log records as closed with no Farkas clause, the leaf's units
     written from the leaf list; for a leaf it records with a pool and a
     clause count, as cubes_sa.py writes, the first that many clauses of
     the pool followed by those units) must pass checkcnf.py delta, and base +
     delta (concatenated here) must be proved unsatisfiable by the
     standalone cadical binary with a DRAT proof that drat-trim verifies.
     The logs are not trusted: a leaf recorded as closed that is not is
     caught when cadical finds base + units satisfiable.
When every step passes, the run class has no face of the question:
CONDITIONAL on the size-encoding assumption of roadmap section 83.2, and
on Lemma 84.A, whose hypothesis |F| < s step 2 checks.

    python3 -I tools/multicolored/certcubes.py P r K s samples DRAT_TRIM [workdir|-] [leaves.json]

leaves.json defaults to P_r<r>_leaves.json; another leaf list (for instance a
copy taken before the tree was refined) can be given instead.

The concatenated CNF and the proof of each leaf go to workdir (default: the
directory of P) and are deleted after the check, whatever its outcome.
"""
import json, os, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))


def run(cmd):
    p = subprocess.run(cmd, capture_output=True, text=True)
    return p.returncode, p.stdout, p.stderr


def main():
    P, r, K, s, samples, drat = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5], sys.argv[6]
    work = sys.argv[7] if len(sys.argv) > 7 and sys.argv[7] != "-" else os.path.dirname(os.path.abspath(P))
    leaves_path = sys.argv[8] if len(sys.argv) > 8 else f"{P}_r{r}_leaves.json"
    spec = json.load(open(leaves_path))
    D, n = spec["D"], spec["n"]
    # the leaf list must be for this run class and question, or the base and
    # the deltas could contradict each other vacuously
    assert (spec["run"], spec["K"], spec["s"]) == (r, K, s), (spec["run"], spec["K"], spec["s"], r, K, s)
    check = [sys.executable, "-I", os.path.join(HERE, "checkcnf.py")]
    out = {"prefix": P, "run": r, "leaves": len(spec["leaves"])}
    base = f"{P}_r{r}_base.cnf"
    _, o, e = run(check + [base, str(D), str(n), str(K), str(s), str(r), samples])
    out["base"] = json.loads(o)["ok"] if o else e[-300:]
    _, o, e = run(check + ["cover", leaves_path])
    out["cover"] = json.loads(o)["ok"] if o else e[-300:]
    with open(base) as f:
        head = f.readline().split()
        base_body = f.read()
    nv, nb = int(head[2]), int(head[3])
    # leaves closed with no Farkas clause, or with a worker's pool, are recorded in the workers' logs
    units_only, pooled, pools = set(), {}, {}
    d = os.path.dirname(os.path.abspath(P))
    stem = os.path.basename(P) + f"_r{r}_closed_w"
    for fn in os.listdir(d):
        if fn.startswith(stem) and fn.endswith(".jsonl"):
            for line in open(os.path.join(d, fn)):
                if line.endswith("\n"):
                    rec = json.loads(line)
                    if rec.get("units_only"):
                        units_only.add(rec["cube"])
                    elif "pool" in rec:
                        pooled[rec["cube"]] = (rec["pool"], rec["pool_clauses"])
    nforb = lambda l: l["nforbidden"] if "nforbidden" in l else len(l["forbidden"])
    leaf_ok, fails = 0, []
    order = sorted(range(len(spec["leaves"])), key=lambda k: -nforb(spec["leaves"][k]))
    for k in order:                             # easiest first, so partial runs certify the most
        leaf = spec["leaves"][k]
        nm = "-".join(map(str, leaf["path"])) or "root"
        dpath = f"{P}_r{r}_cube_{nm}.delta.cnf"
        if not os.path.exists(dpath):
            if nm not in units_only and nm not in pooled:
                fails.append((nm, "not closed"))
                continue
            # the delta is the leaf's units, written from the leaf list (which the
            # cover check verifies), after the pool's clauses for a pooled leaf; it
            # is then checked like any delta
            f = leaf["forbidden"]
            forb = f if isinstance(f, list) else [k for k in range(int(f, 16).bit_length()) if int(f, 16) >> k & 1]
            units = [x + 1 for x in leaf["fixed"]] + [-(x + 1) for x in forb]
            head_cl = []
            if nm not in units_only:
                pool, cnt = pooled[nm]
                if pool not in pools:
                    with open(os.path.join(d, pool)) as fp:
                        pools[pool] = [x for x in fp if x.endswith(" 0\n")]   # a line cut by a crash is not a clause
                if len(pools[pool]) < cnt:
                    fails.append((nm, "pool shorter than recorded", pool))
                    continue
                head_cl = pools[pool][:cnt]
            dpath = os.path.join(work, f"_delta_r{r}_cube_{nm}.cnf")
            with open(dpath, "w") as fo:
                fo.write(f"p cnf {nv} {len(head_cl) + len(units)}\n" + "".join(head_cl)
                         + "".join(f"{u} 0\n" for u in units))
        _, o, e = run(check + ["delta", dpath, str(D), str(n), str(K), str(r), leaves_path, str(k)])
        with open(dpath) as f:
            dh = f.readline().split()
            dbody = f.read()
        if os.path.basename(dpath).startswith("_delta_"):   # a delta written here is removed whatever the outcome
            os.remove(dpath)
        if not (o and json.loads(o)["ok"]):
            fails.append((nm, "delta check", (o or e)[-300:]))
            continue
        if int(dh[2]) != nv:
            fails.append((nm, "variable count differs from the base"))
            continue
        full = os.path.join(work, f"_full_r{r}_cube_{nm}.cnf")
        proof = full + ".drat"
        with open(full, "w") as f:
            f.write(f"p cnf {nv} {nb + int(dh[3])}\n")
            f.write(base_body)
            f.write(dbody)
        code, _, _ = run(["cadical", "-q", full, proof])
        o = run([drat, full, proof])[1] if code == 20 else ""
        for x in (full, proof):
            if os.path.exists(x):
                os.remove(x)
        if code != 20:
            fails.append((nm, f"cadical exit {code}"))
            continue
        if "s VERIFIED" not in o:                # drat-trim prefixes its result line with a carriage return
            fails.append((nm, "drat-trim", o[-200:]))
            continue
        leaf_ok += 1
        print(json.dumps({"leaf": nm, "certified": True}), file=sys.stderr, flush=True)
    out["leaves_certified"] = leaf_ok
    out["failures"] = fails[:10]
    out["ok"] = out["base"] is True and out["cover"] is True and leaf_ok == len(spec["leaves"])
    print(json.dumps(out))


if __name__ == "__main__":
    main()
