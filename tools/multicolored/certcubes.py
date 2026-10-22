#!/usr/bin/env python3
"""Certify one run class's cubes.py result.

docs/roadmap.md section 84. For prefix P and run class r:
  1. checkcnf.py on P_r<r>_base.cnf (every base clause valid);
  2. checkcnf.py cover on P_r<r>_leaves.json (the leaves cover the class);
  3. for each leaf: P_r<r>_cube_<path>.delta.cnf must exist, pass checkcnf.py
     delta, and base + delta (concatenated here) must be proved
     unsatisfiable by the standalone cadical binary with a DRAT proof that
     drat-trim verifies.
The class has no face of the question when every step passes.

    python3 -I tools/multicolored/certcubes.py P r K s samples DRAT_TRIM [workdir]

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
    work = sys.argv[7] if len(sys.argv) > 7 else os.path.dirname(os.path.abspath(P))
    leaves_path = f"{P}_r{r}_leaves.json"
    spec = json.load(open(leaves_path))
    D, n = spec["D"], spec["n"]
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
    leaf_ok, fails = 0, []
    for k, leaf in enumerate(spec["leaves"]):
        nm = "-".join(map(str, leaf["path"])) or "root"
        dpath = f"{P}_r{r}_cube_{nm}.delta.cnf"
        if not os.path.exists(dpath):
            fails.append((nm, "no delta file"))
            continue
        _, o, e = run(check + ["delta", dpath, str(D), str(n), str(K), str(r), leaves_path, str(k)])
        if not (o and json.loads(o)["ok"]):
            fails.append((nm, "delta check", (o or e)[-300:]))
            continue
        with open(dpath) as f:
            dh = f.readline().split()
            dbody = f.read()
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
        for x in (full, proof):                 # proofs can be large: never keep them
            if os.path.exists(x):
                os.remove(x)
        if code != 20:
            fails.append((nm, f"cadical exit {code}"))
            continue
        if "s VERIFIED" not in o:                # drat-trim prefixes its result line with a carriage return
            fails.append((nm, "drat-trim", o[-200:]))
            continue
        leaf_ok += 1
    out["leaves_certified"] = leaf_ok
    out["failures"] = fails[:10]
    out["ok"] = out["base"] is True and out["cover"] is True and leaf_ok == len(spec["leaves"])
    print(json.dumps(out))


if __name__ == "__main__":
    main()
