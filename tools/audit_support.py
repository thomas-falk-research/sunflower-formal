#!/usr/bin/env python3
"""Audit the support ladders (docs/roadmap.md section 56.11): for n = 13,
14, 15 every cube in rstar_3_3_support<n>.cubes.txt must have an
INFEASIBLE row in rstar_3_3_support<n>.tsv with K = 62 and B = 10, no row
may carry another verdict or a witness, and the cube list must equal what
tools/typeprof.py 7 2 <n> enumerates (regenerated here).  Exit 0 iff so."""
import subprocess, sys
root = sys.argv[1] if len(sys.argv) > 1 else "."
ok = True
for n in (15, 14, 13):
    cubes = [l.strip() for l in open(f"{root}/docs/ladder/rstar_3_3_support{n}.cubes.txt") if l.strip()]
    prof = subprocess.run([sys.executable, f"{root}/tools/typeprof.py", "7", "2", str(n)], capture_output=True, text=True).stdout
    regen = set()
    for line in prof.splitlines():
        if not line.startswith("("): continue
        p = eval(line); degs = []
        for d, k in zip(range(2, 10), p): degs += [d] * k
        parts = sorted([9 - d for d in degs if 9 - d > 0], reverse=True)
        regen.add(",".join(map(str, parts)))
    rows = [l.rstrip("\n").split("\t") for l in open(f"{root}/docs/ladder/rstar_3_3_support{n}.tsv") if l.strip() and not l.startswith("#")]
    bad = [r for r in rows if r[4] != "INFEASIBLE" or r[2] != "62" or r[3] != "10" or (len(r) > 6 and r[6].strip())]
    closed = {r[0] for r in rows if r[4] == "INFEASIBLE"}
    missing = set(cubes) - closed
    print(f"n={n}: cubes {len(cubes)} (regenerated {len(regen)}, equal={set(cubes)==regen}), INFEASIBLE rows {len(closed)}, missing {len(missing)}, bad rows {len(bad)}")
    ok = ok and set(cubes) == regen and not missing and not bad
sys.exit(0 if ok else 1)
