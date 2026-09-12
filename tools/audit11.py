#!/usr/bin/env python3
"""Audit the eleven-point ladder: every cube in rstar_3_3_11.cubes.txt must
be closed, either flat (an INFEASIBLE row in rstar_3_3_11.tsv) or by
sub-cubes (an INFEASIBLE row in rstar_3_3_11.sub.tsv for every profile
that tools/cubesub.py 11 <cube> --list enumerates, and no other verdict
anywhere).  Exit status 0 iff the case is closed."""
import subprocess, sys, itertools, collections
root = sys.argv[1] if len(sys.argv) > 1 else "."
def rows(fn):
    return [l.rstrip("\n").split("\t") for l in open(fn) if l.strip() and not l.startswith("#")]
cubes = [l.strip() for l in open(f"{root}/docs/ladder/rstar_3_3_11.cubes.txt") if l.strip() and not l.startswith("#")]
# independent regeneration of the cube list: partitions of 15, <= 11 parts, parts <= 8
def parts(n, mx, k):
    if n == 0: yield (); return
    if k == 0: return
    for p in range(min(n, mx), 0, -1):
        for rest in parts(n - p, p, k - 1): yield (p,) + rest
gen = sorted(",".join(map(str, p)) for p in parts(15, 8, 11))
assert sorted(cubes) == gen and len(cubes) == 139, (len(cubes), len(gen))
flat = rows(f"{root}/docs/ladder/rstar_3_3_11.tsv")
sub = rows(f"{root}/docs/ladder/rstar_3_3_11.sub.tsv")
bad = [r for r in flat + sub if r[4] not in ("INFEASIBLE", "UNKNOWN")]
assert not bad, bad[:5]
assert all(len(r) >= 6 and r[2] == "62" and r[3] == "16" for r in flat + sub)
closed_flat = {r[0] for r in flat if r[4] == "INFEASIBLE"}
subdone = collections.defaultdict(set)
for r in sub:
    if r[4] == "INFEASIBLE": subdone[r[0]].add(r[1])
open_cubes = []
for c in cubes:
    if c in closed_flat: continue
    prof = subprocess.run([sys.executable, f"{root}/tools/cubesub.py", "11", c, "--list"], capture_output=True, text=True).stdout.split()
    prof_set = set(prof); assert len(prof_set) == len(prof)
    if prof_set <= subdone[c]: continue
    open_cubes.append((c, len(prof_set - subdone[c]), len(prof_set)))
n_sub = sum(1 for c in cubes if c not in closed_flat and c not in open_cubes)
print(f"cubes {len(cubes)}: closed flat {len(closed_flat)}, closed by sub-cubes {n_sub}, open {len(open_cubes)}")
for c in open_cubes: print("OPEN", c)
print("witness rows:", sum(1 for r in flat + sub if len(r) > 6 and r[6].strip()))
sys.exit(1 if open_cubes else 0)
