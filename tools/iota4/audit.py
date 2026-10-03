#!/usr/bin/env python3
"""Audit the ledger of the independent iota(4) <= 27 run.

Checks, and fails loudly on any violation:
  1. the frontier file has exactly N shard lines;
  2. every chunk log ends with `DONE exit=20` (the solver's "none found");
  3. every shard index 0..N-1 appears exactly once across all logs;
  4. every shard line says NONE, and no SOLUTION line exists anywhere;
  5. every shard's own ACCEPTED vector has 0 at depth M (= 28).
Prints the per-depth totals of accepted (canonical) nodes, i.e. the number
of isomorphism classes of r-member families below depth 6, summed over
the frontier, plus the depth-6 frontier itself.
"""
import glob, re, sys

logdir, frontier, M = sys.argv[1], sys.argv[2], 28
shards = [l for l in open(frontier) if l.startswith("S ")]
N = len(shards)
seen = {}
totals = [0] * (M + 1)
visited = 0
cpu = 0.0
worst = (0.0, None)
bad = []
for f in sorted(glob.glob(f"{logdir}/chunk_*.log")):
    lines = open(f).read().splitlines()
    if not lines or lines[-1] != "DONE exit=20":
        bad.append(f"{f}: last line {lines[-1] if lines else '<empty>'!r}")
    for i, l in enumerate(lines):
        if l.startswith("SOLUTION"):
            bad.append(f"{f}: SOLUTION line")
        m = re.match(r"SHARD (\d+) k=4 m=28 inter=1 colcap=128: (\w+) visited=(\d+) time=([\d.]+)s", l)
        if not m:
            continue
        idx, verdict = int(m.group(1)), m.group(2)
        if verdict != "NONE":
            bad.append(f"{f}: shard {idx} verdict {verdict}")
        seen[idx] = seen.get(idx, 0) + 1
        visited += int(m.group(3))
        t = float(m.group(4)); cpu += t
        if t > worst[0]:
            worst = (t, idx)
        acc = lines[i + 1].split()
        if acc[0] != "ACCEPTED" or len(acc) != M + 2:
            bad.append(f"{f}: shard {idx} malformed ACCEPTED")
            continue
        vec = list(map(int, acc[1:]))
        if vec[M] != 0:
            bad.append(f"{f}: shard {idx} accepted a depth-{M} node")
        for d, v in enumerate(vec):
            totals[d] += v
missing = [i for i in range(N) if i not in seen]
dup = [i for i, c in seen.items() if c != 1]
extra = [i for i in seen if not (0 <= i < N)]
print(f"frontier shards: {N}")
print(f"shards run: {len(seen)}  missing: {len(missing)}  duplicated: {len(dup)}  out of range: {len(extra)}")
print(f"visited orbit representatives below depth 6: {visited}")
print(f"summed solver time: {cpu:.1f} s   slowest shard: {worst[1]} at {worst[0]:.1f} s")
totals[6] = N
print("isomorphism classes per depth (depth: count), depths 6..28:")
for d in range(6, M + 1):
    print(f"  {d:2d}: {totals[d]}")
deepest = max(d for d in range(M + 1) if totals[d] > 0)
print(f"largest family size reached: {deepest}")
if bad or missing or dup or extra:
    for b in bad[:20]:
        print("FAIL", b)
    print(f"AUDIT FAIL ({len(bad)} problems, {len(missing)} missing)")
    sys.exit(1)
print("AUDIT PASS: no intersecting 3-sunflower-free family of 28 distinct 4-sets")
