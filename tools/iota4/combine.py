"""Combine an emission run (depths 7..10 of shard i) with its sub-shard runs
(depths 11..28) into one SHARD record identical in form to an unsplit run.
Fails unless every sub-shard ran once, every sub-log ends DONE exit=20, and
every sub-shard verdict is NONE."""
import glob, re, sys
i, emit, subfile, pat = int(sys.argv[1]), sys.argv[2], sys.argv[3], sys.argv[4]
M = 28
L = open(emit).read().splitlines()
m = re.match(r"SHARD \d+ k=4 m=28 inter=1 colcap=128: NONE visited=(\d+) time=([\d.]+)s", L[0])
assert m and L[1].startswith("ACCEPTED"), "bad emission log"
vis, t = int(m.group(1)), float(m.group(2))
acc = list(map(int, L[1].split()[1:]))
nsub = sum(1 for l in open(subfile) if l.startswith("S "))
seen = set()
for f in sorted(glob.glob(pat)):
    lines = open(f).read().splitlines()
    assert lines[-1] == "DONE exit=20", f"{f}: {lines[-1]}"
    for j, l in enumerate(lines):
        mm = re.match(r"SHARD (\d+) k=4 m=28 inter=1 colcap=128: (\w+) visited=(\d+) time=([\d.]+)s", l)
        if not mm: continue
        assert mm.group(2) == "NONE", f"{f}: sub-shard {mm.group(1)} {mm.group(2)}"
        k = int(mm.group(1)); assert k not in seen; seen.add(k)
        vis += int(mm.group(3)); t += float(mm.group(4))
        a = list(map(int, lines[j + 1].split()[1:]))
        assert a[10] == 0
        acc = [x + y for x, y in zip(acc, a)]
assert seen == set(range(nsub)), f"sub-shards run {len(seen)} of {nsub}"
assert acc[M] == 0
print(f"SHARD {i} k=4 m=28 inter=1 colcap=128: NONE visited={vis} time={t:.1f}s")
print("ACCEPTED " + " ".join(map(str, acc)))
