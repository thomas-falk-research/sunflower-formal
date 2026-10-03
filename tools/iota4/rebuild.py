"""rebuild.py CHUNK LAST: chunk log = records CHUNK..LAST from the (stopped)
chunk worker's log, then records LAST+1..CHUNK+39 from extra/shard_i.log,
each of which must end DONE exit=20. Writes logs/chunk_XXXXX.log."""
import re, sys
C, L = int(sys.argv[1]), int(sys.argv[2])
base = f"logs/chunk_{C:05d}.log"
lines = open(base).read().splitlines()
recs = {}
for j, l in enumerate(lines):
    m = re.match(r"SHARD (\d+) ", l)
    if m and j + 1 < len(lines) and lines[j + 1].startswith("ACCEPTED"):
        recs[int(m.group(1))] = (l, lines[j + 1])
out = []
for i in range(C, min(C + 40, 11720)):
    if i <= L:
        assert i in recs, f"missing record {i} in stopped chunk log"
        out += list(recs[i])
    else:
        x = open(f"extra/shard_{i}.log").read().splitlines()
        assert x[-1] == "DONE exit=20" and x[0].startswith(f"SHARD {i} ") and x[1].startswith("ACCEPTED"), f"bad extra {i}"
        out += x[:2]
out.append("DONE exit=20")
open(base, "w").write("\n".join(out) + "\n")
print(f"rebuilt {base}: {sum(1 for o in out if o.startswith('SHARD'))} records")
