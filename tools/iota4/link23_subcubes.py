"""Split cK_cube31.cnf further on the next 5 most frequent variables (ranks 6-10
by the same criterion as cubes.py). Writes cK_cube31_s{j}.cnf, j < 32, covering
every assignment of those variables inside cube 31."""
import sys, collections, itertools
k, W = sys.argv[1], sys.argv[2]
base = open(f"{W}/c{k}.cnf").read().splitlines()
cnt = collections.Counter()
for l in base[1:]:
    for x in l.split()[:-1]:
        v = abs(int(x))
        if v <= 2000: cnt[v] += 1
rank = [v for v, _ in cnt.most_common(10)]
first, nxt = rank[:5], rank[5:10]
cube = open(f"{W}/c{k}_cube31.cnf").read().splitlines()
# sanity: cube 31 fixes the first five to false
assert cube[-5:] == [f"{-v} 0" for v in first], cube[-5:]
hdr = cube[0].split(); nv, nc = int(hdr[2]), int(hdr[3])
body = "\n".join(cube[1:]) + "\n"
for j, signs in enumerate(itertools.product((1, -1), repeat=5)):
    with open(f"{W}/c{k}_cube31_s{j}.cnf", "w") as f:
        f.write(f"p cnf {nv} {nc + 5}\n"); f.write(body)
        for s, v in zip(signs, nxt): f.write(f"{s * v} 0\n")
print(k, "cube31 = not", first, "; split on", nxt)
