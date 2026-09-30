"""Split cK.cnf into 2^k cubes on the k variables occurring in the most clauses
among the unary-slot 'first slot' variables (1..ntypes range is not known here,
so pick the k most frequent variables among the first 2000 ids).  Writes
cK_cube_j.cnf = base + k unit clauses; the 2^k sign patterns cover every
assignment, so all-UNSAT refutes the base formula."""
import sys, collections, itertools
k_cls, kk = sys.argv[1], int(sys.argv[2])
W = sys.argv[3]
lines = open(f"{W}/c{k_cls}.cnf").read().splitlines()
hdr = lines[0].split(); nv, nc = int(hdr[2]), int(hdr[3])
cnt = collections.Counter()
for l in lines[1:]:
    for x in l.split()[:-1]:
        v = abs(int(x))
        if v <= 2000: cnt[v] += 1
split = [v for v, _ in cnt.most_common(kk)]
body = "\n".join(lines[1:]) + "\n"
for j, signs in enumerate(itertools.product((1, -1), repeat=kk)):
    with open(f"{W}/c{k_cls}_cube{j}.cnf", "w") as f:
        f.write(f"p cnf {nv} {nc + kk}\n"); f.write(body)
        for s, v in zip(signs, split): f.write(f"{s * v} 0\n")
print(k_cls, "split vars", split, "cubes", 2 ** kk)
