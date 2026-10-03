"""Read `[shard] BIG r C mask...` lines (docs/ladder/iota4_replication/
classes_25_27.txt.gz, or isearch2p shard logs); for each family:
re-verify 4-uniform, distinct, intersecting, 3-sunflower-free; then test
trace saturation: every nonempty T within the family's points, |T| <= 3,
has members C1 != C2 with T&C1 == T&C2 == C1&C2."""
import sys, itertools, glob, gzip
def fam_of(line):
    p = line.split(); p = p[p.index("BIG"):]; r, C = int(p[1]), int(p[2])
    F = [frozenset(i for i in range(128) if int(h, 16) >> i & 1) for h in p[3:]]
    assert len(F) == r
    return F
def load(path):
    op = gzip.open if path.endswith(".gz") else open
    return [fam_of(l) for f in sorted(glob.glob(path)) for l in op(f, "rt") if "BIG" in l]
def check_valid(F):
    assert all(len(S) == 4 for S in F) and len(set(F)) == len(F)
    assert all(a & b for a, b in itertools.combinations(F, 2))
    assert not any((a & b) == (a & c) == (b & c) for a, b, c in itertools.combinations(F, 3))
def unwitnessed(F):
    V = sorted(set().union(*F)); pairs = [(a, b, a & b) for a, b in itertools.combinations(F, 2)]
    bad = []
    for t in (1, 2, 3):
        for T in map(frozenset, itertools.combinations(V, t)):
            if not any((T & a) == K and (T & b) == K for a, b, K in pairs): bad.append(tuple(sorted(T)))
    return V, bad
if __name__ == "__main__":
    out = []
    for F in load(sys.argv[1]):
        check_valid(F); V, bad = unwitnessed(F)
        out.append((len(F), len(V), len(bad), "", bad[:6]))
    from collections import Counter
    for size in sorted({o[0] for o in out}, reverse=True):
        rows = [o for o in out if o[0] == size]
        print(f"size {size}: {len(rows)} classes, saturated {sum(o[2] == 0 for o in rows)}, points {dict(Counter(o[1] for o in rows))}")
        print("   unwitnessed-trace counts of non-saturated:", sorted(o[2] for o in rows if o[2]))
    for o in out:
        if o[2] and o[0] >= 26: print("  NONSAT", o)
