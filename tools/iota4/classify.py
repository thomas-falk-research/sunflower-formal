import glob, itertools, sys
from collections import Counter
sys.path.insert(0, __import__("os").path.dirname(__file__))
from satcheck import load, unwitnessed
fams = load(sys.argv[1])
def tau(F, V):
    return next(t for t in range(1, 5) if any(all(set(T) & S for S in F) for T in itertools.combinations(V, t)))
rows = []
for F in fams:
    V, B = unwitnessed(F)
    rows.append((len(F), len(V), tau(F, V), B))
def bound(B, g3):   # max |M| under: tau(D)=4 (checked by caller), all traces in B of size 3
    return max(27, min(27, g3) + len(B), 6 + 2 * len(B))
for size in (26, 25):
    R = [r for r in rows if r[0] == size]
    need = 54 - size
    c = Counter()
    for (_, nV, t, B) in R:
        if not B: c["saturated"] += 1; continue
        ms = max(len(b) for b in B); mn = min(len(b) for b in B)
        if mn == 3 and t == 4:
            if bound(B, 26) <= need: c["closed, kernel g3<=26"] += 1
            elif bound(B, 20) <= need: c["closed, needs g3=20"] += 1
            else: c[f"size-3 only, |B|={len(B)} too many"] += 1
        else:
            c[f"has trace of size {mn} (tau {t})"] += 1
    print(size, len(R), dict(c))
