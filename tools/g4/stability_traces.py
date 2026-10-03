import itertools
X = [(0,1,2),(3,4,5),(6,7,8)]
A = [frozenset(a) | frozenset(b) for i, j in [(0,1),(0,2),(1,2)] for a in itertools.combinations(X[i], 2) for b in itertools.combinations(X[j], 2)]
assert len(A) == 27 and len(set(A)) == 27
bad = []; n = 0
for t in (1, 2, 3):
    for tau in map(frozenset, itertools.combinations(range(9), t)):
        n += 1
        # S with S & P = tau and outer points fresh: S & C = tau & C for C in A
        w = [(C1, C2) for C1, C2 in itertools.combinations(A, 2) if (tau & C1) == (tau & C2) == (C1 & C2)]
        if not w: bad.append(tau)
print("traces checked", n, "compatible (no witness)", bad)
