"""Independent oracle: counts isomorphism classes of k-uniform, intersecting,
3-sunflower-free families of distinct sets, per size, with NO nauty:
extension of every class representative by every candidate row, then
deduplication by invariant bucketing + networkx VF2 isomorphism."""
import sys, itertools, networkx as nx
from networkx.algorithms import isomorphism as iso

k, depth, inter = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])

def valid_new(F, S):
    if S in F: return False
    for A in F:
        if inter and not (A & S): return False
    for A, B in itertools.combinations(F, 2):
        ab = A & B
        if ab == (A & S) and ab == (B & S): return False
    return True

def graph(F):
    G = nx.Graph()
    for i, A in enumerate(F):
        G.add_node(('r', i), side=0)
        for x in A:
            G.add_node(('c', x), side=1); G.add_edge(('r', i), ('c', x))
    return G

def invariant(F):
    deg = {}
    for A in F:
        for x in A: deg[x] = deg.get(x, 0) + 1
    rows = sorted(tuple(sorted(deg[x] for x in A)) for A in F)
    inter_sizes = sorted(len(A & B) for A, B in itertools.combinations(F, 2))
    return (tuple(sorted(deg.values())), tuple(rows), tuple(inter_sizes))

nm = iso.categorical_node_match('side', None)
level = [[]]
print(0, 1)
for d in range(1, depth + 1):
    buckets = {}
    count = 0
    for F in level:
        pts = sorted(set().union(*F)) if F else []
        fresh = (max(pts) + 1) if pts else 0
        cands = set()
        for s in range(0, k + 1):
            for comb in itertools.combinations(pts, s):
                S = frozenset(comb) | frozenset(range(fresh, fresh + k - s))
                cands.add(S)
        for S in cands:
            if not valid_new(F, S): continue
            G2 = F + [S]
            key = invariant(G2)
            lst = buckets.setdefault(key, [])
            g2 = graph(G2)
            if any(nx.is_isomorphic(g2, h, node_match=nm) for _, h in lst): continue
            lst.append((G2, g2)); count += 1
    level = [F for lst in buckets.values() for F, _ in lst]
    print(d, count, flush=True)
