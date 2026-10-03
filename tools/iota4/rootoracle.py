"""nauty-free oracle for rooted families: b-sets on [n] containing the root
R = {0..b-1}, every member meets R, no 3-sunflower; classes up to point
permutations fixing R setwise (root marked as its own row colour)."""
import sys, itertools, networkx as nx
from networkx.algorithms import isomorphism as iso
b, n = int(sys.argv[1]), int(sys.argv[2])
R = frozenset(range(b))
cands = [frozenset(c) for c in itertools.combinations(range(n), b) if set(c) & R and frozenset(c) != R]
def ok(F, S):
    for A, B in itertools.combinations(F, 2):
        if (A & B) == (A & S) == (B & S): return False
    return True
def graph(F):
    G = nx.Graph()
    for i, A in enumerate(F):
        G.add_node(("r", i), c=2 if A == R else 0)
        for x in A: G.add_node(("p", x), c=1); G.add_edge(("r", i), ("p", x))
    return G
nm = iso.categorical_node_match("c", None)
level = [[R]]; counts = [1]
while level:
    nxt = {}
    for F in level:
        for S in cands:
            if S in F or not ok(F, S): continue
            G2 = F + [S]
            key = (tuple(sorted(sum(1 for A in G2 if x in A) for x in range(n))), tuple(sorted(len(A & B) for A, B in itertools.combinations(G2, 2))))
            g2 = graph(G2); lst = nxt.setdefault(key, [])
            if any(nx.is_isomorphic(g2, h, node_match=nm) for _, h in lst): continue
            lst.append((G2, g2))
    level = [F for l in nxt.values() for F, _ in l]
    if level: counts.append(len(level))
print("sizes 1..", len(counts), ":", counts)
