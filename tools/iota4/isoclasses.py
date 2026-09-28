import glob, sys, itertools
from collections import Counter
import networkx as nx
from networkx.algorithms import isomorphism as iso
sys.path.insert(0, __import__("os").path.dirname(__file__))
from satcheck import load, unwitnessed
fams = load(sys.argv[1])
def graph(F):
    g = nx.Graph()
    for j, S in enumerate(F):
        g.add_node(("m", j), c=1)
        for v in S: g.add_node(("p", v), c=0); g.add_edge(("m", j), ("p", v))
    return g
gs = [graph(F) for F in fams]
from collections import defaultdict
buckets = defaultdict(list)
for k, g in enumerate(gs): buckets[(len(fams[k]), nx.weisfeiler_lehman_graph_hash(g, node_attr="c"))].append(k)
dup = 0
for b in buckets.values():
    for a, c in itertools.combinations(b, 2):
        if iso.GraphMatcher(gs[a], gs[c], node_match=lambda x, y: x["c"] == y["c"]).is_isomorphic(): dup += 1
print("families", len(fams), "WL buckets", len(buckets), "isomorphic pairs", dup)
for F in fams:
    V, bad = unwitnessed(F)
    if len(F) >= 26 or not bad:
        deg = Counter(v for S in F for v in S)
        tau = next(t for t in range(1, 5) if any(all(set(T) & S for S in F) for T in itertools.combinations(V, t)))
        print(len(F), "pts", len(V), "tau", tau, "unwitnessed", len(bad), "by size", dict(Counter(len(b) for b in bad)), "degrees", sorted(deg.values(), reverse=True))
