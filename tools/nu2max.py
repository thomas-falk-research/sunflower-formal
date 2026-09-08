#!/usr/bin/env python3
"""Exact maximum of |F| for 3-uniform F on n points with:
   no three pairwise disjoint members (nu <= 2), point degree <= D, pair degree <= c.
A maximal matching {A,B} with A={0,1,2}, B={3,4,5} is forced in (WLOG when nu=2,
and nu<=1 families are tiny: <= 3*D members? no -- intersecting families are bounded
separately, see notes). Every member meets A u B.
Symmetry breaking: degree sequences sorted inside A, inside B, A>=B lex, outside sorted.
Usage: nu2max.py n D c [target] [threads] [timelimit]
"""
import sys, itertools, time
from ortools.sat.python import cp_model

n = int(sys.argv[1]); D = int(sys.argv[2]); c = int(sys.argv[3])
target = int(sys.argv[4]) if len(sys.argv) > 4 else 0
threads = int(sys.argv[5]) if len(sys.argv) > 5 else 4
tl = float(sys.argv[6]) if len(sys.argv) > 6 else 0

pts = list(range(n))
cover = set(range(6))
cands = [t for t in itertools.combinations(pts, 3) if set(t) & cover]
m = cp_model.CpModel()
x = {t: m.NewBoolVar(str(t)) for t in cands}
m.Add(x[(0,1,2)] == 1); m.Add(x[(3,4,5)] == 1)
deg = {}
for v in pts:
    deg[v] = sum(x[t] for t in cands if v in t)
    m.Add(deg[v] <= D)
for p in itertools.combinations(pts, 2):
    m.Add(sum(x[t] for t in cands if p[0] in t and p[1] in t) <= c)
# no three pairwise disjoint
cnt = 0
for i, s in enumerate(cands):
    ss = set(s)
    for j in range(i+1, len(cands)):
        t = cands[j]
        if ss & set(t): continue
        st = ss | set(t)
        for k in range(j+1, len(cands)):
            u = cands[k]
            if st & set(u): continue
            m.AddBoolOr([x[s].Not(), x[t].Not(), x[u].Not()]); cnt += 1
# symmetry breaking on degrees
for (a, b) in [(0,1),(1,2),(3,4),(4,5)]:
    m.Add(deg[a] >= deg[b])
for a, b in zip(range(6, n-1), range(7, n)):
    m.Add(deg[a] >= deg[b])
# A >= B lexicographically on degree triples: encode with big weights
W = D + 1
m.Add(deg[0]*W*W + deg[1]*W + deg[2] >= deg[3]*W*W + deg[4]*W + deg[5])
total = sum(x.values())
if target:
    m.Add(total >= target)
else:
    m.Maximize(total)
print(f"n={n} D={D} c={c} cands={len(cands)} disjoint-triple clauses={cnt}", flush=True)
solver = cp_model.CpSolver()
solver.parameters.num_workers = threads
if tl: solver.parameters.max_time_in_seconds = tl
solver.parameters.log_search_progress = False
t0 = time.time()
st = solver.Solve(m)
print("status", solver.StatusName(st), "time %.1fs" % (time.time()-t0), flush=True)
if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
    fam = [t for t in cands if solver.Value(x[t])]
    print("size", len(fam), "bound", solver.BestObjectiveBound() if not target else "-")
    print("family", fam)
    dg = [sum(v in t for t in fam) for v in pts]
    print("degrees", dg)
