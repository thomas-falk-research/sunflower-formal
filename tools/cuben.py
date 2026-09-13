#!/usr/bin/env python3
"""Degree-sequence cube of the 28-member question on n points (tools/cube10.py
generalised).  Deficiencies 9 - d_v (sorted) sum to 9n - 84.
Usage: cuben.py n <parts> [workers] [timelimit] [K] [B]"""
import sys, itertools, time
from ortools.sat.python import cp_model
n=int(sys.argv[1]); parts=[int(x) for x in sys.argv[2].split(',')] if sys.argv[2]!='0' else []
workers=int(sys.argv[3]) if len(sys.argv)>3 else 1
tl=float(sys.argv[4]) if len(sys.argv)>4 else 0
K=int(sys.argv[5]) if len(sys.argv)>5 else 62
B=int(sys.argv[6]) if len(sys.argv)>6 else 16
D=9; c=3; T=28
degs=[D-x for x in parts+[0]*(n-len(parts))]
assert sum(degs)==3*T and all(1<=d<=9 for d in degs), degs
pts=range(n); cands=list(itertools.combinations(pts,3))
m=cp_model.CpModel(); x={t:m.NewBoolVar(str(t)) for t in cands}
for v in pts: m.Add(sum(x[t] for t in cands if v in t)==degs[v])
for p in itertools.combinations(pts,2): m.Add(sum(x[t] for t in cands if p[0] in t and p[1] in t)<=c)
S=[set(t) for t in cands]; cnt=0
for i in range(len(cands)):
    for j in range(i+1,len(cands)):
        if S[i]&S[j]: continue
        u=S[i]|S[j]
        for k in range(j+1,len(cands)):
            if u&S[k]: continue
            m.AddBoolOr([x[cands[i]].Not(),x[cands[j]].Not(),x[cands[k]].Not()]); cnt+=1
m.Add(sum(x.values())==T)
def swap(t,v): return tuple(sorted((v+1 if y==v else v if y==v+1 else y) for y in t))
for v in range(n-1):
    if degs[v]==degs[v+1]:
        pos=[t for t in cands if (v in t)!=(v+1 in t)][:K]
        m.Add(sum((1<<(K-1-i))*x[t] for i,t in enumerate(pos)) >= sum((1<<(K-1-i))*x[swap(t,v)] for i,t in enumerate(pos)))
if B:
    for i,t in enumerate(cands):
        m.Add(sum(x[cands[j]] for j in range(len(cands)) if not (S[i]&S[j])) <= B + T*(1-x[t]))
print(f"n={n} cube {parts} degs={degs} cands={len(cands)} ternary={cnt} K={K} B={B}",flush=True)
s=cp_model.CpSolver(); s.parameters.num_workers=workers
if tl: s.parameters.max_time_in_seconds=tl
t0=time.time(); st=s.Solve(m)
print(f"n={n} cube {parts} status {s.StatusName(st)} time {time.time()-t0:.1f}s",flush=True)
if st in (cp_model.OPTIMAL,cp_model.FEASIBLE):
    fam=[t for t in cands if s.Value(x[t])]
    for a,b,cc in itertools.combinations(fam,3): assert set(a)&set(b) or set(a)&set(cc) or set(b)&set(cc)
    print("WITNESS",fam,flush=True)
