#!/usr/bin/env python3
"""Second opinion on a degree-sequence cube by mixed-integer programming
(SCIP via OR-Tools pywraplp): LP relaxation plus branch-and-bound, a
different engine from CP-SAT's clause learning.  Same constraints as
cube10.py, no symmetry breaking.  Usage: cube10_mip.py <parts> [seconds]"""
import sys, itertools, time
from ortools.linear_solver import pywraplp
parts=[int(x) for x in sys.argv[1].split(',')] if sys.argv[1]!='0' else []
secs=int(sys.argv[2]) if len(sys.argv)>2 else 3600
n=10; D=9; c=3; T=28
degs=[D-x for x in parts+[0]*(n-len(parts))]
cands=list(itertools.combinations(range(n),3))
s=pywraplp.Solver.CreateSolver("SCIP"); assert s
x={t:s.BoolVar(str(t)) for t in cands}
for v in range(n): s.Add(sum(x[t] for t in cands if v in t)==degs[v])
for p in itertools.combinations(range(n),2): s.Add(sum(x[t] for t in cands if p[0] in t and p[1] in t)<=c)
S=[set(t) for t in cands]; cnt=0
for i in range(len(cands)):
    for j in range(i+1,len(cands)):
        if S[i]&S[j]: continue
        u=S[i]|S[j]
        for k in range(j+1,len(cands)):
            if u&S[k]: continue
            s.Add(x[cands[i]]+x[cands[j]]+x[cands[k]]<=2); cnt+=1
s.Add(sum(x.values())==T)
K=56
def swap(t,v):
    return tuple(sorted((v+1 if y==v else v if y==v+1 else y) for y in t))
for v in range(n-1):
    if degs[v]==degs[v+1]:
        pos=[t for t in cands if (v in t)!=(v+1 in t)][:K]
        s.Add(sum((2.0**(K-1-i))*x[t] for i,t in enumerate(pos)) >= sum((2.0**(K-1-i))*x[swap(t,v)] for i,t in enumerate(pos)))
B=16
for i,t in enumerate(cands):
    s.Add(sum(x[cands[j]] for j in range(len(cands)) if not (S[i]&S[j])) <= B + T*(1-x[t]))
s.SetTimeLimit(secs*1000)
print(f"cube {parts} degs={degs} constraints={s.NumConstraints()} solver=SCIP",flush=True)
t0=time.time(); st=s.Solve()
names={pywraplp.Solver.OPTIMAL:"FEASIBLE",pywraplp.Solver.FEASIBLE:"FEASIBLE",pywraplp.Solver.INFEASIBLE:"INFEASIBLE",pywraplp.Solver.NOT_SOLVED:"UNKNOWN",pywraplp.Solver.ABNORMAL:"ABNORMAL"}
print(f"cube {parts} SCIP {names.get(st,st)} time {time.time()-t0:.1f}s",flush=True)
if st in (pywraplp.Solver.OPTIMAL,pywraplp.Solver.FEASIBLE):
    fam=[t for t in cands if x[t].solution_value()>0.5]; print("WITNESS",fam,flush=True)
