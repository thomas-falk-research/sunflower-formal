#!/usr/bin/env python3
"""One degree-sequence cube of the ten-point question.

Is there a 3-uniform family on 10 points with 28 members, no three pairwise
disjoint members, point degree <= 9, pair degree <= 3?  Sum of degrees is 84,
so the deficiencies 9 - d_v sum to 6; sorting points by degree, the cube is a
partition of 6.  Usage: cube10.py <parts comma-separated> [workers] [timelimit]
e.g. cube10.py 3,2,1  -> degrees 6,7,8,9,9,9,9,9,9,9
Symmetry left: permutations inside equal-degree blocks (not broken).
"""
import sys, itertools, time
from ortools.sat.python import cp_model

parts=[int(x) for x in sys.argv[1].split(',')] if sys.argv[1]!='0' else []
workers=int(sys.argv[2]) if len(sys.argv)>2 else 1
tl=float(sys.argv[3]) if len(sys.argv)>3 else 0
n=10; D=9; c=3; T=28
defic=parts+[0]*(n-len(parts))
degs=[D-x for x in defic]
assert sum(degs)==3*T, degs
pts=range(n)
cands=list(itertools.combinations(pts,3))
m=cp_model.CpModel(); x={t:m.NewBoolVar(str(t)) for t in cands}
for v in pts: m.Add(sum(x[t] for t in cands if v in t)==degs[v])
for p in itertools.combinations(pts,2): m.Add(sum(x[t] for t in cands if p[0] in t and p[1] in t)<=c)
S=[set(t) for t in cands]
cnt=0
for i in range(len(cands)):
    for j in range(i+1,len(cands)):
        if S[i]&S[j]: continue
        u=S[i]|S[j]
        for k in range(j+1,len(cands)):
            if u&S[k]: continue
            m.AddBoolOr([x[cands[i]].Not(),x[cands[j]].Not(),x[cands[k]].Not()]); cnt+=1
m.Add(sum(x.values())==T)
# symmetry inside equal-degree blocks: for the transposition (v v+1) of two
# points of equal degree, impose X >=lex sigma(X) on the global candidate
# order, truncated to the first K positions where t != sigma(t).  The
# lex-greatest member of every orbit satisfies all of these at once, and a
# prefix of a lex constraint is implied by it, so this is sound.
K=int(sys.argv[4]) if len(sys.argv)>4 else 56
def swap(t,v):
    return tuple(sorted((v+1 if y==v else v if y==v+1 else y) for y in t))
for v in range(n-1):
    if degs[v]==degs[v+1]:
        pos=[t for t in cands if (v in t)!=(v+1 in t)][:K]
        m.Add(sum((1<<(K-1-i))*x[t] for i,t in enumerate(pos)) >= sum((1<<(K-1-i))*x[swap(t,v)] for i,t in enumerate(pos)))
# Optional redundant cut: the members disjoint from any member form an
# intersecting family under the caps, which the kernel bounds by 16
# (TauThree.tau_three_bound for tau = 3; TwoCoverSharp for tau = 2; a star
# for tau = 1).  B = 16 is therefore a proved consequence; B = 10 would rest
# on Frankl's tau = 3 value (cited, not proved).
B=int(sys.argv[5]) if len(sys.argv)>5 else 0
if B:
    for i,t in enumerate(cands):
        m.Add(sum(x[cands[j]] for j in range(len(cands)) if not (S[i]&S[j])) <= B + T*(1-x[t]))
print(f"cube {parts} degs={degs} cands={len(cands)} ternary={cnt} K={K} B={B}",flush=True)
s=cp_model.CpSolver(); s.parameters.num_workers=workers
if tl: s.parameters.max_time_in_seconds=tl
t0=time.time(); st=s.Solve(m)
print(f"cube {parts} status {s.StatusName(st)} time {time.time()-t0:.1f}s",flush=True)
if st in (cp_model.OPTIMAL,cp_model.FEASIBLE):
    fam=[t for t in cands if s.Value(x[t])]; print("WITNESS",fam,flush=True)
