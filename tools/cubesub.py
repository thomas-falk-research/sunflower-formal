#!/usr/bin/env python3
"""Sub-cube of a degree-sequence cube: additionally fix the pair-degree
profile of point 0 (the lowest-degree point).  With degrees sorted
non-decreasing, point 0 has the minimum degree d0; its pair degrees
p_v = |{members containing 0 and v}| satisfy 0 <= p_v <= 3 and sum 2*d0.
Inside each block of points of equal degree (excluding 0) the p_v are
sorted non-increasing, WLOG by the block symmetry; the lex-leader
constraints are then kept only for transpositions (v v+1) with equal
degree AND equal p, which generate the stabiliser of the profile, so the
combination is sound.

Usage: cubesub.py n <parts> <profile p_1,...,p_{n-1}> [workers] [timelimit] [K] [B]
       cubesub.py n <parts> --list       # print every profile (sub-cube) of the cube
"""
import sys, itertools, time

n=int(sys.argv[1]); parts=[int(x) for x in sys.argv[2].split(',')] if sys.argv[2]!='0' else []
D=9; c=3; T=28
degs=[D-x for x in parts+[0]*(n-len(parts))]
assert sum(degs)==3*T and all(1<=d<=9 for d in degs), degs
d0=degs[0]; S2=2*d0
# blocks of equal degree among points 1..n-1
blocks=[]; v=1
while v<n:
    w=v
    while w<n and degs[w]==degs[v]: w+=1
    blocks.append(list(range(v,w))); v=w

def sorted_vectors(k, total_max):
    # non-increasing vectors of length k with entries in 0..3
    def rec(k, mx, pre):
        if k==0: yield pre; return
        for x in range(min(mx,3),-1,-1): yield from rec(k-1,x,pre+(x,))
    return list(rec(k,3,()))

def profiles():
    per=[sorted_vectors(len(b),S2) for b in blocks]
    for combo in itertools.product(*per):
        flat=[x for vec in combo for x in vec]
        if sum(flat)==S2: yield flat

if sys.argv[3]=='--list':
    P=list(profiles()); print(len(P), file=sys.stderr)
    for p in P: print(','.join(map(str,p)))
    sys.exit(0)

from ortools.sat.python import cp_model
prof=[int(x) for x in sys.argv[3].split(',')]; assert len(prof)==n-1 and sum(prof)==S2
workers=int(sys.argv[4]) if len(sys.argv)>4 else 1
tl=float(sys.argv[5]) if len(sys.argv)>5 else 0
K=int(sys.argv[6]) if len(sys.argv)>6 else 62
B=int(sys.argv[7]) if len(sys.argv)>7 else 16
pts=range(n); cands=list(itertools.combinations(pts,3))
m=cp_model.CpModel(); x={t:m.NewBoolVar(str(t)) for t in cands}
for v in pts: m.Add(sum(x[t] for t in cands if v in t)==degs[v])
for p in itertools.combinations(pts,2): m.Add(sum(x[t] for t in cands if p[0] in t and p[1] in t)<=c)
for v in range(1,n): m.Add(sum(x[t] for t in cands if 0 in t and v in t)==prof[v-1])
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
nlex=0
for v in range(1,n-1):
    if degs[v]==degs[v+1] and prof[v-1]==prof[v]:
        pos=[t for t in cands if (v in t)!=(v+1 in t)][:K]
        m.Add(sum((1<<(K-1-i))*x[t] for i,t in enumerate(pos)) >= sum((1<<(K-1-i))*x[swap(t,v)] for i,t in enumerate(pos))); nlex+=1
if B:
    for i,t in enumerate(cands):
        m.Add(sum(x[cands[j]] for j in range(len(cands)) if not (S[i]&S[j])) <= B + T*(1-x[t]))
print(f"n={n} cube {parts} profile {prof} degs={degs} lex={nlex} K={K} B={B}",flush=True)
s=cp_model.CpSolver(); s.parameters.num_workers=workers
if tl: s.parameters.max_time_in_seconds=tl
t0=time.time(); st=s.Solve(m)
print(f"n={n} cube {parts} profile {prof} status {s.StatusName(st)} time {time.time()-t0:.1f}s",flush=True)
if st in (cp_model.OPTIMAL,cp_model.FEASIBLE):
    fam=[t for t in cands if s.Value(x[t])]
    for a,b,cc in itertools.combinations(fam,3): assert set(a)&set(b) or set(a)&set(cc) or set(b)&set(cc)
    print("WITNESS",fam,flush=True)
