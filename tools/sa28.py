#!/usr/bin/env python3
"""Simulated-annealing / tabu search for a 3-uniform family on n points with
nu<=2, deg<=D, pair-deg<=c, maximising size (target T). Pure heuristic; a hit is
re-verified by verify().  Usage: sa28.py n [D c T seed iters]"""
import sys, random, itertools, time
n=int(sys.argv[1]); D=int(sys.argv[2]) if len(sys.argv)>2 else 9
c=int(sys.argv[3]) if len(sys.argv)>3 else 3; T=int(sys.argv[4]) if len(sys.argv)>4 else 28
seed=int(sys.argv[5]) if len(sys.argv)>5 else 1; iters=int(sys.argv[6]) if len(sys.argv)>6 else 10**7
random.seed(seed)
tri=list(itertools.combinations(range(n),3)); mask=[sum(1<<i for i in t) for t in tri]
N=len(tri)
disj=[[j for j in range(N) if mask[i]&mask[j]==0] for i in range(N)]
def verify(F):
    S=[set(tri[i]) for i in F]
    for v in range(n): assert sum(v in s for s in S)<=D
    for p in itertools.combinations(range(n),2): assert sum(p[0] in s and p[1] in s for s in S)<=c
    for a,b,cc in itertools.combinations(range(len(S)),3):
        assert S[a]&S[b] or S[a]&S[cc] or S[b]&S[cc]
    return True
cur=set(); deg=[0]*n; pd={}
def can_add(i):
    t=tri[i]
    for v in t:
        if deg[v]>=D: return False
    for p in itertools.combinations(t,2):
        if pd.get(p,0)>=c: return False
    # nu: is there a disjoint pair in cur both disjoint from t?
    dl=[j for j in disj[i] if j in cur]
    for a in range(len(dl)):
        for b in range(a+1,len(dl)):
            if mask[dl[a]]&mask[dl[b]]==0: return False
    return True
def add(i):
    cur.add(i); t=tri[i]
    for v in t: deg[v]+=1
    for p in itertools.combinations(t,2): pd[p]=pd.get(p,0)+1
def rem(i):
    cur.discard(i); t=tri[i]
    for v in t: deg[v]-=1
    for p in itertools.combinations(t,2): pd[p]-=1
best=0; t0=time.time(); order=list(range(N))
for it in range(iters):
    random.shuffle(order)
    for i in order:
        if i not in cur and can_add(i): add(i)
    if len(cur)>best:
        best=len(cur); print(f"it {it} size {best} t={time.time()-t0:.0f}s", flush=True)
        if best>=T:
            F=sorted(cur); verify(F); print("WITNESS", [tri[i] for i in F], flush=True); sys.exit(0)
    # perturb: remove k random members
    k=random.randint(1,4)
    for i in random.sample(sorted(cur),min(k,len(cur))): rem(i)
print("done best",best)
