"""Second opinion (SCIP via pywraplp, a MIP, different engine) on the type
relaxation: for EVERY degree profile (n_2..n_9) with sum n_d = n and
sum d n_d = 84, n in [NLO..42], decide feasibility of the member-type /
pair-class system with s_E <= 7, pair counts <= n_a n_b, and Kruskal-Katona
shadows.  With n fixed the products are constants, so the system is a MIP.
Prints the number of profiles per n and any feasible one."""
import itertools, sys
from math import comb
from ortools.linear_solver import pywraplp
NLO=int(sys.argv[1]) if len(sys.argv)>1 else 16
SMAX=7; LO=2
types=[]
for T in itertools.combinations_with_replacement(range(LO,10),3):
    D=sum(9-d for d in T)
    if D>SMAX: continue
    for E in itertools.product(range(1,4),repeat=3):
        if D+sum(e-1 for e in E)<=SMAX: types.append((T,E))
pairkeys=[(a,b) for a in range(LO,10) for b in range(a,10)]
def pairs_of(T,E):
    idx=[(0,1),(0,2),(1,2)]
    return [((min(T[i],T[j]),max(T[i],T[j])),E[k]) for k,(i,j) in enumerate(idx)]
def shadow(mm):
    if mm==0: return 0
    tot=0; k=3
    while mm>0 and k>=1:
        a=k
        while comb(a+1,k)<=mm: a+=1
        tot+=comb(a,k-1); mm-=comb(a,k); k-=1
    return tot
def feasible(prof):  # prof: dict d->n_d
    s=pywraplp.Solver.CreateSolver("SCIP")
    t={k:s.IntVar(0,28,str(k)) for k in types}
    q={(pk,e):s.IntVar(0,84,f"q{pk}{e}") for pk in pairkeys for e in (1,2,3)}
    s.Add(sum(t.values())==28)
    for d in range(LO,10): s.Add(sum(t[k]*k[0].count(d) for k in types)==d*prof.get(d,0))
    for pk in pairkeys:
        for e in (1,2,3):
            s.Add(sum(t[k]*sum(1 for pp in pairs_of(*k) if pp==(pk,e)) for k in types)==e*q[(pk,e)])
    for (a,b) in pairkeys:
        tot=sum(q[((a,b),e)] for e in (1,2,3))
        cap=prof.get(a,0)*prof.get(b,0) if a<b else prof.get(a,0)*(prof.get(a,0)-1)//2
        s.Add(tot<=cap)
    # KK: m_e members with all pairs >= e need >= shadow(m_e) pairs of degree >= e; encode by enumerating m_e? use big table via binary choice:
    for e in (2,3):
        me=sum(t[k] for k in types if min(k[1])>=e); pe=sum(q[(pk,f)] for pk in pairkeys for f in (1,2,3) if f>=e)
        # shadow is nondecreasing; piecewise: for each threshold m, (me>=m) -> pe>=shadow(m); linearize with indicator y_m
        for mm in range(1,29):
            y=s.BoolVar(f"y{e}{mm}")  # y=1 if me>=mm
            s.Add(me-mm+1<=28*y); s.Add(pe>=shadow(mm)*y)
    s.Add(sum(q.values())>=shadow(28))
    s.SetTimeLimit(120000)
    r=s.Solve()
    return r in (pywraplp.Solver.OPTIMAL,pywraplp.Solver.FEASIBLE), r
def profiles(n):
    # multisets of n degrees in 2..9 summing to 84
    def rec(d, left_n, left_sum, cur):
        if d==9:
            if left_n*9==left_sum: yield cur+[(9,left_n)]
            return
        for k in range(0, left_n+1):
            rem=left_sum-k*d
            if rem<(left_n-k)*(d+1): break
            if rem>(left_n-k)*9: continue
            yield from rec(d+1,left_n-k,rem,cur+[(d,k)])
    for pr in rec(2,n,84,[]): yield dict(pr)
total=0; feas=[]
for n in range(NLO,43):
    ps=list(profiles(n)); cnt=0; bad=0
    for p in ps:
        ok,r=feasible(p); cnt+=1
        if ok: feas.append((n,p))
        elif r!=pywraplp.Solver.INFEASIBLE: bad+=1; print("NOT DECIDED",n,p,r,flush=True)
    print(f"n={n}: {cnt} profiles, feasible {sum(1 for f in feas if f[0]==n)}, undecided {bad}",flush=True); total+=cnt
print("total profiles",total,"feasible",feas)
