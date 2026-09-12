"""Branch-and-bound certificate tree for the support bound n <= 15 (under
s_E <= 7, degrees >= 2, member types with pair degrees, and only the
full-pair cap  #pairs of full points <= C(n_9, 2)).  Branch on n_9, then
n_8, n_7, n_6, ... only where the LP bound is >= 16; every leaf's LP
(GLOP) optimum is < 16, so the integer optimum is <= 15.  Prints the tree."""
import itertools, sys
from ortools.linear_solver import pywraplp
SMAX=7; LO=2
types=[]
for T in itertools.combinations_with_replacement(range(LO,10),3):
    D=sum(9-d for d in T)
    if D>SMAX: continue
    for E in itertools.product(range(1,4),repeat=3):
        if D+sum(e-1 for e in E)<=SMAX: types.append((T,E))
def pairs_of(T,E):
    idx=[(0,1),(0,2),(1,2)]
    return [((min(T[i],T[j]),max(T[i],T[j])),E[k]) for k,(i,j) in enumerate(idx)]
def lp(fixed):
    s=pywraplp.Solver.CreateSolver("GLOP")
    n={d:(s.NumVar(0,84,f"n{d}") if d not in fixed else fixed[d]) for d in range(LO,10)}
    t={T:s.NumVar(0,28,str(T)) for T in types}
    q={e:s.NumVar(0,84,f"q99_{e}") for e in (1,2,3)}
    s.Add(sum(t.values())==28)
    for d in range(LO,10): s.Add(sum(t[T]*T[0].count(d) for T in types)==d*n[d])
    for e in (1,2,3):
        s.Add(sum(t[T]*sum(1 for pp in pairs_of(*T) if pp==((9,9),e)) for T in types)==e*q[e])
    k=fixed[9]; s.Add(sum(q.values())<=k*(k-1)//2)
    s.Maximize(sum(v for d,v in n.items() if d not in fixed)+sum(fixed.values()))
    r=s.Solve()
    return None if r!=pywraplp.Solver.OPTIMAL else s.Objective().Value()
leaves=[]; maxdepth=0
def branch(fixed, nextd):
    global maxdepth
    v=lp(fixed)
    if v is None: leaves.append((dict(fixed),"infeasible")); return
    if v<16: leaves.append((dict(fixed),v)); maxdepth=max(maxdepth,len(fixed)); return
    assert nextd>=LO, ("all degrees fixed but LP>=16", fixed, v)
    used=sum(d*c for d,c in fixed.items())
    for c in range(0,(84-used)//nextd+1):
        f=dict(fixed); f[nextd]=c; branch(f, nextd-1)
for k in range(10): branch({9:k}, 8)
print("leaves",len(leaves),"max depth",maxdepth,"max leaf LP",max(v for f,v in leaves if v!="infeasible"))
for f,v in leaves:
    if v!="infeasible" and v>15: print("  tight leaf",f,round(v,3))
