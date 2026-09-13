"""Type relaxation with pair degrees.  A member type is (d1<=d2<=d3) with
pair degrees (e12,e13,e23) in 1..3 such that
   s = sum(9-d_i) + sum(e_ij - 1) <= SMAX.
Point classes: n_d points of degree d.  Pair classes: q[(a,b),e] = number of
point pairs with degree types a<=b and pair degree e>=1.
Constraints: members total 28; point incidences d*n_d; pair incidences
e*q[(a,b),e]; number of pairs of type (a,b) at most n_a*n_b (a<b) or
n_a*(n_a-1)/2 (a=b).  Maximise support."""
import itertools, sys
from ortools.sat.python import cp_model
SMAX=int(sys.argv[1]) if len(sys.argv)>1 else 7
LO=int(sys.argv[2]) if len(sys.argv)>2 else 1
types=[]
for T in itertools.combinations_with_replacement(range(LO,10),3):
    D=sum(9-d for d in T)
    if D>SMAX: continue
    for E in itertools.product(range(1,4),repeat=3):
        if D+sum(e-1 for e in E)<=SMAX: types.append((T,E))
m=cp_model.CpModel()
n={d:m.NewIntVar(0,84,f"n{d}") for d in range(LO,10)}
t={k:m.NewIntVar(0,28,str(k)) for k in types}
pairkeys=[(a,b) for a in range(LO,10) for b in range(a,10)]
q={(pk,e):m.NewIntVar(0,84,f"q{pk}{e}") for pk in pairkeys for e in (1,2,3)}
m.Add(sum(t.values())==28)
for d in range(LO,10):
    m.Add(sum(t[k]*k[0].count(d) for k in types)==d*n[d])
# pair incidences: member (T,E) has pairs (T[i],T[j]) with degree E[idx]
def pairs_of(T,E):
    idx=[(0,1),(0,2),(1,2)]
    return [((min(T[i],T[j]),max(T[i],T[j])),E[k]) for k,(i,j) in enumerate(idx)]
for pk in pairkeys:
    for e in (1,2,3):
        m.Add(sum(t[k]*sum(1 for pp in pairs_of(*k) if pp==(pk,e)) for k in types)==e*q[(pk,e)])
for (a,b) in pairkeys:
    tot=sum(q[((a,b),e)] for e in (1,2,3))
    if a<b:
        prod=m.NewIntVar(0,84*84,f"p{a}{b}"); m.AddMultiplicationEquality(prod,[n[a],n[b]]); m.Add(tot<=prod)
    else:
        sq=m.NewIntVar(0,84*84,f"sq{a}"); m.AddMultiplicationEquality(sq,[n[a],n[a]]); m.Add(2*tot<=sq-n[a])

# Kruskal-Katona: m triples span at least shadow(m) pairs.  Members all of
# whose pairs have degree >= e are triples whose pairs all lie among the
# pairs of degree >= e, so  #pairs(degree>=e) >= shadow(#such members).
from math import comb
def shadow(mm):
    if mm==0: return 0
    tot=0; k=3
    while mm>0 and k>=1:
        a=k
        while comb(a+1,k)<=mm: a+=1
        tot+=comb(a,k-1); mm-=comb(a,k); k-=1
    return tot
SH=[shadow(i) for i in range(29)]
for e in (2,3):
    me=m.NewIntVar(0,28,f"m{e}"); m.Add(me==sum(t[k] for k in types if min(k[1])>=e))
    pe=sum(q[(pk,f)] for pk in pairkeys for f in (1,2,3) if f>=e)
    sh=m.NewIntVar(0,100,f"sh{e}"); m.AddElement(me,SH,sh); m.Add(pe>=sh)
# also the whole family: pairs with degree>=1 >= shadow(28)
m.Add(sum(q.values())>=SH[28])

NPTS=int(sys.argv[3])
m.Add(sum(n.values())==NPTS)
found=[]
while True:
    s=cp_model.CpSolver(); s.parameters.num_workers=4; st=s.Solve(m)
    if st not in (cp_model.OPTIMAL,cp_model.FEASIBLE): break
    prof=tuple(s.Value(n[d]) for d in range(LO,10)); found.append(prof)
    # no-good: not this exact profile
    lits=[]
    for d in range(LO,10):
        b=m.NewBoolVar(""); m.Add(n[d]!=s.Value(n[d])).OnlyEnforceIf(b); m.Add(n[d]==s.Value(n[d])).OnlyEnforceIf(b.Not()); lits.append(b)
    m.AddBoolOr(lits)
print("n",NPTS,"feasible degree profiles (n_2..n_9):",len(found))
for p in found: print(p)
sys.exit(0)
s=cp_model.CpSolver(); s.parameters.num_workers=4; s.parameters.max_time_in_seconds=600; st=s.Solve(m)
print("SMAX",SMAX,"LO",LO,"types",len(types),"status",s.StatusName(st),"max support",s.ObjectiveValue(),"bound",s.BestObjectiveBound())
print("degree profile:",{d:s.Value(n[d]) for d in n if s.Value(n[d])})
print("member types:",{k:s.Value(t[k]) for k in types if s.Value(t[k])})
print("pair classes:",{k:s.Value(v) for k,v in q.items() if s.Value(v)})
