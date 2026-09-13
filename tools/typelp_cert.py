"""Exact certificate for the support bound.  Same branch tree as
typelp_tree.py; at each leaf the GLOP dual solution is rounded to rationals
and weak duality is re-evaluated in exact arithmetic:
   max c.x  s.t.  A_eq x = b_eq,  A_le x <= b_le,  0 <= x <= u
   bound(y_eq free, y_le >= 0) = y_eq.b_eq + y_le.b_le + sum_j u_j * max(0, c_j - (A^T y)_j)
Any such bound is >= the LP optimum >= the integer optimum, so a leaf with
an exact bound < 16 has no integer point with support >= 16.  Writes the
certificate (tree + duals) as JSON."""
import itertools, sys, json
from fractions import Fraction as Fr
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
def build(fixed):
    """columns: n_d (unfixed d), t_T, q_e.  Returns c, u, rows (coeff dict, rhs, kind)."""
    cols=[("n",d) for d in range(LO,10) if d not in fixed]+[("t",T) for T in types]+[("q",e) for e in (1,2,3)]
    ci={c:i for i,c in enumerate(cols)}
    c=[Fr(0)]*len(cols); u=[Fr(0)]*len(cols)
    for col in cols:
        if col[0]=="n": c[ci[col]]=Fr(1); u[ci[col]]=Fr(84)
        elif col[0]=="t": u[ci[col]]=Fr(28)
        else: u[ci[col]]=Fr(84)
    rows=[]
    rows.append(({ci[("t",T)]:Fr(1) for T in types}, Fr(28), "eq"))
    for d in range(LO,10):
        row={}
        for T in types:
            m=T[0].count(d)
            if m: row[ci[("t",T)]]=Fr(m)
        if d in fixed: rows.append((row, Fr(d*fixed[d]), "eq"))
        else: row[ci[("n",d)]]=Fr(-d); rows.append((row, Fr(0), "eq"))
    for e in (1,2,3):
        row={}
        for T in types:
            m=sum(1 for pp in pairs_of(*T) if pp==((9,9),e))
            if m: row[ci[("t",T)]]=Fr(m)
        row[ci[("q",e)]]=Fr(-e); rows.append((row, Fr(0), "eq"))
    k=fixed[9]; rows.append(({ci[("q",e)]:Fr(1) for e in (1,2,3)}, Fr(k*(k-1)//2), "le"))
    return cols,c,u,rows
def solve_lp(fixed):
    cols,c,u,rows=build(fixed)
    s=pywraplp.Solver.CreateSolver("GLOP")
    x=[s.NumVar(0,float(u[i]),str(i)) for i in range(len(cols))]
    cons=[]
    for row,rhs,kind in rows:
        expr=sum(float(v)*x[i] for i,v in row.items())
        cons.append(s.Add(expr==float(rhs)) if kind=="eq" else s.Add(expr<=float(rhs)))
    s.Maximize(sum(float(c[i])*x[i] for i in range(len(cols))))
    r=s.Solve()
    if r!=pywraplp.Solver.OPTIMAL: return None, None
    y=[Fr(cn.dual_value()).limit_denominator(10**6) for cn in cons]
    return s.Objective().Value(), y
def exact_bound(fixed, y):
    cols,c,u,rows=build(fixed)
    # sign convention: for a maximisation, y_le must be >= 0
    for (row,rhs,kind),yi in zip(rows,y):
        if kind=="le" and yi<0: yi=Fr(0)
    bound=Fr(0); aty=[Fr(0)]*len(cols)
    for (row,rhs,kind),yi in zip(rows,y):
        if kind=="le" and yi<0: yi=Fr(0)
        bound+=yi*rhs
        for i,v in row.items(): aty[i]+=yi*v
    for j in range(len(cols)):
        red=c[j]-aty[j]
        if red>0: bound+=u[j]*red
    return bound+sum(fixed.values())
leaves=[]
def branch(fixed, nextd):
    v,y=solve_lp(fixed)
    if v is None:
        # infeasible LP: certify by Farkas would be needed; instead branch further until degrees exhaust (finite) or record
        leaves.append((dict(fixed),"infeasible",None)); return
    b=exact_bound(fixed,y)
    if b<16: leaves.append((dict(fixed),float(b),[str(t) for t in y])); return
    assert nextd>=LO, ("no branch left", fixed, float(b))
    used=sum(d*c for d,c in fixed.items())
    for cnt in range(0,(84-used)//nextd+1):
        f=dict(fixed); f[nextd]=cnt; branch(f, nextd-1)
for k in range(10): branch({9:k}, 8)
inf=[f for f,b,y in leaves if b=="infeasible"]
mx=max(b for f,b,y in leaves if b!="infeasible")
print("leaves",len(leaves),"infeasible leaves",len(inf),"max exact dual bound",mx)
json.dump({"smax":SMAX,"lo":LO,"types":[[list(T),list(E)] for T,E in types],"leaves":[{"fixed":f,"bound":b,"dual":y} for f,b,y in leaves]},open("support15_cert.json","w"))
print("infeasible leaves:",inf[:10])

# ---- Farkas certificates for the LP-infeasible leaves -------------------
def farkas(fixed):
    """Find y (free on eq rows, >=0 on le rows, |y|<=1) minimising
    y.b + sum_j u_j * max(0, -(A^T y)_j); a value < 0 certifies infeasibility
    of {A_eq x=b_eq, A_le x<=b_le, 0<=x<=u} by weak duality with c = 0."""
    cols,c,u,rows=build(fixed)
    s=pywraplp.Solver.CreateSolver("GLOP")
    y=[s.NumVar(-1,1,f"y{i}") if kind=="eq" else s.NumVar(0,1,f"y{i}") for i,(row,rhs,kind) in enumerate(rows)]
    sl=[s.NumVar(0,s.infinity(),f"s{j}") for j in range(len(cols))]
    aty=[[] for _ in cols]
    for i,(row,rhs,kind) in enumerate(rows):
        for j,v in row.items(): aty[j].append((i,float(v)))
    for j in range(len(cols)):
        s.Add(sl[j]+sum(v*y[i] for i,v in aty[j])>=0)
    s.Minimize(sum(float(rhs)*y[i] for i,(row,rhs,kind) in enumerate(rows))+sum(float(u[j])*sl[j] for j in range(len(cols))))
    r=s.Solve(); assert r==pywraplp.Solver.OPTIMAL
    yr=[Fr(v.solution_value()).limit_denominator(10**6) for v in y]
    # exact evaluation with c = 0
    bound=Fr(0); at=[Fr(0)]*len(cols)
    for (row,rhs,kind),yi in zip(rows,yr):
        if kind=="le" and yi<0: yi=Fr(0)
        bound+=yi*rhs
        for i,v in row.items(): at[i]+=yi*v
    for j in range(len(cols)):
        if -at[j]>0: bound+=u[j]*(-at[j])
    return bound, yr
cert=json.load(open("support15_cert.json"))
ok=True
for leaf in cert["leaves"]:
    if leaf["bound"]=="infeasible":
        f={int(k):v for k,v in leaf["fixed"].items()}
        b,yr=farkas(f); print("farkas",f,"exact value",float(b))
        if b<0: leaf["bound"]="farkas"; leaf["dual"]=[str(t) for t in yr]
        else: ok=False
json.dump(cert,open("support15_cert.json","w"))
print("all leaves certified:", ok and all(l["bound"]!="infeasible" for l in cert["leaves"]))
