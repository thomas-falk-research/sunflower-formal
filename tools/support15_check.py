#!/usr/bin/env python3
"""Independent checker for the certificate that a 28-member 3-uniform family
with  s_E = sum_{v in E}(9 - d_v) + sum_{p in E}(d_p - 1) <= 7  for every
member and every degree >= 2  has support at most 15.

The certificate (docs/ladder/support15_cert.json) is a branch tree on the
numbers n_9, n_8, ... of points of each degree, with at every leaf either a
dual vector y for the type LP (weak duality: every feasible point has
objective <= y.b + sum_j u_j max(0, c_j - (A^T y)_j), and that number is
< 16) or a Farkas vector (the same expression with c = 0 is < 0, so the LP
is infeasible).  This script rebuilds the LP from scratch, in exact
rational arithmetic, checks every leaf, and checks that the tree covers
every integer assignment.  It uses no solver.  Exit 0 iff everything checks.

The LP (relaxation of the family; anything it forbids the family forbids):
  member types (T, E): T = sorted degree triple, E = its three pair degrees,
    with sum(9 - T_i) + sum(E_j - 1) <= 7;
  variables n_d (points of degree d, d unfixed), t_(T,E) >= 0 members of
    that type, q_e >= 0 pairs of two full points with pair degree e;
  sum t = 28;  for each d: sum_T t mult_T(d) = d n_d;
  for each e: sum_T t (number of (9,9) pairs of degree e in T) = e q_e;
  q_1 + q_2 + q_3 <= C(n_9, 2);  0 <= n_d <= 84, t <= 28, q <= 84;
  objective: number of points."""
import itertools, json, sys
from fractions import Fraction as Fr
from math import comb
cert=json.load(open(sys.argv[1] if len(sys.argv)>1 else "docs/ladder/support15_cert.json"))
SMAX=cert["smax"]; LO=cert["lo"]
types=[]
for T in itertools.combinations_with_replacement(range(LO,10),3):
    D=sum(9-d for d in T)
    if D>SMAX: continue
    for E in itertools.product(range(1,4),repeat=3):
        if D+sum(e-1 for e in E)<=SMAX: types.append((T,E))
assert [[list(T),list(E)] for T,E in types]==cert["types"], "type list differs from the certificate's"
def pairs_of(T,E):
    idx=[(0,1),(0,2),(1,2)]
    return [((min(T[i],T[j]),max(T[i],T[j])),E[k]) for k,(i,j) in enumerate(idx)]
def build(fixed):
    cols=[("n",d) for d in range(LO,10) if d not in fixed]+[("t",T) for T in types]+[("q",e) for e in (1,2,3)]
    ci={c:i for i,c in enumerate(cols)}
    c=[Fr(0)]*len(cols); u=[Fr(0)]*len(cols)
    for col in cols:
        if col[0]=="n": c[ci[col]]=Fr(1); u[ci[col]]=Fr(84)
        elif col[0]=="t": u[ci[col]]=Fr(28)
        else: u[ci[col]]=Fr(84)
    rows=[({ci[("t",T)]:Fr(1) for T in types}, Fr(28), "eq")]
    for d in range(LO,10):
        row={ci[("t",T)]:Fr(T[0].count(d)) for T in types if T[0].count(d)}
        if d in fixed: rows.append((row, Fr(d*fixed[d]), "eq"))
        else: row[ci[("n",d)]]=Fr(-d); rows.append((row, Fr(0), "eq"))
    for e in (1,2,3):
        row={ci[("t",T)]:Fr(m) for T in types for m in [sum(1 for pp in pairs_of(*T) if pp==((9,9),e))] if m}
        row[ci[("q",e)]]=Fr(-e); rows.append((row, Fr(0), "eq"))
    k=fixed[9]; rows.append(({ci[("q",e)]:Fr(1) for e in (1,2,3)}, Fr(comb(k,2)), "le"))
    return cols,c,u,rows
def bound(fixed, y, objective):
    cols,c,u,rows=build(fixed)
    if not objective: c=[Fr(0)]*len(cols)
    assert len(y)==len(rows)
    b=Fr(0); aty=[Fr(0)]*len(cols)
    for (row,rhs,kind),yi in zip(rows,y):
        assert kind=="eq" or yi>=0, "dual on a <= row must be nonnegative"
        b+=yi*rhs
        for i,v in row.items(): aty[i]+=yi*v
    for j in range(len(cols)):
        red=c[j]-aty[j]
        if red>0: b+=u[j]*red
    return b+sum(fixed.values())
leaves={}
for leaf in cert["leaves"]:
    fixed={int(k):int(v) for k,v in leaf["fixed"].items()}
    y=[Fr(s) for s in leaf["dual"]]
    if leaf["bound"]=="farkas":
        val=bound(fixed,y,False)-sum(fixed.values())
        assert val<0, ("Farkas value not negative", fixed, val)
    else:
        val=bound(fixed,y,True)
        assert val<16, ("dual bound not below 16", fixed, val)
    leaves[tuple(sorted(fixed.items()))]=val
# coverage: the tree must cover every integer assignment.  Fixed degrees are
# always a suffix 9,8,...,m; a node (9..m fixed) is covered iff it is a leaf
# or all its children (every count of degree m-1 with total degree <= 84)
# are covered.
def covered(fixed):
    key=tuple(sorted(fixed.items()))
    if key in leaves: return True
    m=min(fixed)
    if m==LO: return False
    used=sum(d*c for d,c in fixed.items())
    return all(covered({**fixed,(m-1):c}) for c in range(0,(84-used)//(m-1)+1))
assert all(covered({9:k}) for k in range(0,10)), "tree does not cover every case"
print(f"support15 certificate: {len(leaves)} leaves, all checked exactly; tree covers n_9 = 0..9; "
      f"max leaf bound {float(max(v for v in leaves.values() if v>0)):.4f} < 16")
