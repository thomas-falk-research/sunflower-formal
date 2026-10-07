# Two-root LP: F = {R,S} ∪ X ∪ Y ∪ Z along a disjoint pair R,S, all links <= Delta.
# Z members typed by (a,b) = (|Z∩R|,|Z∩S|), a,b>=1, a+b<=4. Y members (disjoint from S, meet R) typed by |Y∩R|=a;
# X members typed by |X∩S|=b.  Every ABCDN single-root constraint applied at R and at S.
import itertools
from scipy.optimize import linprog, milp, LinearConstraint, Bounds
import numpy as np
types=[(1,1),(1,2),(2,1),(1,3),(3,1),(2,2)]
# variables: n_ab for types, y1,y2,y3, x1,x2,x3
names=[f"n{a}{b}" for a,b in types]+["y1","y2","y3","x1","x2","x3"]
idx={n:i for i,n in enumerate(names)}
def row(d):
    r=np.zeros(len(names)); 
    for k,v in d.items(): r[idx[k]]+=v
    return r
def solve(Delta, integer=True, extra=None):
    A=[];b=[]
    # s_R = exact R-trace singletons: n11+n12+n13+y1 ; p_R = n21+n22+y2 ; t_R = n31+y3
    sR={"n11":1,"n12":1,"n13":1,"y1":1}; pR={"n21":1,"n22":1,"y2":1}; tR={"n31":1,"y3":1}
    sS={"n11":1,"n21":1,"n31":1,"x1":1}; pS={"n12":1,"n22":1,"x2":1}; tS={"n13":1,"x3":1}
    for s,p,t in ((sR,pR,tR),(sS,pS,tS)):
        A.append(row(s)); b.append(40)        # s_x <= 10 each
        A.append(row(p)); b.append(18)        # p_xy <= 3 each
        A.append(row(t)); b.append(4)         # t_m <= 1 each
        A.append(row({**{k:v for k,v in s.items()}})+2*row(p)+3*row(t)); b.append(76)  # d(x)<=20
        A.append(3*row(s)+2*row(p)); b.append(144)   # lemma 6.3
        A.append(row(s)+row(p)+row(t)); b.append(55)  # Prop 6.5 (h<=55)
    A.append(row({"y1":1,"y2":1,"y3":1})); b.append(Delta-1)   # |Y| = d(S)-1 <= Delta-1
    A.append(row({"x1":1,"x2":1,"x3":1})); b.append(Delta-1)
    if extra:
        for r,bb in extra: A.append(row(r)); b.append(bb)
    A=np.array(A); b=np.array(b); c=-np.ones(len(names))
    if integer:
        res=milp(c,constraints=LinearConstraint(A,-np.inf,b),integrality=np.ones(len(names)),bounds=Bounds(0,np.inf))
    else:
        res=linprog(c,A_ub=A,b_ub=b,bounds=[(0,None)]*len(names),method='highs')
    return 2-res.fun, dict(zip(names,np.round(res.x,2)))
for D in (27,22,20,16,12):
    v,x=solve(D)
    print(f"Delta<={D}: max |F| = {v:.0f}", {k:v2 for k,v2 in x.items() if v2})
