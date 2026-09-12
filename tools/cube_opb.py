#!/usr/bin/env python3
"""Export one degree-sequence cube of the 28-member question as an OPB
pseudo-Boolean instance, the same constraints as tools/cuben.py:
exact degrees, pair degree <= 3, no three pairwise disjoint members
(ternary clauses), exactly 28 members, lex-leader prefix (K) per adjacent
equal-degree transposition, and the cut B (members disjoint from any
member <= B).  Usage: cube_opb.py n parts K B > file.opb"""
import sys, itertools
n=int(sys.argv[1]); parts=[int(x) for x in sys.argv[2].split(',')] if sys.argv[2]!='0' else []
K=int(sys.argv[3]); B=int(sys.argv[4]); D=9; c=3; T=28
degs=[D-x for x in parts+[0]*(n-len(parts))]; assert sum(degs)==3*T
cands=list(itertools.combinations(range(n),3)); var={t:f"x{i+1}" for i,t in enumerate(cands)}
S=[set(t) for t in cands]; out=[]
def lin(terms, op, rhs):
    if op=="=":  # RoundingSat's header counts equalities separately; write two inequalities instead
        lin(terms,">=",rhs); lin([(-w,v) for w,v in terms],">=",-rhs); return
    out.append(" ".join(f"{'+' if w>=0 else ''}{w} {v}" for w,v in terms)+f" {op} {rhs} ;")
for v in range(n): lin([(1,var[t]) for t in cands if v in t],"=",degs[v])
for p in itertools.combinations(range(n),2): lin([(-1,var[t]) for t in cands if p[0] in t and p[1] in t],">=",-c)
for i in range(len(cands)):
    for j in range(i+1,len(cands)):
        if S[i]&S[j]: continue
        u=S[i]|S[j]
        for k in range(j+1,len(cands)):
            if u&S[k]: continue
            lin([(-1,var[cands[i]]),(-1,var[cands[j]]),(-1,var[cands[k]])],">=",-2)
lin([(1,var[t]) for t in cands],"=",T)
def swap(t,v): return tuple(sorted((v+1 if y==v else v if y==v+1 else y) for y in t))
for v in range(n-1):
    if K and degs[v]==degs[v+1]:
        pos=[t for t in cands if (v in t)!=(v+1 in t)][:K]
        terms=[]
        for i,t in enumerate(pos):
            w=1<<(K-1-i); terms.append((w,var[t])); terms.append((-w,var[swap(t,v)]))
        lin(terms,">=",0)
if B:
    for i,t in enumerate(cands):
        # sum_{j disjoint from t} x_j <= B + T*(1-x_t)  <=>  -sum x_j - T x_t >= -B - T
        lin([(-1,var[cands[j]]) for j in range(len(cands)) if not (S[i]&S[j])]+[(-T,var[t])],">=",-B-T)
print(f"* #variable= {len(cands)} #constraint= {len(out)} #equal= 0 intsize= 64")
print("\n".join(out))
