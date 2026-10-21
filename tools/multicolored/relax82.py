#!/usr/bin/env python3
"""Largest Phi allowed by the Benders master's combinatorial rows alone.

docs/roadmap.md section 82.3. Maximises |Phi| over subsets of S_D^(n) that
are free, use each word at most K times per leg, avoid every Lemma 81.A pair
and (with rows3 = 1) every conflict three-set of Corollary 82.B, in the run
class r of benders.py (its forced triple, no triple with more monochromatic
coordinates). Only these consequences of the face condition are used, so the
optimum is an upper bound on what the Benders search can find in that run
class, and the set found need not be a face. The incumbent is printed and
re-checked exactly against the rows.

    python3 -I tools/multicolored/relax82.py D n K r timelimit_s rows3(0|1)
"""
import json, os, sys, time

import numpy as np
import highspy

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import benders as B

D, n, K, r, tl = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), float(sys.argv[5])
with3 = sys.argv[6] == "1"
T = B.Sn(D, n); A = D ** n; N = len(T)
mono = [B.nmono(D, n, t) for t in T]
rep = next(k for k in range(N) if mono[k] == r)
allowed = [mono[k] <= r for k in range(N)]
m = B.quiet(); inf = highspy.kHighsInf
for k in range(N):
    m.addVar(1.0 if k == rep else 0.0, 1.0 if allowed[k] else 0.0)
m.changeColsIntegrality(N, np.arange(N, dtype=np.int32), np.array([highspy.HighsVarType.kInteger] * N))
m.changeColsCost(N, np.arange(N, dtype=np.int32), -np.ones(N))


def add_row(lo, hi, idx):
    m.addRow(lo, hi, len(idx), np.array(idx, dtype=np.int32), np.ones(len(idx)))


for i in range(3):
    fib, use = {}, {}
    for k, t in enumerate(T):
        fib.setdefault(tuple(t[j] for j in range(3) if j != i), []).append(k)
        use.setdefault(t[i], []).append(k)
    for ks in fib.values():
        if len(ks) > 1:
            add_row(-inf, 1.0, ks)
    for ks in use.values():
        add_row(-inf, float(K), ks)
for a, b in B.rectangle_conflicts(T):
    add_row(-inf, 1.0, [a, b])
n3 = 0
if with3:
    bad = B.incompatible(T)
    P, Q = B.relations3(T, A, bad)
    Pc = np.unique(np.sort(P[B.conflicting3(T, P, Q, K, bad)], 1), axis=0)
    al = np.array(allowed)
    Pc = Pc[al[Pc].all(1)]
    n3 = len(Pc)
    del P, Q
    if n3:
        m.addRows(n3, np.full(n3, -inf), np.full(n3, 2.0), 3 * n3, np.arange(0, 3 * n3, 3, dtype=np.int32),
                  Pc.reshape(-1).astype(np.int32), np.ones(3 * n3))
m.setOptionValue("time_limit", tl); m.setOptionValue("mip_rel_gap", 0.0)
t0 = time.time(); m.run()
info = m.getInfo()
out = {"D": D, "n": n, "K": K, "run": r, "rows3": n3, "status": str(m.getModelStatus()),
       "best": -info.objective_function_value, "bound": -info.mip_dual_bound,
       "seconds": round(time.time() - t0, 1)}
if info.primal_solution_status:
    # re-check the incumbent exactly, independently of the MILP tolerances
    phi = sorted(k for k, v in enumerate(m.getSolution().col_value) if v > 0.5)
    fibres = [{tuple(T[k][j] for j in range(3) if j != i) for k in phi} for i in range(3)]
    rect = {frozenset(p) for p in B.rectangle_conflicts(T)}
    inphi = set(phi)
    conf3 = 0
    if with3:
        conf3 = int(np.isin(Pc, phi).all(1).sum())
    out["phi"] = phi
    out["recheck"] = {
        "size": len(phi),
        "forced_triple_in": rep in inphi,
        "all_allowed": all(allowed[k] for k in phi),
        "free": all(len(f) == len(phi) for f in fibres),
        "max_uses_per_word": max(sum(1 for k in phi if T[k][i] == x) for i in range(3) for x in range(A)),
        "lemma_81A_pairs_inside": sum(1 for a in phi for b in phi if a < b and frozenset((a, b)) in rect),
        "conflict_3sets_inside": conf3}
print(json.dumps(out))
