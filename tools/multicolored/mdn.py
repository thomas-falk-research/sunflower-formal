#!/usr/bin/env python3
"""Is M(D,n) >= m ?  docs/roadmap.md section 75.4. Needs cadical on PATH.

Usage: python3 -I tools/multicolored/mdn.py D n m scratch.cnf
Every SAT witness is re-checked by brute force, sharing nothing with the encoding.
UNSAT is cadical's word only: no proof log is kept, so it is COMPUTED, not proved.
"""
# M(D,n): max induced matching in S_D^(n), S_D = {(a,b,c) in [D]^3 : mono or rainbow}.
# CNF: s_t per t in S^(n); X_x/Y_y/Z_z "used" flags (s_t -> X_{t1} etc.);
# at-most-one s_t per x (and per y, per z); closure: X_x & Y_y & Z_z -> s_(x,y,z)
# for every (x,y,z) in S^(n); at-least-m via a sequential counter.
import itertools, subprocess, sys, time, os
D, n, m = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
out = sys.argv[4]
S1 = [t for t in itertools.product(range(D), repeat=3) if len(set(t)) in (1, 3)]
T = [tuple(zip(*combo)) for combo in itertools.product(S1, repeat=n)]  # each t = (x,y,z), x in [D]^n
nv = 0
def new():
    global nv; nv += 1; return nv
s = {t: new() for t in T}
V = list(itertools.product(range(D), repeat=n))
X = {v: new() for v in V}; Y = {v: new() for v in V}; Z = {v: new() for v in V}
cl = []
by = [dict(), dict(), dict()]
for t in T:
    for k, F in enumerate((X, Y, Z)):
        cl.append([-s[t], F[t[k]]]); by[k].setdefault(t[k], []).append(s[t])
def amo(lits):  # sequential AMO
    if len(lits) <= 1: return
    prev = None
    for i, l in enumerate(lits):
        if i < len(lits) - 1:
            r = new(); cl.append([-l, r])
            if prev: cl.append([-prev, r]); cl.append([-l, -prev])
            prev = r
        else:
            cl.append([-l, -prev])
for k in range(3):
    for v, lits in by[k].items(): amo(lits)
for t in T:
    cl.append([-X[t[0]], -Y[t[1]], -Z[t[2]], s[t]])
# at least m of the s_t: R[i][j] = at least j among first i
L = [s[t] for t in T]; N = len(L)
R = [[None] * (m + 1) for _ in range(N + 1)]
for i in range(1, N + 1):
    for j in range(1, min(i, m) + 1):
        R[i][j] = new()
        opts = []
        # R[i][j] -> R[i-1][j] or (L[i-1] and R[i-1][j-1])
        a = R[i - 1][j] if j <= i - 1 else None
        b = R[i - 1][j - 1] if j - 1 >= 1 else True
        if a is None and b is True:
            cl.append([-R[i][j], L[i - 1]])
        elif a is None:
            cl.append([-R[i][j], L[i - 1]]); cl.append([-R[i][j], b])
        elif b is True:
            cl.append([-R[i][j], a, L[i - 1]])
        else:
            cl.append([-R[i][j], a, L[i - 1]]); cl.append([-R[i][j], a, b])
cl.append([R[N][m]])
# Symmetry: relabelling letters by one permutation per coordinate (applied to x, y, z alike)
# and permuting coordinates both preserve S^(n) and inducedness, so some chosen triple may be
# taken canonical: coordinates (0,0,0) first, then (0,1,2).
canon = []
for k in range(n + 1):
    pat = [(0, 0, 0)] * k + [(0, 1, 2)] * (n - k)
    canon.append(s[tuple(zip(*pat))])
cl.append(canon)
with open(out, 'w') as f:
    f.write(f"p cnf {nv} {len(cl)}\n")
    for c in cl: f.write(" ".join(map(str, c)) + " 0\n")
t0 = time.time()
r = subprocess.run(["cadical", "-q", out], capture_output=True, text=True)
dt = time.time() - t0
status = "SAT" if r.returncode == 10 else "UNSAT" if r.returncode == 20 else f"rc{r.returncode}"
if status == "SAT":
    vals = set(int(x) for line in r.stdout.splitlines() if line.startswith('v') for x in line.split()[1:])
    chosen = [t for t in T if s[t] in vals]
    # independent re-check of the witness, sharing nothing with the encoding
    G = set(T)
    assert len(chosen) >= m
    for i, j, l in itertools.product(range(len(chosen)), repeat=3):
        if not i == j == l:
            assert (chosen[i][0], chosen[j][1], chosen[l][2]) not in G, "witness not induced"
    print(f"D={D} n={n} m>={m}: SAT ({len(chosen)} found, witness re-checked) {dt:.1f}s vars={nv} clauses={len(cl)}")
else:
    print(f"D={D} n={n} m>={m}: {status} {dt:.1f}s vars={nv} clauses={len(cl)}")
os.remove(out)
