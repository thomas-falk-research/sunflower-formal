#!/usr/bin/env python3
"""Border (combinatorially degenerate) matchings in S_D^(n): docs/roadmap.md section 80.

A set Phi = {t_1..t_m} of triples of S_D^(n) with pairwise distinct words in
each leg is the zero set of a combinatorial degeneration of S_D^(n) ([CVZ18]
Def. 4.9, restricted to the words Phi uses) iff the system

    alpha_i + beta_j - alpha_l - beta_l >= 1
        for every (i,j,l) not all equal with (x_i, y_j, z_l) in S_D^(n)     (*)

is feasible (u1(x_i) = alpha_i, u2(y_i) = beta_i, u3(z_i) = -alpha_i - beta_i;
words outside Phi get a weight larger than every other, which makes every
element using them positive). Then [CVZ18] Lemma 4.13 gives
Lambda(D) >= m^(1/n), and Lemma 78.A's argument gives SR_C(q_c) >= m^(1/n) for
every c nonzero on rainbow tuples. Feasibility of (*) is hereditary, so a DFS
over sets with pruning is exact.

Pairwise feasibility is closed-form. For two triples i, l the constraints
are sign conditions on a = alpha_l - alpha_i, b = beta_l - beta_i and
a + b = gamma_l - gamma_i, from the six patterns (l,i,i), (i,l,l) [a],
(i,l,i), (l,i,l) [b], (i,i,l), (l,l,i) [a+b]; infeasible iff a 2-cycle in one
of them, or a, b forced positive with a+b forced negative, or the reverse.

Symmetry: Sym(D) per coordinate (on all legs alike), permutations of the n
coordinates and of the 3 legs all preserve S_D^(n) and (*). The orbit of a
triple is its number of monochromatic coordinates. Run r forces the
representative with r monochromatic coordinates into Phi and forbids triples
with more than r (a set containing one is covered by an earlier run).

    python3 -I tools/multicolored/bmatch.py max D n [timelimit_s]
        largest m found, with the certificate (alpha, beta, Phi) as JSON;
        "exhaustive": true when every run finished.
LP: scipy linprog (HiGHS), floating point. A found certificate is re-checked
in exact integers by tools/multicolored/degen2.py verify (see `cert`); an
infeasible verdict at a node is the LP's word (no exact re-check), so an
exhaustive negative is COMPUTED, not PROVEN.
"""
import itertools, json, sys, time


def S1(D):
    return [t for t in itertools.product(range(D), repeat=3) if len(set(t)) in (1, 3)]


def Sn(D, n):
    out = []
    for combo in itertools.product(S1(D), repeat=n):
        x = y = z = 0
        for (a, b, c) in combo:
            x, y, z = x * D + a, y * D + b, z * D + c
        out.append((x, y, z))
    return out


def nmono(D, n, t):
    """number of monochromatic coordinates of a triple of encoded words"""
    x, y, z = t
    c = 0
    for _ in range(n):
        if x % D == y % D == z % D:
            c += 1
        x, y, z = x // D, y // D, z // D
    return c


def feasible(chosen, inS):
    """LP feasibility of (*) for the chosen triples."""
    import numpy as np
    from scipy.optimize import linprog
    m = len(chosen)
    if m <= 1:
        return True, [0.0] * m, [0.0] * m
    rows = []
    for i, j, l in itertools.product(range(m), repeat=3):
        if i == j == l:
            continue
        if (chosen[i][0], chosen[j][1], chosen[l][2]) in inS:
            r = np.zeros(2 * m)
            r[i] -= 1; r[m + j] -= 1; r[l] += 1; r[m + l] += 1   # -(a_i+b_j-a_l-b_l) <= -1
            rows.append(r)
    if not rows:
        return True, [0.0] * m, [0.0] * m
    A = np.array(rows)
    bounds = [(0, 0)] + [(-1e4, 1e4)] * (m - 1) + [(0, 0)] + [(-1e4, 1e4)] * (m - 1)
    res = linprog(np.zeros(2 * m), A_ub=A, b_ub=-np.ones(len(rows)), bounds=bounds, method="highs")
    if res.status != 0:
        return False, None, None
    return True, res.x[:m].tolist(), res.x[m:].tolist()


def pair_ok(t, s, inS):
    """closed-form pairwise feasibility of (*) on {t, s} (t = index i, s = index l)."""
    if t[0] == s[0] or t[1] == s[1] or t[2] == s[2]:
        return False                          # a matching: distinct words per leg
    def has(a, b, c):
        return (a[0], b[1], c[2]) in inS
    # a = alpha_s - alpha_t:  (s,t,t) in S -> a >= 1 ;  (t,s,s) in S -> a <= -1
    ap, an = has(s, t, t), has(t, s, s)
    # b = beta_s - beta_t:    (t,s,t) -> b >= 1 ;       (s,t,s) -> b <= -1
    bp, bn = has(t, s, t), has(s, t, s)
    # g = gamma_s - gamma_t:  (t,t,s) -> gamma_t >= gamma_s + 1 -> g <= -1 ; (s,s,t) -> g >= 1
    gn, gp = has(t, t, s), has(s, s, t)
    if (ap and an) or (bp and bn) or (gp and gn):
        return False
    if ap and bp and gn:
        return False
    if an and bn and gp:
        return False
    return True


def search_max(D, n, tl=600.0):
    T = Sn(D, n)
    inS = set(T)
    N = len(T)
    t0 = time.time()
    adj = [0] * N
    for a in range(N):
        for b in range(a + 1, N):
            if pair_ok(T[a], T[b], inS):
                adj[a] |= 1 << b
                adj[b] |= 1 << a
    best = {"m": 0, "phi": [], "alpha": [], "beta": []}
    exhaustive = True
    mono = [nmono(D, n, t) for t in T]
    runs = []
    for r in range(n, -1, -1):              # more monochromatic coordinates first
        rep = next(k for k in range(N) if mono[k] == r)
        allowed = 0
        for k in range(N):
            if mono[k] <= r and k != rep:
                allowed |= 1 << k
        runs.append((r, rep, allowed))
    nodes = [0]

    def popcount(v):
        return bin(v).count("1")

    def dfs(chosen, cand):
        nonlocal exhaustive
        nodes[0] += 1
        if time.time() - t0 > tl:
            exhaustive = False
            return
        if len(chosen) + popcount(cand) <= best["m"]:
            return
        if len(chosen) > best["m"]:
            ok, al, be = feasible([T[k] for k in chosen], inS)
            if not ok:
                return
            best.update(m=len(chosen), phi=[T[k] for k in chosen], alpha=al, beta=be)
        while cand:
            if len(chosen) + popcount(cand) <= best["m"]:
                return
            k = cand.bit_length() - 1
            cand &= ~(1 << k)
            new = chosen + [k]
            if len(new) >= 3:
                ok, _, _ = feasible([T[j] for j in new], inS)
                if not ok:
                    continue
            dfs(new, cand & adj[k])

    for r, rep, allowed in runs:
        dfs([rep], allowed & adj[rep])
    return {"D": D, "n": n, "max_m_found": best["m"], "exhaustive": exhaustive,
            "seconds": round(time.time() - t0, 1), "nodes": nodes[0],
            "phi": best["phi"], "alpha": best["alpha"], "beta": best["beta"]}


def cert(res):
    """turn (alpha, beta, Phi) into a degen2.py certificate with integer weights."""
    from fractions import Fraction
    D, n = res["D"], res["n"]
    A = D ** n
    phi, al, be = res["phi"], res["alpha"], res["beta"]
    # rationalise and scale; the LP solution satisfies (*) with margin 1, so
    # rounding to a fine grid and re-scaling keeps the strict inequalities
    q = 64
    a = [round(v * q) for v in al]
    b = [round(v * q) for v in be]
    big = 10 * (max([abs(v) for v in a + b] + [1]) * 3 + 1)
    u = [[big] * A, [big] * A, [big] * A]
    for (x, y, z), ai, bi in zip(phi, a, b):
        u[0][x] = ai
        u[1][y] = bi
        u[2][z] = -ai - bi
    return {"D": D, "n": n, "u": u}


if __name__ == "__main__":
    if sys.argv[1] == "max":
        D, n = int(sys.argv[2]), int(sys.argv[3])
        tl = float(sys.argv[4]) if len(sys.argv) > 4 else 600.0
        r = search_max(D, n, tl)
        r["cert"] = cert(r) if r["phi"] else None
        print(json.dumps(r))
