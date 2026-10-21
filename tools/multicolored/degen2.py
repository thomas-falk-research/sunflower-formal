#!/usr/bin/env python3
"""Free combinatorial degenerations of the n-letter support S_D^(n).

docs/roadmap.md section 79. Each leg's alphabet is [D]^n; a triple (x,y,z) of
words lies in S_D^(n) when every coordinate (x_k, y_k, z_k) lies in S_D (all
equal, or pairwise distinct). q_c^{(x)n} has exactly this support, and
SR(q_c^{(x)n}) = SR(q_c)^n ([CVZ18] Cor. 5.7), so a free combinatorial
degeneration Phi of S_D^(n) with max_P min_j H(P_j) = h gives
SR(q_c) >= 2^(h/n) over C, for every c nonzero on rainbow tuples (Lemma 78.A's
argument, applied to q_c^{(x)n}).

Weights u_i : [D]^n -> Z are arbitrary (not of product form). Since
h <= log2(min_i #letters of Phi in leg i), beating the single-letter value
log2 3 per letter needs more than 3^n letters in every leg; the search
therefore maximises L = min_i #letters used in leg i.

    search:  python3 -I tools/multicolored/degen2.py search D n [timelimit_s] [B]
             MILP (scipy/HiGHS) over integer weights |u| <= B (default 4*D^n).
             Freeness is one clique constraint per leg and per pair of other
             letters: at most one element of Phi in each fibre.
             Restriction to a sub-box is covered only in so far as large
             weights within |u| <= B exclude letters; it is not separately
             searched.
    verify:  python3 -I tools/multicolored/degen2.py verify CERT.json
             exact integer check of nonnegativity on all of S_D^(n), the zero
             set and freeness, sharing no code with the search; then
             max_P min_j H(P_j) by floating-point SLSQP (value achieved by an
             explicit P, so a valid lower bound on h).
"""
import itertools, json, math, sys


def S1(D):
    return [t for t in itertools.product(range(D), repeat=3) if len(set(t)) in (1, 3)]


def Sn(D, n):
    """S_D^(n) as triples of letter indices; a word is encoded base D."""
    out = []
    for combo in itertools.product(S1(D), repeat=n):
        x = y = z = 0
        for (a, b, c) in combo:
            x, y, z = x * D + a, y * D + b, z * D + c
        out.append((x, y, z))
    return out


def search(D, n, tl=600.0, B=None):
    import numpy as np
    from scipy.optimize import milp, LinearConstraint, Bounds
    from scipy.sparse import lil_matrix
    A = D ** n
    B = B or 4 * A
    T = Sn(D, n)
    nu, nz, ny = 3 * A, len(T), 3 * A
    iz, iy, iL = nu, nu + nz, nu + nz + ny
    N = iL + 1
    M = 3 * B + 1
    cons = []                                   # (dict col->coef, lo, hi)
    for k, t in enumerate(T):
        base = {i * A + t[i]: 1 for i in range(3)}
        r = dict(base); r[iz + k] = 1
        cons.append((r, 1, np.inf))             # w + z >= 1
        r = dict(base); r[iz + k] = M
        cons.append((r, -np.inf, M))            # w + M z <= M
    for i in range(3):                          # freeness: one per fibre
        fib = {}
        for k, t in enumerate(T):
            key = tuple(t[j] for j in range(3) if j != i)
            fib.setdefault(key, []).append(k)
        for ks in fib.values():
            if len(ks) > 1:
                cons.append(({iz + k: 1 for k in ks}, -np.inf, 1))
    for i in range(3):                          # y_{i,x} <= sum of z over elements using x in leg i
        use = {}
        for k, t in enumerate(T):
            use.setdefault(t[i], []).append(k)
        for x in range(A):
            r = {iy + i * A + x: 1}
            for k in use.get(x, []):
                r[iz + k] = r.get(iz + k, 0) - 1
            cons.append((r, -np.inf, 0))
        r = {iL: 1}
        for x in range(A):
            r[iy + i * A + x] = -1
        cons.append((r, -np.inf, 0))            # L <= sum_x y_{i,x}
    Amat = lil_matrix((len(cons), N))
    lo, hi = [], []
    for row, (d, l, h) in enumerate(cons):
        for col, v in d.items():
            Amat[row, col] = v
        lo.append(l); hi.append(h)
    c = np.zeros(N); c[iL] = -1
    lb = np.r_[-B * np.ones(nu), np.zeros(nz + ny), 0]
    ub = np.r_[B * np.ones(nu), np.ones(nz + ny), A]
    res = milp(c, constraints=LinearConstraint(Amat.tocsr(), lo, hi),
               integrality=np.ones(N), bounds=Bounds(lb, ub),
               options={"time_limit": tl, "disp": False})
    out = {"D": D, "n": n, "B": B, "status": res.message, "optimal": res.status == 0,
           "mip_dual_bound_L": getattr(res, "mip_dual_bound", None)}
    if res.x is not None:
        x = np.round(res.x).astype(int)
        out["u"] = [x[i * A:(i + 1) * A].tolist() for i in range(3)]
        out["L"] = int(x[iL])
    return out


def maxmin_entropy(phi):
    import numpy as np
    from scipy.optimize import minimize
    n = len(phi)
    cols = [{} for _ in range(3)]
    for k, t in enumerate(phi):
        for j in range(3):
            cols[j].setdefault(t[j], []).append(k)
    groups = [list(c.values()) for c in cols]

    def H(p, j):
        s = 0.0
        for g in groups[j]:
            v = p[g].sum()
            if v > 1e-300:
                s -= v * math.log2(v)
        return s

    def mins(p):
        return min(H(p, j) for j in range(3))
    x0 = np.r_[np.ones(n) / n, 0.0]
    cons = [{"type": "eq", "fun": lambda x: x[:n].sum() - 1}]
    for j in range(3):
        cons.append({"type": "ineq", "fun": (lambda x, j=j: H(np.clip(x[:n], 0, 1), j) - x[n])})
    r = minimize(lambda x: -x[n], x0, constraints=cons, bounds=[(0, 1)] * n + [(0, 30)],
                 method="SLSQP", options={"maxiter": 1000, "ftol": 1e-12})
    p = np.clip(r.x[:n], 0, 1); p = p / p.sum()
    u0 = np.ones(n) / n
    return max(mins(p), mins(u0))


def verify(cert):
    D, n, u = cert["D"], cert["n"], cert["u"]
    T = Sn(D, n)
    w = {t: u[0][t[0]] + u[1][t[1]] + u[2][t[2]] for t in T}
    neg = [t for t in T if w[t] < 0]
    if neg:
        return {"ok": False, "why": f"negative weight on {neg[:3]}"}
    phi = sorted(t for t in T if w[t] == 0)
    for i in range(3):
        seen = {}
        for t in phi:
            key = tuple(t[j] for j in range(3) if j != i)
            if key in seen:
                return {"ok": False, "why": f"not free: {seen[key]} {t}"}
            seen[key] = t
    h = maxmin_entropy(phi)
    letters = [len({t[j] for t in phi}) for j in range(3)]
    return {"ok": True, "D": D, "n": n, "phi_size": len(phi), "letters_per_leg": letters,
            "maxmin_entropy_bits": h, "per_letter_bound_2^(h/n)": 2 ** (h / n),
            "single_letter_value": 3.0}


if __name__ == "__main__":
    if sys.argv[1] == "search":
        D, n = int(sys.argv[2]), int(sys.argv[3])
        tl = float(sys.argv[4]) if len(sys.argv) > 4 else 600.0
        B = int(sys.argv[5]) if len(sys.argv) > 5 else None
        print(json.dumps(search(D, n, tl, B)))
    elif sys.argv[1] == "verify":
        print(json.dumps(verify(json.load(open(sys.argv[2])))))
