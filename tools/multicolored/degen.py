#!/usr/bin/env python3
"""Free combinatorial degenerations of S_D, and the slice-rank lower bound they give.

docs/roadmap.md section 78. S_D = {(a,b,c) in [D]^3 : a = b = c, or a, b, c
pairwise distinct}. A combinatorial degeneration of S_D ([CVZ18] Def. 4.9) is
given by integer weights u1, u2, u3 : [D] -> Z with w(t) = u1(a)+u2(b)+u3(c) >= 0
on every t in S_D; its zero set Phi = {t in S_D : w(t) = 0}. Phi is *free*
([CVZ18] Def. 4.17) if no two of its elements differ in exactly one coordinate.
For such Phi and any distribution P on Phi, every tensor with support S_D has
asymptotic slice rank over C at least 2^(min_j H(P_j)) (section 78.1).

    search:  python3 -I tools/multicolored/degen.py search D [cap] [timelimit_s]
             MILP (scipy/HiGHS): maximise |Phi| subject to freeness and, if cap
             is given, at most `cap` elements of Phi per letter per coordinate.
    verify:  python3 -I tools/multicolored/degen.py verify CERT.json
             independent exact check of a certificate, sharing nothing with the
             search: recompute every weight in integers, the zero set, freeness;
             then compute max_P min_j H(P_j) over P on Phi.
"""
import itertools, json, math, sys


def S(D):
    return [t for t in itertools.product(range(D), repeat=3) if len(set(t)) in (1, 3)]


def search(D, cap=None, tl=600.0, B=None):
    import numpy as np
    from scipy.optimize import milp, LinearConstraint, Bounds
    B = B or 3 * D
    T = S(D)
    nu, nz = 3 * D, len(T)
    N = nu + nz                      # x = [u1(0..D-1), u2, u3, z_t ...]
    rows, lo, hi = [], [], []

    def row():
        return np.zeros(N)
    M = 3 * B + 1
    for k, t in enumerate(T):
        r = row()
        for i in range(3):
            r[i * D + t[i]] += 1
        # w_t >= 1 - z_t   i.e.  w_t + z_t >= 1
        r1 = r.copy(); r1[nu + k] = 1
        rows.append(r1); lo.append(1); hi.append(np.inf)
        # w_t <= M (1 - z_t)   i.e.  w_t + M z_t <= M
        r2 = r.copy(); r2[nu + k] = M
        rows.append(r2); lo.append(-np.inf); hi.append(M)
    idx = {t: k for k, t in enumerate(T)}
    for t in T:
        if len(set(t)) != 3:
            continue
        for i in range(3):
            for v in range(D):
                if v <= t[i]:
                    continue
                t2 = list(t); t2[i] = v; t2 = tuple(t2)
                if t2 in idx and len(set(t2)) == 3:
                    r = row(); r[nu + idx[t]] = 1; r[nu + idx[t2]] = 1
                    rows.append(r); lo.append(-np.inf); hi.append(1)
    if cap:
        for i in range(3):
            for v in range(D):
                r = row()
                for k, t in enumerate(T):
                    if t[i] == v:
                        r[nu + k] = 1
                rows.append(r); lo.append(-np.inf); hi.append(cap)
    c = np.zeros(N); c[nu:] = -1
    integrality = np.ones(N)
    bounds = Bounds(np.r_[-B * np.ones(nu), np.zeros(nz)], np.r_[B * np.ones(nu), np.ones(nz)])
    res = milp(c, constraints=LinearConstraint(np.array(rows), lo, hi),
               integrality=integrality, bounds=bounds,
               options={"time_limit": tl, "disp": False})
    if res.x is None:
        return {"D": D, "status": res.message}
    x = np.round(res.x).astype(int)
    u = [x[0:D].tolist(), x[D:2 * D].tolist(), x[2 * D:3 * D].tolist()]
    return {"D": D, "cap": cap, "status": res.message, "optimal": res.status == 0,
            "u": u, "phi_size_milp": int(round(-res.fun))}


def maxmin_entropy(phi):
    """max over distributions P on phi of min_j H(P_j), in bits. Concave in P;
    solved as max t s.t. H(P_j) >= t by SLSQP from the uniform start, then the
    returned P is re-evaluated exactly (the value reported is achieved by an
    explicit P, so it is a valid lower bound whatever the optimiser did)."""
    import numpy as np
    from scipy.optimize import minimize
    n = len(phi)

    def marg(p, j):
        m = {}
        for pk, t in zip(p, phi):
            m[t[j]] = m.get(t[j], 0.0) + pk
        return m

    def H(m):
        return -sum(v * math.log2(v) for v in m.values() if v > 1e-300)

    def mins(p):
        return min(H(marg(p, j)) for j in range(3))
    x0 = np.r_[np.ones(n) / n, 0.0]
    cons = [{"type": "eq", "fun": lambda x: x[:n].sum() - 1}]
    for j in range(3):
        cons.append({"type": "ineq", "fun": (lambda x, j=j: H(marg(np.clip(x[:n], 0, 1), j)) - x[n])})
    r = minimize(lambda x: -x[n], x0, constraints=cons, bounds=[(0, 1)] * n + [(0, 20)],
                 method="SLSQP", options={"maxiter": 500, "ftol": 1e-12})
    p = np.clip(r.x[:n], 0, 1); p = p / p.sum()
    best_p, best = (p, mins(p))
    u0 = np.ones(n) / n
    if mins(u0) > best:
        best_p, best = u0, mins(u0)
    return best, best_p.tolist()


def verify(cert):
    D, u = cert["D"], cert["u"]
    T = S(D)
    w = {t: u[0][t[0]] + u[1][t[1]] + u[2][t[2]] for t in T}
    neg = [t for t in T if w[t] < 0]
    if neg:
        return {"ok": False, "why": f"negative weight on {neg[:3]}"}
    phi = sorted(t for t in T if w[t] == 0)
    for a, b in itertools.combinations(phi, 2):
        if sum(x != y for x, y in zip(a, b)) == 1:
            return {"ok": False, "why": f"not free: {a} {b}"}
    h, p = maxmin_entropy(phi)
    letters = [len({t[j] for t in phi}) for j in range(3)]
    return {"ok": True, "D": D, "phi_size": len(phi), "letters_per_coord": letters,
            "rainbow": sum(1 for t in phi if len(set(t)) == 3),
            "maxmin_entropy_bits": h, "bound_2^h": 2 ** h, "phi": phi}


if __name__ == "__main__":
    if sys.argv[1] == "search":
        D = int(sys.argv[2])
        cap = int(sys.argv[3]) if len(sys.argv) > 3 and sys.argv[3] != "-" else None
        tl = float(sys.argv[4]) if len(sys.argv) > 4 else 600.0
        print(json.dumps(search(D, cap, tl)))
    elif sys.argv[1] == "verify":
        r = verify(json.load(open(sys.argv[2])))
        r.pop("phi", None) if len(r.get("phi", [])) > 40 else None
        print(json.dumps(r))
