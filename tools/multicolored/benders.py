#!/usr/bin/env python3
"""Combinatorial Benders search for free combinatorial degenerations of S_D^(n).

docs/roadmap.md section 81. Question: is there Phi subset of S_D^(n) with
  (a) Phi free: at most one element per fibre (leg i, the other two words);
  (b) each word used at most K times in each leg;
  (c) |Phi| >= s;
  (d) Phi a face: weights u with w = 0 on Phi and w >= 1 on S_D^(n) \\ Phi?
With s = 3^n K + 1 the uniform distribution on Phi has every marginal
entropy above n log2 3, so SR_C(q_c) > 3 per letter (sections 79, 80).

Master (HiGHS MILP through highspy): binary z_t with (a), (b), (c), symmetry
breaking, the rectangle-conflict rows of Lemma 81.A, and the cuts found so
far. Subproblem: for the master's Phi solve
the Farkas system
    sum_{t in Phi} lambda_t v_t + sum_{t notin Phi} mu_t v_t = 0,
    mu >= 0, sum mu >= 1, minimise sum |lambda| + sum mu,
where v_t is the 0/1 incidence vector of t's three words. It is feasible
iff (d) fails; then every Phi' containing supp(lambda) and avoiding
supp(mu) fails (d) by the same certificate, giving the no-good cut
    sum_{supp lambda} (1 - z_t) + sum_{supp mu} z_t >= 1.
If the Farkas system is infeasible, (d) holds: the face LP is solved, its
weights scaled and rounded to integers, and the zero set and nonnegativity
re-checked in exact integers before it is reported. Freeness comes from the
master; tools/multicolored/degen2.py verify re-checks all three from scratch.

Symmetry: run r forces the orbit representative with r monochromatic
coordinates into Phi and forbids triples with more (as in bmatch.py); the
union of the runs is the whole search.

    python3 -I tools/multicolored/benders.py D n K s [timelimit_s] [runs]
A run ends "infeasible" when the master becomes infeasible: then no Phi
exists in that run (up to the floating LP verdicts behind each cut).
"""
import itertools, json, sys, time

import numpy as np
import highspy


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
    x, y, z = t
    c = 0
    for _ in range(n):
        if x % D == y % D == z % D:
            c += 1
        x, y, z = x // D, y // D, z // D
    return c


def rectangle_conflicts(T):
    """Pairs {a, b} that cannot both lie in a free face (Lemma 81.A in
    docs/roadmap.md): for a leg i with a_i != b_i, let c = a with leg i
    replaced by b_i and d = b with leg i replaced by a_i. If c and d are in
    S_D^(n), then w(a) + w(b) = w(c) + w(d) for every weight, so a, b in Phi
    forces c, d in Phi, and c differs from a in exactly leg i: not free."""
    inS = set(T)
    idx = {t: k for k, t in enumerate(T)}
    out = []
    for ka in range(len(T)):
        a = T[ka]
        for kb in range(ka + 1, len(T)):
            b = T[kb]
            for i in range(3):
                if a[i] == b[i]:
                    continue
                c = list(a); c[i] = b[i]; c = tuple(c)
                d = list(b); d[i] = a[i]; d = tuple(d)
                if c in inS and d in inS:
                    out.append((ka, kb))
                    break
    return out


def quiet():
    h = highspy.Highs()
    h.setOptionValue("output_flag", False)
    return h


def farkas(T, A, phi_set, lam_allowed=None, mu_allowed=None):
    """Return (lambda_support, mu_support) of a sparse certificate that phi
    is not a face, or None if none exists. lam_allowed / mu_allowed restrict
    the supports (used by the deletion filter)."""
    N = len(T)
    cols = []                                  # (kind, t index)
    for k in range(N):
        if k in phi_set:
            if lam_allowed is None or k in lam_allowed:
                cols.append(("lp", k)); cols.append(("lm", k))
        else:
            if mu_allowed is None or k in mu_allowed:
                cols.append(("mu", k))
    nc = len(cols)
    h = quiet()
    lp = highspy.HighsLp()
    lp.num_col_, lp.num_row_ = nc, 3 * A + 1
    lp.col_cost_ = np.ones(nc)
    lp.col_lower_ = np.zeros(nc)
    lp.col_upper_ = np.full(nc, highspy.kHighsInf)
    rl = np.zeros(3 * A + 1); ru = np.zeros(3 * A + 1)
    rl[-1], ru[-1] = 1.0, highspy.kHighsInf     # sum mu >= 1
    lp.row_lower_, lp.row_upper_ = rl, ru
    start, index, value = [0], [], []
    for kind, k in cols:
        sgn = -1.0 if kind == "lm" else 1.0
        t = T[k]
        for i in range(3):
            index.append(i * A + t[i]); value.append(sgn)
        if kind == "mu":
            index.append(3 * A); value.append(1.0)
        start.append(len(index))
    lp.a_matrix_.format_ = highspy.MatrixFormat.kColwise
    lp.a_matrix_.start_ = np.array(start, dtype=np.int32)
    lp.a_matrix_.index_ = np.array(index, dtype=np.int32)
    lp.a_matrix_.value_ = np.array(value)
    h.passModel(lp)
    h.run()
    st = h.getModelStatus()
    if st == highspy.HighsModelStatus.kInfeasible:
        return None
    if st != highspy.HighsModelStatus.kOptimal:
        raise RuntimeError(f"Farkas LP status {st}")
    x = h.getSolution().col_value
    lam, mu = set(), set()
    for (kind, k), v in zip(cols, x):
        if v > 1e-9:
            (mu if kind == "mu" else lam).add(k)
    return lam, mu


def minimise(T, A, phi, lam, mu):
    """Deletion filter: drop elements from the certificate's supports while a
    certificate on the smaller supports still exists. The result is a
    minimal certificate (no single element can be removed)."""
    lam, mu = set(lam), set(mu)
    for e in sorted(lam | mu):
        L = lam - {e}; M = mu - {e}
        if not M:
            continue
        c = farkas(T, A, phi, L, M)
        if c is not None:
            lam, mu = c
    return lam, mu


def group_maps(D, n):
    """Sym(D)^n x| S_n x S_3 on triples of encoded words (as in bmatch.py)."""
    def digits(w):
        out = []
        for _ in range(n):
            out.append(w % D); w //= D
        return out[::-1]

    def enc(ds):
        w = 0
        for d in ds:
            w = w * D + d
        return w
    words = range(D ** n)
    dig = [digits(w) for w in words]
    for sigmas in itertools.product(itertools.permutations(range(D)), repeat=n):
        for pi in itertools.permutations(range(n)):
            wmap = [enc([sigmas[k][dig[w][pi[k]]] for k in range(n)]) for w in words]
            for rho in itertools.permutations(range(3)):
                yield (lambda t, wmap=wmap, rho=rho:
                       (wmap[t[rho[0]]], wmap[t[rho[1]]], wmap[t[rho[2]]]))


def face_weights(T, A, phi_set):
    """Integer weights realising phi as a face (w = 0 on phi, >= 1 elsewhere)."""
    N = len(T)
    h = quiet()
    lp = highspy.HighsLp()
    lp.num_col_, lp.num_row_ = 3 * A, N
    lp.col_cost_ = np.zeros(3 * A)
    lp.col_lower_ = np.full(3 * A, -1e6); lp.col_upper_ = np.full(3 * A, 1e6)
    rl = np.array([0.0 if k in phi_set else 1.0 for k in range(N)])
    ru = np.array([0.0 if k in phi_set else highspy.kHighsInf for k in range(N)])
    lp.row_lower_, lp.row_upper_ = rl, ru
    start, index, value = [0], [], []
    for t in T:
        for i in range(3):
            index.append(i * A + t[i]); value.append(1.0)
        start.append(len(index))
    lp.a_matrix_.format_ = highspy.MatrixFormat.kRowwise
    lp.a_matrix_.start_ = np.array(start, dtype=np.int32)
    lp.a_matrix_.index_ = np.array(index, dtype=np.int32)
    lp.a_matrix_.value_ = np.array(value)
    h.passModel(lp)
    h.run()
    x = np.array(h.getSolution().col_value)
    for q in (1, 2, 4, 8, 16, 64, 256, 1024):
        u = np.rint(x * q).astype(int)
        w = [int(u[t[0]] + u[A + t[1]] + u[2 * A + t[2]]) for t in T]
        if all((w[k] == 0) == (k in phi_set) and w[k] >= 0 for k in range(N)):
            return [u[i * A:(i + 1) * A].tolist() for i in range(3)]
    return None


def run_one(D, n, K, s, r, tl, t0):
    T = Sn(D, n)
    A = D ** n
    N = len(T)
    mono = [nmono(D, n, t) for t in T]
    rep = next(k for k in range(N) if mono[k] == r)
    index = {t: k for k, t in enumerate(T)}
    H = [g for g in group_maps(D, n) if g(T[rep]) == T[rep]]
    seen_cuts = set()
    allowed = [mono[k] <= r for k in range(N)]
    m = quiet()
    m.setOptionValue("mip_rel_gap", 0.0)
    inf = highspy.kHighsInf
    for k in range(N):
        lo = 1.0 if k == rep else 0.0
        hi = 1.0 if allowed[k] else 0.0
        m.addVar(lo, hi)
    m.changeColsIntegrality(N, np.arange(N, dtype=np.int32),
                            np.array([highspy.HighsVarType.kInteger] * N))

    def add_row(lo, hi, idx, val):
        m.addRow(lo, hi, len(idx), np.array(idx, dtype=np.int32), np.array(val, dtype=float))
    for i in range(3):                          # (a) freeness: one per fibre
        fib = {}
        for k, t in enumerate(T):
            fib.setdefault(tuple(t[j] for j in range(3) if j != i), []).append(k)
        for ks in fib.values():
            if len(ks) > 1:
                add_row(-inf, 1.0, ks, [1.0] * len(ks))
    for i in range(3):                          # (b) cap K per word per leg
        use = {}
        for k, t in enumerate(T):
            use.setdefault(t[i], []).append(k)
        for ks in use.values():
            add_row(-inf, float(K), ks, [1.0] * len(ks))
    add_row(float(s), inf, list(range(N)), [1.0] * N)   # (c) size
    conf = rectangle_conflicts(T)                       # Lemma 81.A
    for ka, kb in conf:
        add_row(-inf, 1.0, [ka, kb], [1.0, 1.0])
    cuts, sizes, lm = 0, [], []
    while True:
        if time.time() - t0 > tl:
            return {"run": r, "status": "time", "cuts": cuts,
                    "mean_cut_size": (sum(sizes) / len(sizes)) if sizes else None,
                    "lam_mu_mean": (sum(a for a, _ in lm) / len(lm), sum(b for _, b in lm) / len(lm)) if lm else None}
        m.setOptionValue("time_limit", max(1.0, tl - (time.time() - t0)))
        m.run()
        st = m.getModelStatus()
        if st == highspy.HighsModelStatus.kInfeasible:
            return {"run": r, "status": "infeasible", "cuts": cuts, "rect_conflicts": len(conf),
                    "mean_cut_size": (sum(sizes) / len(sizes)) if sizes else None,
                    "max_cut_size": max(sizes) if sizes else None}
        if st != highspy.HighsModelStatus.kOptimal:
            return {"run": r, "status": f"master {st}", "cuts": cuts}
        z = m.getSolution().col_value
        phi = {k for k in range(N) if z[k] > 0.5}
        cert = farkas(T, A, phi)
        if cert is None:
            u = face_weights(T, A, phi)
            return {"run": r, "status": "found", "cuts": cuts, "phi_size": len(phi),
                    "cert": {"D": D, "n": n, "u": u} if u else None}
        lam, mu = minimise(T, A, phi, *cert)
        sizes.append(len(lam) + len(mu))
        lm.append((len(lam), len(mu)))
        # the cut is a statement about S_D^(n) alone, so every image under the
        # symmetry group is valid; add the images under Stab(rep)
        for g in H:
            gl = frozenset(index[g(T[k])] for k in lam)
            gm = frozenset(index[g(T[k])] for k in mu)
            if (gl, gm) in seen_cuts:
                continue
            seen_cuts.add((gl, gm))
            idx = list(gl) + list(gm)
            val = [-1.0] * len(gl) + [1.0] * len(gm)
            add_row(1.0 - len(gl), inf, idx, val)   # sum_lam (1-z) + sum_mu z >= 1
            cuts += 1


if __name__ == "__main__":
    D, n, K, s = (int(v) for v in sys.argv[1:5])
    tl = float(sys.argv[5]) if len(sys.argv) > 5 else 600.0
    runs = [int(v) for v in sys.argv[6].split(",")] if len(sys.argv) > 6 else list(range(n, -1, -1))
    t0 = time.time()
    out = {"D": D, "n": n, "K": K, "s": s, "runs": []}
    for r in runs:
        res = run_one(D, n, K, s, r, tl, t0)
        out["runs"].append(res)
        if res["status"] == "found":
            break
    out["seconds"] = round(time.time() - t0, 1)
    sts = [x["status"] for x in out["runs"]]
    out["verdict"] = ("found" if "found" in sts else
                      "none (all runs infeasible)" if len(sts) == len(runs) and all(v == "infeasible" for v in sts)
                      else "undecided")
    print(json.dumps(out))
