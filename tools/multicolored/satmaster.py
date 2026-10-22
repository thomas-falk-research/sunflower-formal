#!/usr/bin/env python3
"""SAT master for the Benders search for free faces of S_D^(n).

docs/roadmap.md section 83. Same question as benders.py: is there Phi in
S_D^(n), free, with at most K uses of each word per leg, |Phi| >= s, and a
face (weights with w = 0 on Phi, w >= 1 elsewhere)? Same run classes: run r
forces the orbit representative with r monochromatic coordinates and
excludes triples with more.

The master is an incremental SAT solver (CaDiCaL 1.9.5 through PySAT), one
variable per triple. Its clauses, every one a consequence of the question:
  fibre      at most one element per fibre (pairwise)
  rect       Lemma 81.A pairs
  2+1        pairs (a, b) differing in every leg whose three single-leg swaps
             a[i <- b_i] all lie in S_D^(n): 2 v_a + v_b is the sum of the
             swaps, each of which shares a fibre with a (Lemma 83.A)
  conf3      conflict three-sets of Corollary 82.B
  force3     Horn clauses (not p1 or not p2 or not p3 or q) for the other
             relations of benders.relations3 (Lemma 82.A)
  cap, size  cardinality encodings (PySAT seqcounter / cardinality network)
  farkas     for each model that is not a face, the minimised Farkas
             certificate of benders.py as a clause, re-checked in exact
             rational arithmetic before it is added, with its images under
             the stabiliser of the forced triple
A model that is a face is reported with integer weights re-checked exactly.

    python3 -I tools/multicolored/satmaster.py D n K s [timelimit_s] [runs|-] [cnf_prefix]

Requires python-sat==1.9.dev15 (PySAT; pip), as well as numpy and highspy.

CaDiCaL cannot be interrupted through PySAT, so the time limit is checked
between solves only; a single long solve can overrun it, and a hard limit
must come from outside (e.g. timeout). One JSON progress line per solve goes
to stderr.

With cnf_prefix, each run class writes its clauses before any Farkas clause
to cnf_prefix_r<r>_base.cnf, and, if it ends unsatisfiable, its full clause
set to cnf_prefix_r<r>.cnf (DIMACS) and its Farkas certificates to
cnf_prefix_r<r>.certs.json, for an independent proof run and re-check.
"""
import itertools, json, os, sys, time
from fractions import Fraction

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import benders as B
from pysat.card import CardEnc, EncType
from pysat.solvers import Solver


def twoplusone(T):
    """Pairs {a, b} of Lemma 83.A (as sorted index pairs)."""
    Tn = np.array(T)
    N = len(T)
    A = int(Tn.max()) + 1
    inS = np.zeros((A, A, A), bool)
    inS[Tn[:, 0], Tn[:, 1], Tn[:, 2]] = True
    out = set()
    for a in range(N):
        x = Tn[a]
        diff = (Tn != x).all(1)
        ok = diff.copy()
        ok &= inS[Tn[:, 0], x[1], x[2]]          # a with leg 0 replaced by b_0
        ok &= inS[x[0], Tn[:, 1], x[2]]
        ok &= inS[x[0], x[1], Tn[:, 2]]
        for b in np.where(ok)[0]:
            out.add((min(a, int(b)), max(a, int(b))))
    return sorted(out)


def exact_farkas(T, A, lam, mu):
    """Exact check of a Farkas certificate on the supports lam (free sign)
    and mu (nonnegative): find a rational x != 0 with sum_t x_t v_t = 0,
    x_mu >= 0 and sum x_mu > 0. Uses the kernel of the incidence matrix on
    the supports; returns the multipliers {t: Fraction} or None."""
    cols = sorted(lam) + sorted(mu)
    m = len(cols)
    rows = []
    for i in range(3):
        for wd in range(A):
            r = [Fraction(1 if T[t][i] == wd else 0) for t in cols]
            if any(r):
                rows.append(r)
    # reduced row echelon form
    piv, rk = [], 0
    for c in range(m):
        p = next((i for i in range(rk, len(rows)) if rows[i][c] != 0), None)
        if p is None:
            continue
        rows[rk], rows[p] = rows[p], rows[rk]
        pv = rows[rk][c]
        rows[rk] = [v / pv for v in rows[rk]]
        for i in range(len(rows)):
            if i != rk and rows[i][c] != 0:
                f = rows[i][c]
                rows[i] = [a - f * b for a, b in zip(rows[i], rows[rk])]
        piv.append(c)
        rk += 1
    free = [c for c in range(m) if c not in piv]
    if len(free) != 1:
        return None                                     # not a single circuit
    x = [Fraction(0)] * m
    x[free[0]] = Fraction(1)
    for i, c in enumerate(piv):
        x[c] = -rows[i][free[0]]
    nl = len(lam)
    if sum(x[nl:]) < 0:
        x = [-v for v in x]
    if any(v < 0 for v in x[nl:]) or sum(x[nl:]) <= 0:
        return None
    # independent re-check of the identity
    for i in range(3):
        for wd in range(A):
            if sum(x[k] for k, t in enumerate(cols) if T[t][i] == wd) != 0:
                return None
    return dict(zip(cols, x))


class Clauses:
    """Collects clauses for the solver and, optionally, for a DIMACS file."""

    def __init__(self, solver, keep):
        self.s, self.keep, self.all, self.count = solver, keep, [], {}

    def add(self, kind, cl):
        self.s.add_clause(cl)
        self.count[kind] = self.count.get(kind, 0) + 1
        if self.keep:
            self.all.append(cl)


def build(D, n, K, s, r, keep=False):
    """The run class's solver with every clause before any Farkas clause."""
    t_run = time.time()
    T = B.Sn(D, n)
    A = D ** n
    N = len(T)
    mono = [B.nmono(D, n, t) for t in T]
    rep = next(k for k in range(N) if mono[k] == r)
    index = {t: k for k, t in enumerate(T)}
    H = [g for g in B.group_maps(D, n) if g(T[rep]) == T[rep]]
    v = lambda k: k + 1
    solver = Solver(name="cadical195")
    C = Clauses(solver, keep)
    C.add("unit", [v(rep)])
    for k in range(N):
        if mono[k] > r:
            C.add("unit", [-v(k)])
    for i in range(3):
        fib = {}
        for k, t in enumerate(T):
            fib.setdefault(tuple(t[j] for j in range(3) if j != i), []).append(k)
        for ks in fib.values():
            for a, b in itertools.combinations(ks, 2):
                C.add("fibre", [-v(a), -v(b)])
    for a, b in B.rectangle_conflicts(T):
        C.add("rect", [-v(a), -v(b)])
    for a, b in twoplusone(T):
        C.add("2+1", [-v(a), -v(b)])
    bad = B.incompatible(T)
    P, Q = B.relations3(T, A, bad)
    cf = B.conflicting3(T, P, Q, K, bad)
    for row in np.unique(np.sort(P[cf], 1), axis=0).tolist():
        C.add("conf3", [-v(k) for k in row])
    conf_sets = {tuple(x) for x in np.unique(np.sort(P[cf], 1), axis=0).tolist()}
    seenf = set()
    for p, q in zip(np.sort(P[~cf], 1).tolist(), Q[~cf].tolist()):
        if tuple(p) in conf_sets:
            continue
        for qq in set(q):
            if (tuple(p), qq) not in seenf:
                seenf.add((tuple(p), qq))
                C.add("force3", [-v(k) for k in p] + [v(qq)])
    del P, Q, cf, conf_sets, seenf
    top = N
    for i in range(3):
        use = {}
        for k, t in enumerate(T):
            use.setdefault(t[i], []).append(v(k))
        for lits in use.values():
            if len(lits) > K:
                enc = CardEnc.atmost(lits, bound=K, top_id=top, encoding=EncType.seqcounter)
                top = max(top, enc.nv)
                for cl in enc.clauses:
                    C.add("cap", cl)
    if s > N:
        C.add("size", [])                       # |Phi| >= s is impossible outright
    else:
        enc = CardEnc.atleast([v(k) for k in range(N)], bound=s, top_id=top, encoding=EncType.cardnetwrk)
        top = max(top, enc.nv)
        for cl in enc.clauses:
            C.add("size", cl)
    return {"D": D, "n": n, "K": K, "s": s, "r": r, "T": T, "A": A, "N": N, "mono": mono, "rep": rep,
            "index": index, "H": H, "solver": solver, "C": C, "top": top, "nbase": len(C.all),
            "certs": [], "seen": set(), "setup": round(time.time() - t_run, 1)}


def write_cnf(path, top, clauses):
    with open(path, "w") as f:
        f.write(f"p cnf {top} {len(clauses)}\n")
        for cl in clauses:
            f.write(" ".join(map(str, cl)) + " 0\n")


def solve_loop(st, assumptions, tl, t0, tag=None):
    """The Benders loop under the given assumptions. Farkas clauses are valid
    for every face, so they stay in st for later calls."""
    T, A, N, H, index, C, solver = st["T"], st["A"], st["N"], st["H"], st["index"], st["C"], st["solver"]
    r, certs, seen = st["r"], st["certs"], st["seen"]
    v = lambda k: k + 1
    nsolve, ncert0 = 0, len(certs)
    mean = lambda: (sum(len(a) + len(b) for a, b in certs) / len(certs)) if certs else None
    common = lambda: {"run": r, "setup_s": st["setup"], "solves": nsolve, "clauses": dict(C.count),
                      "farkas_certs": len(certs)}
    while True:
        left = tl - (time.time() - t0)
        if left <= 0:
            return {**common(), "status": "time", "mean_cert_size": mean()}
        ts = time.time()
        res = solver.solve(assumptions=assumptions)   # CaDiCaL in PySAT cannot be interrupted
        nsolve += 1
        line = {"run": r, "solve": nsolve, "result": res, "farkas_certs": len(certs),
                "solve_s": round(time.time() - ts, 2), "elapsed_s": round(time.time() - t0, 1)}
        if tag is not None:
            line["cube"] = tag
        print(json.dumps(line), file=sys.stderr, flush=True)
        if res is False:
            return {**common(), "status": "infeasible", "mean_cert_size": mean(),
                    "new_certs": len(certs) - ncert0}
        model = solver.get_model()
        phi = {k for k in range(N) if model[k] > 0}
        ts = time.time()
        cert = B.farkas(T, A, phi)
        if cert is None:
            u = B.face_weights(T, A, phi)
            return {**common(), "status": "found" if u else "face, no integer certificate",
                    "phi_size": len(phi), "phi": sorted(phi),
                    "cert": {"D": st["D"], "n": st["n"], "u": u} if u else None}
        lam, mu = B.minimise(T, A, phi, *cert)
        if exact_farkas(T, A, lam, mu) is None:
            # the floating-point certificate does not survive the exact check:
            # add nothing for it, and stop rather than loop on the same model
            return {**common(), "status": "inexact certificate", "lam": sorted(lam), "mu": sorted(mu)}
        certs.append((lam, mu))
        print(json.dumps({"run": r, "cut": len(certs), "lam": len(lam), "mu": len(mu),
                          "lp_s": round(time.time() - ts, 2)}), file=sys.stderr, flush=True)
        for g in H:
            gl = frozenset(index[g(T[k])] for k in lam)
            gm = frozenset(index[g(T[k])] for k in mu)
            if (gl, gm) in seen:
                continue
            seen.add((gl, gm))
            C.add("farkas", [-v(k) for k in gl] + [v(k) for k in gm])


def run_one(D, n, K, s, r, tl, t0, cnf_prefix=None):
    st = build(D, n, K, s, r, keep=cnf_prefix is not None)
    if cnf_prefix:                              # the clauses before any Farkas clause
        write_cnf(f"{cnf_prefix}_r{r}_base.cnf", st["top"], st["C"].all)
    out = solve_loop(st, [], tl, t0)
    out.pop("new_certs", None)
    if out["status"] == "infeasible" and cnf_prefix:
        path = f"{cnf_prefix}_r{r}.cnf"
        write_cnf(path, st["top"], st["C"].all)
        with open(f"{cnf_prefix}_r{r}.certs.json", "w") as f:
            json.dump({"D": D, "n": n, "K": K, "s": s, "run": r,
                       "certs": [[sorted(a), sorted(b)] for a, b in st["certs"]]}, f)
        out["cnf"] = path
    return out


if __name__ == "__main__":
    D, n, K, s = (int(x) for x in sys.argv[1:5])
    tl = float(sys.argv[5]) if len(sys.argv) > 5 else 600.0
    runs = ([int(x) for x in sys.argv[6].split(",")] if len(sys.argv) > 6 and sys.argv[6] != "-"
            else list(range(n, -1, -1)))
    prefix = sys.argv[7] if len(sys.argv) > 7 else None
    t0 = time.time()
    out = {"D": D, "n": n, "K": K, "s": s, "runs": []}
    for r in runs:
        res = run_one(D, n, K, s, r, tl, t0, prefix)
        out["runs"].append(res)
        if res["status"] != "infeasible":
            break
    out["seconds"] = round(time.time() - t0, 1)
    sts = [x["status"] for x in out["runs"]]
    out["verdict"] = ("found" if "found" in sts else
                      "face found, not certified" if "face, no integer certificate" in sts else
                      "none (all runs infeasible)" if len(sts) == len(runs) and all(x == "infeasible" for x in sts)
                      else "undecided")
    print(json.dumps(out))
