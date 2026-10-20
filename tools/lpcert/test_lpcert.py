#!/usr/bin/env python3
"""Tests for tools/lpcert/lpcert.py, and its agreement with coq/LPCert.v.

  python3 tools/lpcert/test_lpcert.py            all but the Coq round trip
  python3 tools/lpcert/test_lpcert.py --coq      also compile exported certificates

1. The examples of coq/LPCertExamples.v, with the same verdicts.
2. 300 random small integer programs: the brute-force optimum `opt` over
   the box (its lower faces given as rows -x_i <= 0 in even trials and as
   nonnegativity declarations in odd ones); the solver proves c·x < opt + 1
   and the checker accepts;
   c·x < opt is refused by the solver (it finds an integer point) and no
   leaf the checker accepts exists for it at the root; infeasible ones are
   refuted with K = 0 leaves.
3. Tampering: one multiplier of each solved tree increased by one.  The
   checker agrees with an independent dense reference on every tampered
   tree; without declarations every one is rejected (an equality breaks);
   with declarations the extra slack may leave a valid proof of the same
   true claim, which both accept.  Trees that use a declaration are
   rejected without it.
4. (--coq) Branching certificates exported to Coq (one without and one
   with declarations) compile; the same with one multiplier changed do not.
"""
import itertools, json, os, random, subprocess, sys, tempfile, copy
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import lpcert as L

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
fails = 0


def expect(cond, what):
    global fails
    if not cond:
        fails += 1
        print("FAIL:", what)


# 1. the Coq examples
rows1 = [[[[0, 1], [1, 1]], 1], [[[0, -1]], 0], [[[1, -1]], 0]]
c1 = [[0, 1], [1, 1]]
t1 = {"leaf": {"K": 1, "y": [[["base", 0], 1]]}}
rows2 = [[[[0, 2]], 1], [[[0, -2]], -1]]
t2 = {"branch": [[0, 1]], "f": 0,
      "le": {"leaf": {"K": 0, "y": [[["br", 0], 2], [["base", 1], 1]]}},
      "ge": {"leaf": {"K": 0, "y": [[["base", 0], 1], [["br", 0], 2]]}}}
P1 = {"n": 2, "rows": rows1, "c": c1, "T": 2}
P2 = {"n": 1, "rows": rows2, "c": [], "T": 0}
expect(L.check(P1, t1), "ex1_ok")
expect(L.check(P2, t2), "ex2_ok")
expect(not L.check(P2, {"leaf": {"K": 0, "y": [[["base", 0], 1], [["base", 1], 1]]}}), "ex2_no_single_leaf")
bad = copy.deepcopy(t2); bad["le"]["leaf"]["y"][0][1] = 1
expect(not L.check(P2, bad), "rej_coefficient")
expect(not L.check({**P1, "T": 1}, {"leaf": {"K": 1, "y": [[["base", 0], 1], [["base", 1], -1]]}}), "rej_negative")
expect(not L.check(P1, {"leaf": {"K": -1, "y": [[["base", 0], -1]]}}), "rej_scale")
expect(not L.check({**P1, "T": 1}, t1), "rej_bound")
expect(not L.check({**P1, "n": 1}, t1), "rej_dimension")
expect(not L.check(P2, {"leaf": {"K": 0, "y": [[["br", 5], 1]]}}), "rej_phantom_branch")
P3 = {"n": 2, "rows": [[[[0, 1], [1, 1]], 1]], "c": [[0, 1]], "T": 2, "nonneg": [1]}
t3 = {"leaf": {"K": 1, "y": [[["base", 0], 1]]}}
expect(L.check(P3, t3), "ex3_ok")
expect(not L.check({**P3, "nonneg": []}, t3), "rej_undeclared")
expect(not L.check({**P3, "nonneg": [0]}, t3), "rej_wrong_declared")
print("examples: done")

# 2-3. random programs against brute force
rng = random.Random(20261013)
solved = branched = infeasible = 0
trees = []
for trial in range(300):
    n = rng.randint(1, 3)
    box = 3
    rows = []
    declare = trial % 2 == 1
    for i in range(n):
        if not declare:
            rows.append([[[i, -1]], 0])
        rows.append([[[i, 1]], box])
    for _ in range(rng.randint(1, 3)):
        a = [[i, rng.randint(-4, 4)] for i in range(n)]
        a = [p for p in a if p[1]]
        if not a:
            continue
        rows.append([a, rng.randint(-3, 8)])
    c = [[i, rng.randint(-3, 3)] for i in range(n)]
    c = [p for p in c if p[1]] or [[0, 1]]
    pts = [x for x in itertools.product(range(box + 1), repeat=n)
           if all(sum(v * x[i] for i, v in a) <= b for a, b in rows)]
    if not pts:
        P = {"n": n, "rows": rows, "c": [], "T": 0, "nonneg": list(range(n)) if declare else []}
        t = L.solve(P)
        expect(L.check(P, t), f"infeasible {trial}")
        infeasible += 1; trees.append((P, t)); continue
    opt = max(sum(v * x[i] for i, v in c) for x in pts)
    P = {"n": n, "rows": rows, "c": c, "T": opt + 1, "nonneg": list(range(n)) if declare else []}
    t = L.solve(P)
    expect(L.check(P, t), f"bound {trial}")
    solved += 1; branched += "branch" in t; trees.append((P, t))
    try:
        L.solve({**P, "T": opt})
        expect(False, f"false claim proved {trial}")
    except L.CertError:
        pass
    # no root leaf can certify the false claim: the LP optimum is >= opt
    expect(L._leaf(n, c, opt, [(a, b) for a, b in rows], [], False, frozenset(P["nonneg"])) is None,
           f"false root leaf {trial}")

def ref_tree(P, node, path=()):
    """An independent dense re-implementation of the acceptance condition
    (no shared code with lpcert.py), used to judge tampered trees."""
    n = P["n"]; nn = set(P.get("nonneg", []))
    def dense(v):
        if any(not (0 <= i < n) for i, _ in v):
            return None
        d = [0] * n
        for i, a in v:
            d[i] += a
        return d
    if "branch" in node:
        a, f = node["branch"], node["f"]
        return (ref_tree(P, node["le"], path + ((a, f),))
                and ref_tree(P, node["ge"], path + (([[i, -x] for i, x in a], -f - 1),)))
    K, ys = node["leaf"]["K"], node["leaf"]["y"]
    cd = dense(P["c"])
    if K < 0 or cd is None:
        return False
    tot = [0] * n; rhs = 0
    for (kind, k), y in ys:
        src = P["rows"] if kind == "base" else path
        a, b = src[k] if 0 <= k < len(src) else ([], 0)
        ad = dense(a)
        if y < 0 or ad is None:
            return False
        tot = [u + y * v for u, v in zip(tot, ad)]; rhs += y * b
    return (all((K * cd[j] <= tot[j]) if j in nn else (K * cd[j] == tot[j]) for j in range(n))
            and rhs < K * P["T"])


tampered = still_valid = 0
for P, t in trees:
    def leaves(node):
        if "leaf" in node:
            yield node
        else:
            yield from leaves(node["le"]); yield from leaves(node["ge"])
    for lf in leaves(t):
        for idx, (tag, y) in enumerate(lf["leaf"]["y"]):
            row = L.rget([(a, b) for a, b in P["rows"]], [], tag) if tag[0] == "base" else None
            if row is not None and not any(v for _, v in row[0]):
                continue
            lf["leaf"]["y"][idx][1] = y + 1
            acc = L.check(P, t)
            # the two implementations agree; without declarations a changed
            # multiplier always breaks an equality, so it must be rejected;
            # with them, extra slack can leave a valid proof of the same
            # (true, brute-forced) claim
            expect(acc == ref_tree(P, t), "checker and reference disagree on a tampered tree")
            expect(not acc or P["nonneg"], "tampered certificate accepted without declarations")
            still_valid += acc
            tampered += 1
            lf["leaf"]["y"][idx][1] = y
            break
# a tree accepted only with the declarations is rejected without them
needed = 0
for P, t in trees:
    if P["nonneg"] and not L.check({**P, "nonneg": []}, t):
        needed += 1
expect(needed > 0, "no certificate depended on its nonnegativity declarations")
for P, t in trees:
    expect(ref_tree(P, t), "reference rejects a solved tree")
print(f"random: {solved} bounds ({branched} needing branches), {infeasible} infeasible; "
      f"{tampered} tamperings, {tampered - still_valid} rejected, {still_valid} still valid proofs "
      f"(declared programs, agreeing with the reference); "
      f"{needed} certificates rejected without their declarations")

# 4. Coq round trip
if "--coq" in sys.argv:
    cases = []
    for decl in (False, True):
        P, t = next((P, t) for P, t in trees if "branch" in t and P["c"] and bool(P["nonneg"]) == decl
                    and (not decl or not L.check({**P, "nonneg": []}, t)))
        sfx = "_nn" if decl else ""
        cases += [(P, f"rt_ok{sfx}", t, 0), (P, f"rt_bad{sfx}", None, 1)]
        if decl:
            cases.append(({**P, "nonneg": []}, "rt_undeclared", t, 1))
    with tempfile.TemporaryDirectory() as d:
        for P, name, tree, want in cases:
            if tree is None:
                t = next(tt for PP, nm, tt, w in cases if PP is P and tt is not None)
                tree = copy.deepcopy(t)
                node = tree
                while "leaf" not in node:
                    node = node["le"]
                node["leaf"]["y"][0][1] += 1
            path = os.path.join(d, f"{name}.v")
            open(path, "w").write(L.to_coq(P, tree, name))
            r = subprocess.run(["coqc", "-q", "-Q", os.path.join(ROOT, "coq"), "Sunflower", "-R", d, "T", path],
                               capture_output=True, text=True)
            expect((r.returncode == 0) == (want == 0), f"coq round trip {name}: rc {r.returncode} {r.stderr[-300:]}")
    print("coq round trip: done")

print("ALL PASS" if fails == 0 else f"{fails} FAILURES")
sys.exit(1 if fails else 0)
