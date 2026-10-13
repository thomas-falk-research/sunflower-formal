#!/usr/bin/env python3
"""Tests for tools/lpcert/lpcert.py, and its agreement with coq/LPCert.v.

  python3 tools/lpcert/test_lpcert.py            all but the Coq round trip
  python3 tools/lpcert/test_lpcert.py --coq      also compile exported certificates

1. The examples of coq/LPCertExamples.v, with the same verdicts.
2. 300 random small integer programs: the brute-force optimum `opt` over
   the box; the solver proves c·x < opt + 1 and the checker accepts;
   c·x < opt is refused by the solver (it finds an integer point) and no
   leaf the checker accepts exists for it at the root; infeasible ones are
   refuted with K = 0 leaves.
3. Tampering: every solved tree with one multiplier changed is rejected.
4. (--coq) A branching certificate exported to Coq compiles; the same with
   one multiplier changed does not.
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
print("examples: done")

# 2-3. random programs against brute force
rng = random.Random(20261013)
solved = branched = infeasible = 0
trees = []
for trial in range(300):
    n = rng.randint(1, 3)
    box = 3
    rows = []
    for i in range(n):
        rows.append([[[i, -1]], 0]); rows.append([[[i, 1]], box])
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
        P = {"n": n, "rows": rows, "c": [], "T": 0}
        t = L.solve(P)
        expect(L.check(P, t), f"infeasible {trial}")
        infeasible += 1; trees.append((P, t)); continue
    opt = max(sum(v * x[i] for i, v in c) for x in pts)
    P = {"n": n, "rows": rows, "c": c, "T": opt + 1}
    t = L.solve(P)
    expect(L.check(P, t), f"bound {trial}")
    solved += 1; branched += "branch" in t; trees.append((P, t))
    try:
        L.solve({**P, "T": opt})
        expect(False, f"false claim proved {trial}")
    except L.CertError:
        pass
    # no root leaf can certify the false claim: the LP optimum is >= opt
    expect(L._leaf(n, c, opt, [(a, b) for a, b in rows], [], False) is None, f"false root leaf {trial}")

tampered = 0
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
            expect(not L.check(P, t), "tampered certificate accepted")
            lf["leaf"]["y"][idx][1] = y
            tampered += 1
            break
print(f"random: {solved} bounds ({branched} needing branches), {infeasible} infeasible, {tampered} tamperings rejected")

# 4. Coq round trip
if "--coq" in sys.argv:
    P, t = next((P, t) for P, t in trees if "branch" in t and P["c"])
    with tempfile.TemporaryDirectory() as d:
        for name, tree, want in (("rt_ok", t, 0), ("rt_bad", None, 1)):
            if tree is None:
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
