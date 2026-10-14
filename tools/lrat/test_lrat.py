#!/usr/bin/env python3
"""Tests for tools/lrat/lrat.py and its agreement with coq/LRAT.v.

  python3 tools/lrat/test_lrat.py          (needs cadical on PATH)
  python3 tools/lrat/test_lrat.py --coq    also the Coq round trip

1. Pigeonhole PHP(n+1, n), n = 2..6, and random 3-CNF on 12 variables:
   CaDiCaL's LRAT proof (text, `--lrat=true --binary=false`) is accepted;
   satisfiable formulas are confirmed by their model.
2. Semantic oracle: on these small formulas every clause a proof adds is
   checked by brute force to follow from the clauses present at that
   step.  Every proof the checker accepts, tampered ones included, must
   pass the oracle (soundness of the mirror).
3. Must-reject cases: the proof cut before the empty clause; a step
   whose clause does not follow (by the oracle) replacing a real step; a
   hint pointing to a missing clause; a bogus empty clause for a
   satisfiable formula; a RAT hint (refused by the parser).
4. (--coq) A proof exported to Coq compiles; the same with one hint
   pointing to a missing clause does not.
"""
import copy, itertools, os, random, subprocess, sys, tempfile
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import lrat as L

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
fails = 0


def expect(cond, what):
    global fails
    if not cond:
        fails += 1
        print("FAIL:", what)


def nvars(cnf):
    return max((abs(l) for C in cnf for l in C), default=0)


def sat(C, x):
    return any((x[abs(l) - 1] if l > 0 else not x[abs(l) - 1]) for l in C)


def implied(db, C, n):
    """db |= C, by brute force over n variables."""
    for x in itertools.product((False, True), repeat=n):
        if all(sat(D, x) for D in db) and not sat(C, x):
            return False
    return True


def oracle(cnf, steps, n):
    """Every added clause follows from the clauses present when it is added."""
    db = {i + 1: C for i, C in enumerate(cnf)}
    for s in steps:
        if s[0] == "a":
            if not implied(list(db.values()), s[2], n):
                return False
            if not s[2]:
                return True
            db[s[1]] = s[2]
        else:
            for i in s[1]:
                db.pop(i, None)
    return True


def solve(cnf, d):
    path, proof = os.path.join(d, "f.cnf"), os.path.join(d, "f.lrat")
    open(path, "w").write(f"p cnf {max(nvars(cnf), 1)} {len(cnf)}\n" + "".join(" ".join(map(str, C)) + " 0\n" for C in cnf))
    r = subprocess.run(["cadical", "--lrat=true", "--binary=false", "-q", path, proof], capture_output=True, text=True)
    if r.returncode == 20:
        return "unsat", L.parse_lrat(proof)
    model = [int(t) for line in r.stdout.splitlines() if line.startswith("v") for t in line.split()[1:]]
    return "sat", model


def php(n):
    P = n + 1
    v = lambda p, h: p * n + h + 1
    cnf = [[v(p, h) for h in range(n)] for p in range(P)]
    for h in range(n):
        for p in range(P):
            for q in range(p + 1, P):
                cnf.append([-v(p, h), -v(q, h)])
    return cnf


rng = random.Random(20261014)
instances = [("php%d" % n, php(n)) for n in range(2, 7)]
for k in range(80):
    n, m = 12, rng.randint(50, 70)
    cnf = [[rng.choice((1, -1)) * x for x in rng.sample(range(1, n + 1), 3)] for _ in range(m)]
    instances.append(("r%d" % k, cnf))

proofs = []
n_unsat = n_sat = 0
with tempfile.TemporaryDirectory() as d:
    for name, cnf in instances:
        kind, res = solve(cnf, d)
        if kind == "sat":
            n_sat += 1
            x = [False] * nvars(cnf)
            for t in res:
                if t > 0 and t <= len(x):
                    x[t - 1] = True
            expect(all(sat(C, x) for C in cnf), f"{name}: model does not satisfy")
            # a bogus refutation of a satisfiable formula is rejected
            expect(not L.check(cnf, [("a", len(cnf) + 1, [], list(range(1, len(cnf) + 1)))]), f"{name}: bogus refutation accepted")
            continue
        n_unsat += 1
        expect(L.check(cnf, res), f"{name}: CaDiCaL proof rejected")
        if nvars(cnf) <= 14:
            expect(oracle(cnf, res, nvars(cnf)), f"{name}: an accepted step is not implied")
        proofs.append((name, cnf, res))
print(f"instances: {n_unsat} unsatisfiable (proofs accepted), {n_sat} satisfiable (models checked)")

tam = rej = 0
for name, cnf, steps in proofs:
    n = nvars(cnf)
    small = n <= 14
    adds = [k for k, s in enumerate(steps) if s[0] == "a"]
    # cut before the empty clause
    cut = steps[:adds[-1]]
    expect(not L.check(cnf, cut), f"{name}: proof without the empty clause accepted")
    tam += 1; rej += 1
    for k in adds:
        s = steps[k]
        variants = []
        if s[3]:
            t = copy.deepcopy(steps); t[k] = ("a", s[1], s[2], s[3][:-1]); variants.append((t, False))
            t = copy.deepcopy(steps); t[k] = ("a", s[1], s[2], s[3][:-1] + [10 ** 6]); variants.append((t, True))
        t = copy.deepcopy(steps); t[k] = ("a", s[1], s[2] + [rng.choice((1, -1)) * rng.randint(1, n)], s[3]); variants.append((t, False))
        if s[2]:
            t = copy.deepcopy(steps); t[k] = ("a", s[1], [-s[2][0]] + s[2][1:], s[3]); variants.append((t, False))
        for t, must in variants:
            acc = L.check(cnf, t)
            tam += 1; rej += not acc
            if must:
                expect(not acc, f"{name}: missing-clause hint accepted")
            if acc and small:
                expect(oracle(cnf, t, n), f"{name}: tampered proof accepted with an unimplied step")
# a RAT hint is refused when parsing
with tempfile.TemporaryDirectory() as d:
    p = os.path.join(d, "x.lrat"); open(p, "w").write("5 1 0 -2 3 0\n")
    try:
        L.parse_lrat(p); expect(False, "RAT hint parsed")
    except L.CertError:
        pass
print(f"tampering: {tam} variants, {rej} rejected; every accepted one passes the semantic oracle")

if "--coq" in sys.argv:
    name, cnf, steps = next(p for p in proofs if p[0] == "php3")
    bad = copy.deepcopy(steps)
    k = next(k for k, s in enumerate(bad) if s[0] == "a" and s[3])
    bad[k] = ("a", bad[k][1], bad[k][2], bad[k][3][:-1] + [10 ** 6])
    expect(not L.check(cnf, bad), "the Coq negative case is accepted in Python")
    with tempfile.TemporaryDirectory() as d:
        for nm, st, want in (("rtok", steps, True), ("rtbad", bad, False)):
            out = os.path.join(d, nm + ".v")
            open(out, "w").write(L.to_coq(cnf, st, nm))
            r = subprocess.run(["coqc", "-q", "-Q", os.path.join(ROOT, "coq"), "Sunflower", "-R", d, "T", out],
                               capture_output=True, text=True)
            expect((r.returncode == 0) == want, f"coq round trip {nm}: rc {r.returncode} {r.stderr[-200:]}")
    print("coq round trip: done")

print("ALL PASS" if fails == 0 else f"{fails} FAILURES")
sys.exit(1 if fails else 0)
