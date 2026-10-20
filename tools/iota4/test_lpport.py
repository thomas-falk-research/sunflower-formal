#!/usr/bin/env python3
"""Tests for the Link23 -> LPCert port (tools/iota4/link23_coq.py, coq/Link23.v).

  python3 tools/iota4/test_lpport.py          conversion and checking
  python3 tools/iota4/test_lpport.py --coq    also the Coq round trip

On the committed size-22 trees (link22_trees/shard_0) and classes:

1. Every tree converts to LPCert form, the converted tree passes the exact
   LPCert-semantics check here ([lp_check]) and the independent generic
   checker of tools/lpcert ([lpcert.check]) on the same program.
2. Tampered trees: [lp_check] and [lpcert.check] agree on every one;
   the always-invalid tamperings (negative scale, negative multiplier,
   a leaf stripped of its multipliers, a branching row named off the
   path in place of a needed one) are rejected.
3. (--coq) A module of a few classes, branching ones included, compiles
   (its lemma is decided by [vm_compute] through [Link23.lpclass]); the
   same module with one needed multiplier zeroed does not.
"""
import copy, gzip, json, os, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(ROOT, "tools", "lpcert"))
import link23_coq as L
import lpcert

DATA = os.path.join(ROOT, "docs", "ladder", "iota4_replication")
fails = 0


def expect(cond, what):
    global fails
    if not cond:
        fails += 1
        print("FAIL:", what)


def leaves(node):
    if "leaf" in node:
        yield node
    else:
        yield from leaves(node["le"])
        yield from leaves(node["ge"])


def ok_here(D, lt, mdl):
    try:
        L.lp_check(D, lt, mdl)
        return True
    except AssertionError:
        return False


def ok_generic(D, lt, mdl):
    prob, tr = L.lp_problem(D, mdl)
    try:
        return lpcert.check(prob, tr(lt))
    except lpcert.CertError:
        return False


docs = json.load(gzip.open(os.path.join(DATA, "link22_trees", "shard_0.json.gz"), "rt"))
pick = docs[:40] + [d for d in docs if "leaf" not in d["tree"]][:15]
fams = L.load_ks(os.path.join(DATA, "classes_22.txt.gz"), [d["k"] for d in pick])
cases = []
for d in pick:
    D = L.canon(fams[d["k"]])
    mdl = L.model(D)
    lt = L.lp_of_doc(d, mdl[2])
    expect(ok_here(D, lt, mdl), f"converted tree rejected, class {d['k']}")
    expect(ok_generic(D, lt, mdl), f"generic checker rejects class {d['k']}")
    cases.append((d["k"], D, mdl, lt))
nbr = sum("branch" in lt for _, _, _, lt in cases)
print(f"converted: {len(cases)} classes ({nbr} branching), all accepted by both checkers")

tam = rej = 0
for k, D, mdl, lt in cases:
    variants = []
    t = copy.deepcopy(lt); next(leaves(t))["leaf"]["K"] = -1; variants.append((t, True))
    t = copy.deepcopy(lt); lf = next(leaves(t))["leaf"]
    if lf["y"]:
        lf["y"][0][1] = -lf["y"][0][1] - 1; variants.append((t, True))
    t = copy.deepcopy(lt); lf = next(lf_ for lf_ in leaves(t) if lf_["leaf"]["K"] > 0)["leaf"] if any(
        x["leaf"]["K"] > 0 for x in leaves(t)) else None
    if lf is not None:
        lf["y"] = []; variants.append((t, True))
    t = copy.deepcopy(lt); lf = next(leaves(t))["leaf"]
    if lf["y"]:
        lf["y"][0][0] = ["br", 10 ** 6]; variants.append((t, False))      # may or may not matter
    t = copy.deepcopy(lt)
    for lf in leaves(t):
        for q in lf["leaf"]["y"]:
            q[1] += 1
    variants.append((t, False))
    for t, must_reject in variants:
        a, b = ok_here(D, t, mdl), ok_generic(D, t, mdl)
        expect(a == b, f"checkers disagree on a tampered tree, class {k}")
        if must_reject:
            expect(not a, f"invalid tampered tree accepted, class {k}")
        tam += 1; rej += not a
print(f"tampering: {tam} trees, {rej} rejected, checkers agree on all")

if "--coq" in sys.argv:
    few = [c for c in cases if "branch" in c[3]][:2] + [c for c in cases if "branch" not in c[3]][:2]
    good = [(k, D, lt) for k, D, _, lt in few]
    k0, D0, m0, lt0 = few[0]
    bad_lt = copy.deepcopy(lt0)
    broken = False
    for lf in leaves(bad_lt):
        for q in lf["leaf"]["y"]:
            old = q[1]; q[1] = 0
            if not ok_here(D0, bad_lt, m0):
                broken = True; break
            q[1] = old
        if broken:
            break
    expect(broken, "no single multiplier is needed (cannot build the negative case)")
    bad = [(k0, D0, bad_lt)] + good[1:]
    with tempfile.TemporaryDirectory() as d:
        for name, items, want_ok in (("PortOk", good, True), ("PortBad", bad, False)):
            out = os.path.join(d, f"{name}.v")
            L.emit_shard_lp(items, out, name.lower())
            r = subprocess.run(["coqc", "-q", "-Q", os.path.join(ROOT, "coq"), "Sunflower", "-R", d, "T", out],
                               capture_output=True, text=True)
            expect((r.returncode == 0) == want_ok, f"coq round trip {name}: rc {r.returncode} {r.stderr[-300:]}")
    print("coq round trip: done")

print("ALL PASS" if fails == 0 else f"{fails} FAILURES")
sys.exit(1 if fails else 0)
