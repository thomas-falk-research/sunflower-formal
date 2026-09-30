#!/usr/bin/env python3
"""Regression test for bnbcert.check (docs/roadmap.md §65.4).

A fresh-context review forged a certificate that the first checker accepted,
using a negative multiplier key ("-362") that indexed lo[] from the end
without the matching term in w. This test builds that forgery and four other
malformed certificates on class 14708, and requires each to be rejected;
the genuine certificate must pass. Run it plain and under `python3 -O`
(the checks must not be asserts).
"""
import sys, os, json, gzip, copy, tempfile
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
import bnbcert
from linkcert import load

REPO = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))
CLASSES = os.path.join(REPO, "docs/ladder/iota4_replication/classes_23_27.txt.gz")
CERT = os.path.join(REPO, "docs/ladder/iota4_replication/link23_bnb/bnb_14708.json.gz")
K = 14708
D = load(CLASSES)[K]
n, rows, rhs, ub = bnbcert.matrix(D)
genuine = json.load(gzip.open(CERT, "rt"))


def first_leaf(t):
    return t if "leaf" in t else first_leaf(t["le"])


def forged_negative_key():
    # the reviewer's construction: a chain splitting every variable at 0; each
    # 'ge' leaf claims a huge v at index j - n (negative), which the old
    # checker subtracted from the bound without adding to w
    allu = {str(i): "1" for i in range(n)}
    def build(j):
        if j == n:
            return {"leaf": "bound", "cert": {"y": {}, "u": allu, "v": {}}}
        ge = {"leaf": "bound", "cert": {"y": {}, "u": allu, "v": {str(j - n): "1000000"}}}
        return {"var": j, "f": 0, "le": build(j + 1), "ge": ge}
    return {"n": n, "goal": genuine["goal"], "tree": build(0)}


def float_split():
    c = copy.deepcopy(genuine)
    t = c["tree"]
    t["f"] = t["f"] + 0.5
    return c


def emptied_leaf():
    c = copy.deepcopy(genuine)
    L = first_leaf(c["tree"])
    L["cert"] = {"y": {}, "u": {}, "v": {}}
    return c


def y_out_of_range():
    c = copy.deepcopy(genuine)
    L = first_leaf(c["tree"])
    L["cert"]["y"][str(len(rows))] = "1"
    return c


def unknown_leaf_kind():
    c = copy.deepcopy(genuine)
    first_leaf(c["tree"])["leaf"] = "trust-me"
    return c


def run(cert):
    with tempfile.NamedTemporaryFile(suffix=".json.gz", delete=False) as f:
        path = f.name
    with gzip.open(path, "wt") as g:
        json.dump(cert, g)
    try:
        return bnbcert.check(D, path)
    finally:
        os.unlink(path)


if __name__ == "__main__":
    sys.setrecursionlimit(10000)
    ok = run(genuine)
    print("genuine certificate: PASS", ok)
    bad = 0
    for name, make in [("negative key forgery", forged_negative_key), ("float split", float_split),
                       ("emptied leaf", emptied_leaf), ("y key out of range", y_out_of_range),
                       ("unknown leaf kind", unknown_leaf_kind)]:
        try:
            run(make())
        except (bnbcert.CertError, KeyError, ValueError) as e:
            print(f"{name}: rejected ({type(e).__name__}: {str(e)[:60]})")
        else:
            print(f"{name}: ACCEPTED -- checker is unsound")
            bad += 1
    print("TEST FAIL" if bad else "TEST PASS")
    sys.exit(1 if bad else 0)
