"""Stability case of Palvolgyi at b=4 on a bounded ground set.
# Build: gcc -O2 -o tools/g4/stabtri tools/g4/stabtri.c ; usage: python3 tools/g4/stability_sat.py <outer points k> <target T> [timeout s] (docs/roadmap.md §62.1)
P = {0..8} carries A = AHS27 (fixed); outer points 9..8+k; R = {9,10,11,12} in F.
Every member outside A meets R (D(R) = A), so the variables are the 4-sets meeting R, other than R.
Constraint: A + R + chosen has no 3-sunflower.  Target: #chosen + 1 (= |U|+|W|) >= T."""
import sys, itertools, subprocess, os
from pysat.card import CardEnc, EncType
k, T = int(sys.argv[1]), int(sys.argv[2]); tl = sys.argv[3] if len(sys.argv) > 3 else "600"
X = [(0,1,2),(3,4,5),(6,7,8)]
A = [frozenset(a) | frozenset(b) for i, j in [(0,1),(0,2),(1,2)] for a in itertools.combinations(X[i], 2) for b in itertools.combinations(X[j], 2)]
assert len(A) == 27
n = 9 + k; R = frozenset(range(9, 13)); P = frozenset(range(9))
cands = [frozenset(c) for c in itertools.combinations(range(n), 4) if set(c) & R and frozenset(c) != R]
allsets = A + [R] + cands; nf = 28
inp = f"{len(allsets)}\n" + "".join(f"{sum(1<<x for x in s)} {1 if i < nf else 0}\n" for i, s in enumerate(allsets))
out = subprocess.run([os.path.join(os.path.dirname(os.path.abspath(__file__)), "stabtri")], input=inp, capture_output=True, text=True, check=True).stdout.split("\n")
cl = []
for l in out:
    if not l.strip(): continue
    assert l != "ERR"
    cl.append([-(int(v) - nf + 1) for v in l.split()])
nv = len(cands)
card = CardEnc.atleast(lits=list(range(1, nv + 1)), bound=T - 1, top_id=nv, encoding=EncType.seqcounter)
fn = f"s_{k}_{T}.cnf"
with open(fn, "w") as f:
    f.write(f"p cnf {card.nv} {len(cl) + len(card.clauses)}\n")
    for c in cl + card.clauses: f.write(" ".join(map(str, c)) + " 0\n")
p = subprocess.run(["/tmp/claude-0/tools/cadical/build/cadical", "-q", "-t", tl, fn], capture_output=True, text=True); os.remove(fn)
v = {10: "SAT", 20: "UNSAT"}.get(p.returncode, "TIMEOUT")
if v == "SAT":
    model = set(int(x) for l in p.stdout.splitlines() if l.startswith("v") for x in l.split()[1:] if int(x) > 0)
    fam = [c for i, c in enumerate(cands) if i + 1 in model] + [R]
    Fall = A + fam
    assert all(not ((a & b) == (a & c) == (b & c)) for a, b, c in itertools.combinations(Fall, 3))
    U = [s for s in fam if not (s & P)]; W = [s for s in fam if s & P]
    print(v, "U+W =", len(fam), "U", len(U), "W", len(W), "W trace sizes", sorted(len(s & P) for s in W))
    print("  W:", sorted(tuple(sorted(s)) for s in W)); print("  U:", sorted(tuple(sorted(s)) for s in U))
else: print(v, "cands", nv, "clauses", len(cl))
