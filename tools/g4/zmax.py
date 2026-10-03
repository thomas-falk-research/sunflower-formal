"""max |Z|: 4-sets on R={0..3}, S={4..7}, outer {8..8+k-1}, each meeting both
R and S, such that Z ∪ {R, S} has no 3-sunflower. Exact, by SAT (CaDiCaL)."""
import sys, itertools, subprocess, os
from pysat.card import CardEnc, EncType
k = int(sys.argv[1]); T = int(sys.argv[2])
n = 8 + k; R = frozenset(range(4)); S = frozenset(range(4, 8))
cands = [frozenset(c) for c in itertools.combinations(range(n), 4) if set(c) & R and set(c) & S]
idx = {c: i + 1 for i, c in enumerate(cands)}
fixed = [R, S]
cl = []
allsets = fixed + cands
# triples: sunflower iff pairwise intersections equal
for a, b, c in itertools.combinations(range(len(allsets)), 3):
    A, B, C = allsets[a], allsets[b], allsets[c]
    ab = A & B
    if ab == (A & C) and ab == (B & C):
        clause = [-idx[X] for X in (A, B, C) if X in idx]
        cl.append(clause)
card = CardEnc.atleast(lits=list(idx.values()), bound=T, top_id=len(cands), encoding=EncType.seqcounter)
fn = f"z_{k}_{T}.cnf"
with open(fn, "w") as f:
    f.write(f"p cnf {card.nv} {len(cl) + len(card.clauses)}\n")
    for c in cl + card.clauses: f.write(" ".join(map(str, c)) + " 0\n")
p = subprocess.run(["/tmp/claude-0/tools/cadical/build/cadical", "-q", "-t", sys.argv[3] if len(sys.argv) > 3 else "600", fn], capture_output=True, text=True)
os.remove(fn)
v = {10: "SAT", 20: "UNSAT"}.get(p.returncode, "TIMEOUT")
if v == "SAT":
    model = set(int(x) for l in p.stdout.splitlines() if l.startswith("v") for x in l.split()[1:] if int(x) > 0)
    Z = [sorted(c) for c in cands if idx[c] in model]
    print(v, len(Z), Z)
else:
    print(v, "cands", len(cands), "sunflower clauses", len(cl))
