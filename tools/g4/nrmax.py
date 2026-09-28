"""max |N[R]|: 4-sets on R={0..3} + outer {4..4+k-1}, each meeting R, R included,
no 3-sunflower. Exact by SAT for given k, T."""
import sys, itertools, subprocess, os
from pysat.card import CardEnc, EncType
k, T = int(sys.argv[1]), int(sys.argv[2]); n = 4 + k; R = frozenset(range(4))
cands = [frozenset(c) for c in itertools.combinations(range(n), 4) if set(c) & R and frozenset(c) != R]
idx = {c: i + 1 for i, c in enumerate(cands)}; allsets = [R] + cands; cl = []
for a, b, c in itertools.combinations(range(len(allsets)), 3):
    A, B, C = allsets[a], allsets[b], allsets[c]; ab = A & B
    if ab == (A & C) and ab == (B & C): cl.append([-idx[X] for X in (A, B, C) if X in idx])
card = CardEnc.atleast(lits=list(idx.values()), bound=T - 1, top_id=len(cands), encoding=EncType.seqcounter)
fn = f"n_{k}_{T}.cnf"
with open(fn, "w") as f:
    f.write(f"p cnf {card.nv} {len(cl) + len(card.clauses)}\n")
    for c in cl + card.clauses: f.write(" ".join(map(str, c)) + " 0\n")
p = subprocess.run(["/tmp/claude-0/tools/cadical/build/cadical", "-q", "-t", "300", fn], capture_output=True, text=True); os.remove(fn)
print({10: "SAT", 20: "UNSAT"}.get(p.returncode, "TIMEOUT"))
