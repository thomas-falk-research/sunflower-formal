"""km.py -- prescribed-symmetry search for a b-uniform 3-sunflower-free
family of at least T members on n points, invariant under a given group.
  python3 km.py n b T 'gen1;gen2;...'     each gen = space-separated image list
Prints SAT + the family (independently re-verified) or UNSAT, with the
max achievable under the group found by descending search if --max."""
import sys, subprocess, itertools, time
from pysat.card import CardEnc, EncType
from pysat.solvers import Solver

def verify(F, b):
    F = [frozenset(A) for A in F]
    assert len(set(F)) == len(F) and all(len(A) == b for A in F)
    for A, B, C in itertools.combinations(F, 3):
        if (A & B) == (A & C) == (B & C):
            return False
    return True

def orbit_expand(rep, gens, n):
    seen = {rep}; st = [rep]
    while st:
        x = st.pop()
        for g in gens:
            y = frozenset(g[i] for i in x)
            if y not in seen: seen.add(y); st.append(y)
    return seen

def run(n, b, T, gens, solver='cadical153'):
    inp = f"{n} {b} {len(gens)}\n" + "\n".join(" ".join(map(str, g)) for g in gens) + "\n"
    out = subprocess.run(["./kmtri"], input=inp, capture_output=True, text=True, check=True).stdout.split("\n")
    sizes, reps, clauses = {}, {}, []
    for l in out:
        if l.startswith("w "):
            _, o, s, r = l.split(); sizes[int(o)] = int(s); reps[int(o)] = int(r)
        elif l.startswith("c "):
            os_ = sorted(set(int(v) for v in l.split()[1:]))
            clauses.append([-(o + 1) for o in os_])
    m = len(sizes)
    lits = [o + 1 for o in range(m) for _ in range(sizes[o])]
    if len(lits) < T: return ("UNSAT", m, len(clauses), None)
    card = CardEnc.atleast(lits=lits, bound=T, top_id=m, encoding=EncType.kmtotalizer)
    s = Solver(name=solver, bootstrap_with=clauses + card.clauses)
    t0 = time.time(); ok = s.solve(); dt = time.time() - t0
    if not ok: return ("UNSAT", m, len(clauses), dt)
    model = set(v for v in s.get_model() if v > 0)
    fam = []
    for o in range(m):
        if o + 1 in model:
            rep = frozenset(i for i in range(n) if reps[o] >> i & 1)
            fam += [sorted(A) for A in orbit_expand(rep, [tuple(g) for g in gens], n)]
    assert verify(fam, b), "SOLVER FAMILY FAILS VERIFICATION"
    return ("SAT", m, len(clauses), dt, fam)

if __name__ == "__main__":
    n, b, T = map(int, sys.argv[1:4])
    gens = [list(map(int, g.split())) for g in sys.argv[4].split(";") if g.strip()] or [list(range(n))]
    r = run(n, b, T, gens)
    print(r[0], "orbits", r[1], "clauses", r[2], "time", r[3])
    if r[0] == "SAT": print(len(r[4]), r[4])
