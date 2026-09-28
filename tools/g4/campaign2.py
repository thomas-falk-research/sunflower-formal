"""Memory-lean KM campaign: kmtri -> DIMACS file -> standalone CaDiCaL.
Usage: campaign2.py T timeout maxorbits jobfile outfile"""
import sys, subprocess, json, os, time, itertools
from pysat.card import CardEnc, EncType
import km
CAD = "/tmp/claude-0/tools/cadical/build/cadical"
T, timeout, maxorb, jobfile, outfile = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4], sys.argv[5]
for line in open(jobfile):
    name, n, g = line.rstrip("\n").split("\t"); n = int(n)
    gens = [list(map(int, x.split())) for x in g.split(";")]
    import itertools as _it
    seen=set(); m0=0
    for c in _it.combinations(range(n),4):
        c=frozenset(c)
        if c in seen: continue
        m0+=1; st=[c]; seen.add(c)
        while st:
            y=st.pop()
            for g_ in gens:
                z=frozenset(g_[i] for i in y)
                if z not in seen: seen.add(z); st.append(z)
    if m0 > maxorb:
        with open(outfile, "a") as out: out.write(json.dumps(dict(name=name, n=n, T=T, orbits=m0, verdict="SKIPPED-too-many-orbits")) + "\n")
        print(name, n, m0, "SKIPPED", flush=True); continue
    inp = f"{n} 4 {len(gens)}\n" + "\n".join(" ".join(map(str, x)) for x in gens) + "\n"
    tri = f"tri_{name}.txt"
    with open(tri, "w") as f: subprocess.run(["./kmtri"], input=inp, text=True, stdout=f, check=True)
    sizes, reps = {}, {}
    with open(tri) as f:
        for l in f:
            if l[0] == "w": _, o, s, r = l.split(); sizes[int(o)] = int(s); reps[int(o)] = int(r)
            elif l[0] == "c": break
    m = len(sizes); res = dict(name=name, n=n, T=T, orbits=m)
    if m > maxorb:
        res["verdict"] = "SKIPPED-too-many-orbits"
    else:
        lits = [o + 1 for o in range(m) for _ in range(sizes[o])]
        card = CardEnc.atleast(lits=lits, bound=T, top_id=m, encoding=EncType.kmtotalizer)
        cnf = f"cnf_{name}.cnf"; ncl = 0
        with open(tri) as f, open(cnf + ".body", "w") as w:
            for l in f:
                if l[0] == "c":
                    os_ = sorted(set(int(v) for v in l.split()[1:]))
                    w.write(" ".join(str(-(o + 1)) for o in os_) + " 0\n"); ncl += 1
            for c in card.clauses: w.write(" ".join(map(str, c)) + " 0\n"); ncl += 1
        with open(cnf, "w") as w:
            w.write(f"p cnf {card.nv} {ncl}\n")
        os.system(f"cat {cnf}.body >> {cnf}; rm {cnf}.body")
        t0 = time.time()
        p = subprocess.run([CAD, "-q", "-t", str(timeout), cnf], capture_output=True, text=True)
        res["time"] = round(time.time() - t0, 1); res["clauses"] = ncl
        if p.returncode == 20: res["verdict"] = "UNSAT"
        elif p.returncode == 10:
            model = set(int(v) for l in p.stdout.splitlines() if l.startswith("v") for v in l.split()[1:] if int(v) > 0)
            fam = []
            for o in range(m):
                if o + 1 in model:
                    rep = frozenset(i for i in range(n) if reps[o] >> i & 1)
                    fam += [sorted(A) for A in km.orbit_expand(rep, [tuple(x) for x in gens], n)]
            assert km.verify(fam, 4), "family fails verification"
            res.update(verdict="SAT", size=len(fam), family=fam)
        else: res["verdict"] = "TIMEOUT"
        os.remove(cnf)
    os.remove(tri)
    with open(outfile, "a") as out: out.write(json.dumps(res) + "\n")
    print(name, n, m, res["verdict"], res.get("time", ""), res.get("size", ""), flush=True)
