#!/usr/bin/env python3
"""The registered forward test for the "block tightness" question, and the
calibration that fixes its convention.  Committed because the original
registration (6ec69dc, stopping rule c0a21ca) shipped only a PROSE
description of "the same stratified permutation test", and prose was not
enough to reproduce it: see the resolution header block in
iota4_11.deg13.cryptominisat5.tsv.  A pre-registration must ship its code.

Run from the repository root:      python3 docs/ladder/forward_test.py
Needs only the standard library and `git` (it reads the checkpoint out of git,
not off disk).

BY DEFAULT THIS REPRODUCES THE TEST AS RUN, by reading the checkpoint at the
resolution commit REV_AS_RUN.  That matters: the sweep appends rows
continuously, so running against the working tree gives DIFFERENT numbers as
soon as another cube lands, and a script that cannot reproduce the result it
documents is no better than the prose it replaces.  Pass a revision to run it
on other data:  python3 docs/ladder/forward_test.py WORKTREE  (or any rev).

THE QUESTION.  Block [13,13,12,12] looked unusually "tight" -- its decided
consecutive triples had a smaller coefficient of variation than triples
elsewhere.  But the block was examined BECAUSE a tight trio turned up in it,
so that finding was contaminated by selection.  The forward test asks the
same question of the NEXT block, [13,13,12,11], whose data had no hand in
raising it.  RESULT: null, p = 0.1235.  See the header block.

CONVENTION, fixed before any in-block value was computed:
  unit      decided consecutive triple (i, i+1, i+2 all decided)
  value     CV = sample sd / mean (ddof=1) of the three DECIDED costs, where
            the decided cost of a label is the max over its NON-UNKNOWN rows
            (6ec69dc: max over ALL rows picks UNKNOWN cap costs and is wrong)
  stratum   length of the common leading prefix of all THREE degree sequences
  statistic pooled median CV(in-block) - pooled median CV(all other triples)
  null      reassign in-block labels at random WITHIN each stratum, preserving
            each stratum's in-block count; 20000 shuffles; Random(20260913)
  p         one-sided in the predicted direction (in-block smaller),
            (k + 1) / (N + 1)
"""
import collections, statistics, random, subprocess, sys, os

F = 'docs/ladder/iota4_11.deg13.cryptominisat5.tsv'
REV_AS_RUN = '9528aa9'   # the resolution commit: the data the test was run on
SEED, NSHUF = 20260913, 20000
NEW, OLD = (13, 13, 12, 11), (13, 13, 12, 12)
CALIB_CAP = 641          # idx 641 starts NEW; calibration may never see it

# ---- the cube list: a Python re-implementation of `fill` in rust/src/symbreak.rs
def cube_list(g=11, b=4, total=128, lo=0, prefix=11, d0=13):
    out = []
    def most_from(pos, top, prev):
        if pos >= g: return 0
        if pos < b:  return (b - pos) * prev + (g - b) * top
        return (g - pos) * min(prev, top)
    def fill(pos, top, prev, left, cur):
        if pos == prefix:
            ceiling = top if pos == b else prev
            if (g - pos) * lo <= left <= most_from(pos, top, ceiling):
                out.append(list(cur))
            return
        ceiling = top if pos == b else prev
        for d in range(ceiling, lo - 1, -1):
            if d > left: continue
            nc = top if pos + 1 == b else d
            if left - d > most_from(pos + 1, top, nc) or left - d < (g - pos - 1) * lo:
                continue
            cur.append(d); fill(pos + 1, top, d, left - d, cur); cur.pop()
    fill(1, d0, d0, total - d0, [d0])
    return out

SEQ = cube_list()
assert len(SEQ) == 1949, len(SEQ)
IDX = {'g=11 ' + str(s): i for i, s in enumerate(SEQ)}

def decided(text):
    """idx -> decided cost, i.e. max over the label's NON-UNKNOWN rows."""
    by = collections.defaultdict(list)
    for l in text.splitlines():
        if not l or l.startswith('#'): continue
        lab, v, c = l.split('\t'); by[lab].append((v, float(c)))
    return {IDX[lab]: max(c for v, c in rs if v != 'UNKNOWN')
            for lab, rs in by.items()
            if lab in IDX and any(v != 'UNKNOWN' for v, _ in rs)}

def at_rev(rev):
    return decided(subprocess.run(['git', 'show', rev + ':' + F],
                                  capture_output=True, text=True).stdout)

cv      = lambda xs: statistics.stdev(xs) / statistics.mean(xs)
blockof = lambda i, k=4: tuple(SEQ[i][:k])

def agree(idxs):
    """length of the common leading prefix of these cubes' degree sequences"""
    ss = [SEQ[i] for i in idxs]
    n = 0
    for pos in range(len(ss[0])):
        if all(s[pos] == ss[0][pos] for s in ss): n += 1
        else: break
    return n

def triples(dec, cap=None):
    ds = {i for i in dec if cap is None or i < cap}
    return [(i, i + 1, i + 2) for i in sorted(ds) if i + 1 in ds and i + 2 in ds]

def perm_test(units, seed=SEED, n=NSHUF):
    """units = [(stratum, in_block, value)].  Returns (obs, med_in, med_out, k, p).
    `obs` and every shuffled value are the POOLED median difference,
    in-block minus other; `k` counts shuffles at or BELOW the observed one."""
    def stat(flags):
        a = [u[2] for u, f in zip(units, flags) if f]
        b = [u[2] for u, f in zip(units, flags) if not f]
        return statistics.median(a) - statistics.median(b)
    obs = stat([u[1] for u in units])
    mi  = statistics.median([u[2] for u in units if u[1]])
    mo  = statistics.median([u[2] for u in units if not u[1]])
    by = collections.defaultdict(list)
    for k, u in enumerate(units): by[u[0]].append(k)
    nin = {a: sum(1 for k in ks if units[k][1]) for a, ks in by.items()}
    rng, le = random.Random(seed), 0
    for _ in range(n):
        fl = [False] * len(units)
        for a, ks in by.items():
            for k in rng.sample(ks, nin[a]): fl[k] = True
        if stat(fl) <= obs: le += 1
    return obs, mi, mo, le, (le + 1) / (n + 1)

def triple_units(dec, T, block, drop=None):
    u = []
    for t in T:
        inb = all(blockof(i) == block for i in t)
        if drop and not inb and all(blockof(i) == drop for i in t): continue
        u.append((agree(t), inb, cv([dec[i] for i in t])))
    return u

def ok(label, got, want, tol=5e-5):
    good = abs(got - want) <= tol
    print("  %-58s %10.4f  want %8.4f  %s" % (label, got, want, "OK" if good else "MISMATCH"))
    return good

# ------------------------------------------------------------------ calibration
def calibrate():
    """Reproduce every DESCRIPTIVE statistic published at 6ec69dc and 29785de.
    Nothing at or above idx 641 may enter here -- that is the forward-test
    block, and calibrating on it would defeat the pre-registration."""
    print("CALIBRATION -- published descriptive statistics, idx >= %d excluded" % CALIB_CAP)
    allgood = True
    d = at_rev('6ec69dc')
    if not d:
        print("  (revision 6ec69dc unavailable; skipping)"); return None
    T = triples(d, CALIB_CAP)
    ins  = [cv([d[i] for i in t]) for t in T if all(blockof(i) == OLD for i in t)]
    outs = [cv([d[i] for i in t]) for t in T if not all(blockof(i) == OLD for i in t)]
    print("  6ec69dc: triples, CV, block [13,13,12,12]")
    allgood &= ok("n in-block (want 62)", len(ins), 62, 0.5)
    allgood &= ok("n other    (want 559)", len(outs), 559, 0.5)
    allgood &= ok("median CV in-block", statistics.median(ins), 0.1260)
    allgood &= ok("median CV other", statistics.median(outs), 0.2843)

    d = at_rev('29785de')
    ds = {i for i in d if i < CALIB_CAP}
    P = [(i, i + 1) for i in sorted(ds) if i + 1 in ds]
    gap = lambda p: abs(d[p[0]] - d[p[1]]) / ((d[p[0]] + d[p[1]]) / 2)
    print("  29785de: PAIRS, relative gap |d|/mean -- note: NOT triples, NOT CV")
    Si, So = collections.defaultdict(list), collections.defaultdict(list)
    for p in P:
        (Si if all(blockof(i) == OLD for i in p) else So)[agree(p)].append(gap(p))
    for a, wi, wo in ((7, 0.2309, 0.4336), (8, 0.0776, 0.2634), (9, 0.1051, 0.1311)):
        allgood &= ok("agreement %d, median in-block" % a, statistics.median(Si[a]), wi)
        allgood &= ok("agreement %d, median other"    % a, statistics.median(So[a]), wo)
    ai = [agree(p) for p in P if all(blockof(i) == OLD for i in p)]
    ao = [agree(p) for p in P if not all(blockof(i) == OLD for i in p)]
    allgood &= ok("mean pair agreement in-block", statistics.mean(ai), 8.47, 5e-3)
    allgood &= ok("mean pair agreement other",    statistics.mean(ao), 8.10, 5e-3)
    print("  ALL DESCRIPTIVE STATISTICS REPRODUCE" if allgood else "  *** A DESCRIPTIVE STATISTIC DOES NOT REPRODUCE ***")
    print("  The published p = 0.0117 does NOT reproduce under this convention")
    print("  (pooled-median difference gives 0.0235).  The search for a convention")
    print("  that would hit 0.0117 was STOPPED, not continued: trying conventions")
    print("  until one reproduces a target is the tuning pre-registration prevents.")
    return allgood

# ----------------------------------------------------------------- the test
def main():
    if not os.path.exists(F):
        sys.exit("run from the repository root; %s not found" % F)
    rev = sys.argv[1] if len(sys.argv) > 1 else REV_AS_RUN
    calibrate()
    if rev.upper() == 'WORKTREE':
        dec, src = decided(open(F).read()), 'the working tree (NOT the data the test was run on)'
    else:
        dec, src = at_rev(rev), 'revision %s%s' % (rev, ' -- the data the test was run on'
                                                  if rev == REV_AS_RUN else '')
        if not dec:
            sys.exit("cannot read %s at %s" % (F, rev))
    T = triples(dec)
    print("\nDATA: %s" % src)
    print("      %d decided cubes, %d decided consecutive triples" % (len(dec), len(T)))

    U = triple_units(dec, T, NEW)
    nin = sum(1 for u in U if u[1])
    print("\n=== PRIMARY -- THE REGISTERED TEST: block [13,13,12,11] ===")
    print("in-block triples %d, other triples %d" % (nin, len(U) - nin))
    S = collections.defaultdict(lambda: ([], []))
    for a, inb, v in U: S[a][0 if inb else 1].append(v)
    print("per-stratum median CV (stratum = common prefix of all three):")
    for a in sorted(S):
        i, o = S[a]
        print("   agr %2d  n_in=%3d med_in=%s   n_out=%4d med_out=%s"
              % (a, len(i), ("%.4f" % statistics.median(i)) if i else "   -  ",
                    len(o), ("%.4f" % statistics.median(o)) if o else "   -  "))
    obs, mi, mo, k, p = perm_test(U)
    print("median CV in-block %.4f   other %.4f   difference %+.4f" % (mi, mo, obs))
    print("%d of %d shuffles at or below observed" % (k, NSHUF))
    print("ONE-SIDED p (predicted direction: in-block smaller) = %.4f" % p)
    print("STOPPING RULE (c0a21ca): run at the first of >= 20 in-block triples")
    print("or the block complete.  Met at 20 triples, on the row for idx 662.")
    if rev == REV_AS_RUN and (nin != 20 or abs(p - 0.1235) > 5e-5):
        print("*** WARNING: this does NOT match the published result "
              "(20 triples, p = 0.1235) ***")

    print("\n=== COMPANIONS -- all declared before computing, all reported ===")
    _, i1, o1, k1, p1 = perm_test(triple_units(dec, T, NEW, drop=OLD))
    print("1. [13,13,12,12] triples dropped from the comparison set:"
          "  %.4f vs %.4f, p = %.4f" % (i1, o1, p1))
    _, i2, o2, k2, p2 = perm_test([(0, inb, v) for _, inb, v in U])
    print("2. the 6ec69dc form, triples/CV UNSTRATIFIED:"
          "              %.4f vs %.4f, p = %.4f" % (i2, o2, p2))
    ds = set(dec)
    P = [(i, i + 1) for i in sorted(ds) if i + 1 in ds]
    U3 = [(agree(p_), all(blockof(i) == NEW for i in p_),
           abs(dec[p_[0]] - dec[p_[1]]) / ((dec[p_[0]] + dec[p_[1]]) / 2)) for p_ in P]
    _, i3, o3, k3, p3 = perm_test(U3)
    print("3. the 29785de form, PAIRS/relative gap stratified:"
          "      %.4f vs %.4f, p = %.4f" % (i3, o3, p3))
    _, i4, o4, k4, p4 = perm_test(triple_units(dec, T, OLD))
    print("4. reference, [13,13,12,12] under THIS convention today:"
          " %.4f vs %.4f, p = %.4f" % (i4, o4, p4))

if __name__ == '__main__':
    main()
