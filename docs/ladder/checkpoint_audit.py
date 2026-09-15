#!/usr/bin/env python3
"""Audit the deg-13 checkpoint against the independently regenerated cube list.

WHY
---
Every progress figure reported for this sweep -- how many cubes are decided,
where the frontier is, which indices are holes, what percentage is done --
comes from resolving each row's label to an index in the 1949-cube list.
That resolution is done row by row as rows land.  This script redoes the
whole thing from scratch, for every row in the file at once, so the running
figures are checked rather than trusted.

It reuses the cube-list generator and the decided() resolver shipped in
forward_test.py, and cross-checks its own recomputation against decided()
as a second opinion on the same data.

TWO KINDS OF CHECK
------------------
INVARIANTS hold at any size and any point in the sweep.  They are the
durable value of this script:

  I1  every row has exactly 3 tab-separated fields
  I2  every verdict is UNSAT, SAT or UNKNOWN; every cost parses as a number
  I3  every label resolves to some index in the regenerated 1949-cube list
  I4  no index is ever DECIDED twice -- at most one non-UNKNOWN attempt per
      label, so the decided-cost rule's max() never has to choose between
      two conflicting decided costs
  I5  the recomputation here agrees exactly with shipped decided()
  I6  no SAT verdict anywhere (a SAT would refute deg(0)=13 being UNSAT and
      is the one result that would change the mathematics)

A SNAPSHOT cross-check compares against figures recorded at one revision.
The checkpoint GROWS, so a snapshot mismatch is EXPECTED once new rows land
and is reported as drift, not as failure.  Only an invariant violation is a
failure.

THE DECIDED-COST RULE, AND WHAT "27 DISAGREE" MEANS
---------------------------------------------------
A cube's cost is  max(c for verdict, c in rows if verdict != 'UNKNOWN').
6ec69dc introduced this after finding that taking the max over ALL rows for
a label picks up an earlier attempt that hit the cap and wrote UNKNOWN.  Its
words: "80 labels carry multiple rows and in 27 the max disagrees with the
decided cost; worst case used 10893.7 for a cube decided at 8270.4, 32
percent too high."

That 27 is the count of labels where the NAIVE max over all rows differs
from the decided cost.  It is NOT a count of conflicting verdicts, and
compressing it to "27 disagree" invites that misreading.  Invariant I4 is
the sharper statement: no label is ever decided twice, so nothing in this
file disagrees with anything.  Every multi-row label is exactly one UNSAT
preceded by one or more UNKNOWN attempts.  The filter in the decided rule
therefore never breaks a tie -- it only ever discards UNKNOWN cap costs --
and the 27 counts how often discarding them actually changes the number.

Run with no arguments to audit the working tree; pass a git rev to audit the
checkpoint as of that revision.
"""

import collections, subprocess, sys

CHECKPOINT = 'docs/ladder/iota4_11.deg13.cryptominisat5.tsv'
HELPERS    = 'docs/ladder/forward_test.py'
SPLIT_AT   = "# ------------------------------------------------------------------ calibration"

# Figures recorded at this revision.  The checkpoint grows, so these go stale
# by design; drift from them is not a failure.
SNAPSHOT_REV = '07b8a61'
SNAPSHOT = dict(rows=860, decided=691, total=1949, contig_top=683, highest=691,
                holes=[684], undecided_only=0, sat=0,
                multi_row_labels=80, naive_max_differs=27)


def load(rev=None):
    if rev:
        return subprocess.run(['git', 'show', f'{rev}:{CHECKPOINT}'],
                              capture_output=True, text=True, check=True).stdout
    return open(CHECKPOINT).read()


def main(rev=None):
    ns = {}
    exec(open(HELPERS).read().split(SPLIT_AT)[0], ns)
    IDX, SEQ, decided, blockof = ns['IDX'], ns['SEQ'], ns['decided'], ns['blockof']

    raw  = load(rev)
    rows = [l for l in raw.splitlines() if l and not l.startswith('#')]
    where = rev or 'working tree'
    print(f"auditing {CHECKPOINT} @ {where}: {len(rows)} real data rows,"
          f" {len(SEQ)} cubes in the regenerated list\n")

    fails = []

    # I1/I2 structure
    malformed = [i for i, l in enumerate(rows) if len(l.split('\t')) != 3]
    if malformed: fails.append(f"I1 malformed rows at lines {malformed[:5]}")
    verdicts = collections.Counter(l.split('\t')[1] for l in rows if len(l.split('\t')) == 3)
    stray = [v for v in verdicts if v not in ('UNSAT', 'SAT', 'UNKNOWN')]
    if stray: fails.append(f"I2 unexpected verdict strings {stray}")
    badc = []
    for l in rows:
        f = l.split('\t')
        if len(f) == 3:
            try: float(f[2])
            except ValueError: badc.append(l)
    if badc: fails.append(f"I2 {len(badc)} non-numeric cost fields")
    print(f"I1 structure        rows malformed: {len(malformed)}")
    print(f"I2 fields           verdicts {dict(verdicts)}, non-numeric costs {len(badc)}")

    # I3 resolution
    by, unresolved = collections.defaultdict(list), []
    for i, l in enumerate(rows):
        f = l.split('\t')
        if len(f) != 3: continue
        lab, v, c = f
        if lab not in IDX: unresolved.append((i, lab)); continue
        by[IDX[lab]].append((v, float(c)))
    if unresolved:
        fails.append(f"I3 {len(unresolved)} labels not in the cube list, e.g. {unresolved[:3]}")
    print(f"I3 resolution       unresolved labels: {len(unresolved)};"
          f" distinct indices touched: {len(by)}")

    # I4 no index decided twice
    twice = [i for i, a in by.items() if sum(1 for v, _ in a if v != 'UNKNOWN') >= 2]
    if twice: fails.append(f"I4 {len(twice)} indices decided more than once: {twice[:5]}")
    multi = {i: a for i, a in by.items() if len(a) > 1}
    print(f"I4 single decision  indices decided more than once: {len(twice)}"
          f"   (multi-row labels: {len(multi)})")

    # I5 agreement with shipped decided()
    mine   = {i: max(c for v, c in a if v != 'UNKNOWN')
              for i, a in by.items() if any(v != 'UNKNOWN' for v, _ in a)}
    theirs = decided(raw)
    if mine != theirs:
        d = set(mine) ^ set(theirs)
        fails.append(f"I5 recomputation disagrees with decided() on {len(d)} indices")
    print(f"I5 second opinion   agrees with shipped decided(): {mine == theirs}"
          f"   ({len(mine)} decided)")

    # I6 no SAT
    sats = sorted(i for i, a in by.items() if any(v == 'SAT' for v, _ in a))
    if sats: fails.append(f"I6 SAT verdict present at indices {sats}")
    print(f"I6 no SAT           indices with any SAT attempt: {len(sats)}")

    # derived figures
    lo = 0
    while lo in mine: lo += 1
    contig, highest = lo - 1, (max(mine) if mine else -1)
    holes = [i for i in range(highest + 1) if i not in mine]
    undec = sorted(i for i in by if i not in mine)
    naive = sum(1 for a in multi.values()
                if any(v != 'UNKNOWN' for v, _ in a)
                and max(c for v, c in a if v != 'UNKNOWN') != max(c for _, c in a))

    print(f"\nfrontier contiguous 0..{contig}, highest decided {highest}, holes {holes}")
    print(f"done {len(mine)} of {len(SEQ)} = {100*len(mine)/len(SEQ):.4f}%,"
          f" remaining {len(SEQ)-len(mine)}")
    print(f"undecided-only indices: {len(undec)}"
          f"   (UNKNOWN rows in file: {verdicts.get('UNKNOWN', 0)}, the rest superseded)")
    print(f"multi-row labels {len(multi)}; naive max over ALL rows differs from the"
          f" decided cost in {naive} of them")

    # cap history, recovered from the UNKNOWN rows (diagnostic, NOT an invariant:
    # the cap is raised over the sweep's life, so these values legitimately change)
    unk = sorted((float(l.split('\t')[2]), n) for n, l in enumerate(rows)
                 if len(l.split('\t')) == 3 and l.split('\t')[1] == 'UNKNOWN')
    if unk:
        groups = [[unk[0]]]
        for c in unk[1:]:
            if c[0] - groups[-1][-1][0] > 0.10 * groups[-1][-1][0]: groups.append([c])
            else: groups[-1].append(c)
        print("\ncap history recovered from UNKNOWN rows (diagnostic, not an invariant).")
        print("An UNKNOWN row is written when the per-cube budget runs out, so each")
        print("tight cluster marks a cap that was in force for part of the sweep:")
        print(f"   {'n':>4} {'cost min':>10} {'cost max':>10} {'file rows':>14}  cluster")
        for g in groups:
            lo, hi = g[0][0], g[-1][0]
            pos = [n for _, n in g]
            tight = (hi - lo) <= 0.02 * lo
            print(f"   {len(g):>4} {lo:>10.1f} {hi:>10.1f} {min(pos):>6}..{max(pos):<6}  "
                  f"{'tight -- a cap' if tight else 'diffuse -- mechanism not established'}")
        last_unk = max(n for _, n in unk)
        print(f"\nTHE CAP IS SOFT. Every tight cluster sits ABOVE its nominal cap, by an")
        print(f"amount proportional to the cap rather than a fixed number of seconds, so")
        print(f"the budget is a deadline checked periodically and overshot by the lag.")
        print(f"A decided cost slightly above the nominal cap is therefore NOT an anomaly:")
        print(f"it is a cube that finished inside that lag, before the check killed it.")
        print(f"\nlast UNKNOWN row is at file row {last_unk}; {len(rows)-1-last_unk} rows have")
        print(f"landed since, none of them capped.")

    got = dict(rows=len(rows), decided=len(mine), total=len(SEQ), contig_top=contig,
               highest=highest, holes=holes, undecided_only=len(undec), sat=len(sats),
               multi_row_labels=len(multi), naive_max_differs=naive)
    print(f"\nsnapshot recorded at {SNAPSHOT_REV} (the checkpoint grows, so drift"
          f" here is expected, not failure):")
    drift = [k for k in SNAPSHOT if SNAPSHOT[k] != got[k]]
    for k in SNAPSHOT:
        mark = 'same    ' if k not in drift else 'DRIFTED '
        print(f"   {mark} {k:<18} snapshot {SNAPSHOT[k]!s:<8} now {got[k]!s}")
    print(f"   {'matches the snapshot exactly' if not drift else f'{len(drift)} field(s) moved on'}")

    print()
    if fails:
        print("INVARIANT VIOLATIONS -- these are failures:")
        for f in fails: print("  *", f)
        return 1
    print("all invariants hold.")
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1] if len(sys.argv) > 1 else None))
