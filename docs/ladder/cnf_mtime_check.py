#!/usr/bin/env python3
"""Validate the CNF-mtime method for measuring in-flight solver runtime.

THE METHOD
----------
The deg-13 sweep driver (rust/.../examples/iota_sym) writes each sub-cube's
DIMACS file to /tmp immediately before it launches that cube's solver.  So the
CNF's mtime is, up to launch latency, the solver's start time.

That matters at a restart.  When the container is reclaimed the driver dies
without writing rows for its in-flight cubes, and their CPU time is lost.  The
dead driver's CNFs survive in /tmp, so

    lost work for cube i  =  (mtime of the driver's [killed] marker)
                           - (mtime of cube i's CNF)

recovers each discarded cube's runtime exactly, and names which cubes they
were -- with no extrapolation from `ps`, which is gone by then.  The restart
#32 and #33 accounting (c91934e, 1802af3) is computed this way.

WHAT THIS SCRIPT DOES
---------------------
The method's one assumption is that launch latency is negligible.  This script
tests that assumption directly, while a driver is alive, by comparing

    now - mtime(CNF)        (the method)
    ps ELAPSED              (the kernel's own count, independent)

for every solver currently running.  Cubes are paired to pids by reading
/proc/<pid>/cmdline -- the CNF path the solver was actually handed -- not by
matching timings, which would assume the answer.

Run it with no arguments; it samples whatever is running now and prints what
it finds.  It has no expected output and asserts nothing about the live
sample.

WHAT HAS BEEN OBSERVED SO FAR
-----------------------------
Two samples, recorded below as PINNED_SAMPLES and NOT re-derived by the live
run.  Both are from driver pid 374, on the same four in-flight cubes (idx
684, 692, 693, 694), 95 s apart:

    2026-09-15 03:50:01Z   max |now-mtime - ps ELAPSED|  =  0 s   (n = 4)
    2026-09-15 03:51:36Z   max |now-mtime - ps ELAPSED|  =  1 s   (n = 4)

So over n = 8 cube-observations the method agrees with the kernel's own
elapsed count to WITHIN 1 s.  Not to 0 s: the first sample was computed from
integer epoch seconds on both sides, the second from a float clock that is
then rounded, so a sub-second launch latency lands on 0 or 1 depending on
which side of the rounding boundary the sample falls.  Both readings are the
same underlying fact -- launch latency below 1 s -- seen through two slightly
different instruments.

The honest bound is <= 1 s, and quoting the 0 s sample alone would overstate
it.  That very overstatement was written down once before this second sample
was taken; the second sample is what corrected it.  One sample of a quantity
whose instrument has 1 s resolution cannot distinguish 0 from "less than 1".

LIMITS OF THAT OBSERVATION -- read these before relying on it
-------------------------------------------------------------
1.  n = 8 cube-observations, but only 4 distinct cubes, one container boot,
    one driver pid, and two samples 95 s apart.  The two samples are very far
    from independent.  This is a bound, not a distribution.
2.  Both clocks have 1-second resolution.  The delta therefore bounds launch
    latency below 1 s; it cannot resolve the latency itself, and this script
    cannot show the latency is zero.
3.  This validates the LIVE case: one filesystem, one clock, one moment.  The
    restart case compares a surviving CNF mtime against the [killed] marker's
    mtime -- the same launch-latency assumption, but read across two moments
    with a process death in between.  So this is strong evidence for the
    restart accounting, NOT a complete validation of it.  The residual
    untested step is the [killed] marker's own timing, which no live sample
    can reach.
4.  Before running it, this check anticipated "a small positive delta" for
    launch latency.  The first sample showed 0 and the second showed 1, so
    the anticipation is neither confirmed nor refuted at this resolution.
    It was never registered as a commitment and does NOT enter the prediction
    tally.  It is noted only so it is on the record.
5.  A 1 s error is negligible against the quantity the method is used for:
    the smallest per-cube lost-work figure in the ten-restart series is 1.190
    CPU-hours.  1 s is 0.023% of that.  This check bounds the error; it does
    not make the method exact.
"""

import os, glob, re, subprocess, sys, time

CNF_GLOB = "/tmp/sf-sym-*-seq-c*-cryptominisat5-{pid}-*.cnf"
CUBE_RE  = re.compile(r"seq-c(\d+)-cryptominisat5-(\d+)-(\d+)\.cnf")

# (idx, ps_elapsed_s, now_minus_mtime_s, pcpu) per cube.
PINNED_SAMPLES = [
    {"when": "2026-09-15T03:50:01Z", "driver_pid": 374, "clock": "integer epoch",
     "rows": [(684, 6350, 6350, 99.4), (692, 1263, 1263, 99.5),
              (693,  646,  646, 99.1), (694,  259,  259, 98.9)]},
    {"when": "2026-09-15T03:51:36Z", "driver_pid": 374, "clock": "float, rounded",
     "rows": [(684, 6445, 6446, 99.4), (692, 1358, 1358, 99.4),
              (693,  741,  741, 99.0), (694,  354,  354, 99.1)]},
]


def running_solvers():
    """{pid: (elapsed_s, cpu_s, pcpu)} for every live cryptominisat5."""
    try:
        out = subprocess.run(
            ["ps", "-o", "pid=,etimes=,times=,pcpu=", "-C", "cryptominisat5"],
            capture_output=True, text=True, timeout=30).stdout
    except Exception as e:
        print(f"could not run ps: {e}", file=sys.stderr)
        return {}
    res = {}
    for line in out.splitlines():
        f = line.split()
        if len(f) == 4:
            res[int(f[0])] = (int(f[1]), int(f[2]), float(f[3]))
    return res


def cube_of(pid):
    """(cube_idx, driver_pid, cnf_path) read from the solver's own cmdline.

    This is the definitive pairing: it is the file the kernel recorded the
    solver being handed.  Returns None if the process is gone or its
    arguments name no CNF.
    """
    try:
        with open(f"/proc/{pid}/cmdline", "rb") as fh:
            argv = fh.read().decode("utf-8", "replace").split("\0")
    except (FileNotFoundError, PermissionError, ProcessLookupError):
        return None
    for a in argv:
        m = CUBE_RE.search(a)
        if m:
            return int(m.group(1)), int(m.group(2)), a
    return None


def main():
    solvers = running_solvers()
    now = time.time()

    if not solvers:
        print("no cryptominisat5 processes running -- nothing to validate.")
        print("This check only works while a sweep driver is alive.")
        return 0

    rows, unpaired = [], []
    for pid, (et, ct, pc) in solvers.items():
        c = cube_of(pid)
        if c is None:
            unpaired.append(pid)
            continue
        idx, dpid, path = c
        try:
            mt = os.stat(path).st_mtime
        except FileNotFoundError:
            unpaired.append(pid)
            continue
        rows.append((pid, idx, dpid, et, ct, pc, int(round(now - mt))))

    if not rows:
        print(f"{len(solvers)} solver(s) running but none could be paired to a CNF.")
        return 1

    # THIS BLOCK RUNS BEFORE ANY PRINTING, AND THAT ORDER IS LOAD-BEARING.
    # It used to sit at the end of main().  Piping this tool to `head`
    # closes the pipe, and the next print raises BrokenPipeError OUTSIDE
    # this try -- killing the script before it ever appended.  On 2026-09-22
    # it silently lost the 16:41:33Z CHECK-IN sample and the 16:42:51Z
    # reproduction run, while the SAME `| head -11` invocation appended fine
    # at 15:42:08Z: it is a race between the buffer reaching the closed pipe
    # and the script reaching this block, so the loss was silent AND
    # nondeterministic.  `rows` and `now` are both final by here, so doing
    # the write first costs nothing and cannot be raced away.
    # Append this sample to the same log bank.py writes, so there is ONE
    # source for a restart's weighting ratios instead of two.  Before this,
    # bank.py wrote the file and this script only printed, so the freshest
    # ratio could exist solely in a terminal transcript -- which is exactly
    # the archaeology the file was added to stop.  At #42 the two sources
    # disagreed by 3.2 s of CPU across four cubes and gave the same rank, so
    # nothing turned on it; the point is that it should not be possible.
    try:
        stamp = time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime(now))
        out = []
        for pid, idx, dpid, et, ct, pc, _ in sorted(rows, key=lambda r: r[1]):
            if et > 0:
                out.append(f"{stamp}\t{dpid}\t{pid}\t{idx}\t{et}\t{ct}\t{pc}\t{ct/et:.4f}")
        if out:
            path = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                'cpu_ratio_samples.tsv')
            head = not os.path.exists(path)
            # Running this tool twice in one second appends the same rows
            # twice -- harmless for a "last sample per cube" query, but noise.
            # Skip if the file already ends with this stamp for this driver.
            if not head:
                try:
                    with open(path) as fh:
                        tailline = fh.readlines()[-1] if os.path.getsize(path) else ''
                    if tailline.startswith(stamp + '\t'):
                        print(f"\nsample already logged at {stamp}; not appended again")
                        return 0
                except (IndexError, OSError):
                    pass
            with open(path, 'a') as fh:
                if head:
                    fh.write("# iso_utc\tdriver_pid\tsolver_pid\tidx\telapsed_s"
                             "\tcpu_s\tpcpu\tratio\n")
                fh.write("\n".join(out) + "\n")
            print(f"\nappended {len(out)} row(s) to cpu_ratio_samples.tsv at {stamp}")
    except Exception as e:
        print(f"\n!! sample NOT appended: {type(e).__name__}: {e}")

    dpids = sorted({r[2] for r in rows})
    print(f"live sample at {time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime(now))}"
          f"   driver pid(s): {', '.join(map(str, dpids))}   n = {len(rows)}")
    if len(dpids) > 1:
        print("  NOTE: more than one driver pid is present; CNFs from a dead")
        print("        driver must never be mixed into a live measurement.")
    print()
    print(f"{'pid':>6} {'idx':>5} {'ps_elapsed':>11} {'now-mtime':>10} "
          f"{'delta':>6} {'cpu%':>6} {'cpu/elapsed':>12}")
    for pid, idx, dpid, et, ct, pc, derived in sorted(rows, key=lambda r: -r[3]):
        print(f"{pid:>6} {idx:>5} {et:>11} {derived:>10} {derived-et:>6} "
              f"{pc:>6} {ct/et if et else float('nan'):>12.4f}")

    worst = max(abs(r[6] - r[3]) for r in rows)
    print(f"\nmax |now-mtime - ps ELAPSED| over this sample: {worst} s   (n = {len(rows)})")
    print("both clocks have 1 s resolution, so a 0 s delta bounds launch")
    print("latency below 1 s -- it does not show the latency is zero.")
    if unpaired:
        print(f"\nunpaired pids (exited mid-sample, or CNF already removed): {unpaired}")

    print("\nfor reference, the pinned earlier samples:")
    allworst, alln = 0, 0
    for p in PINNED_SAMPLES:
        w = max(abs(d - e) for _, e, d, _ in p["rows"])
        allworst = max(allworst, w); alln += len(p["rows"])
        print(f"  {p['when']}  driver pid {p['driver_pid']}  n = {len(p['rows'])}"
              f"  max |delta| = {w} s  ({p['clock']} clock)")
    print(f"  over all pinned observations: max |delta| = {allworst} s, n = {alln}")
    print("  the live run above is a SEPARATE sample; it does not reproduce")
    print("  the pinned ones and is not expected to.")

    return 0


if __name__ == "__main__":
    sys.exit(main())
