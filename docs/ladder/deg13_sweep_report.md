# A second opinion on the `deg(0) = 13` branch of `ι(4,11) ≥ 32`

**Complete exhaustion of the degree-sequence split under CryptoMiniSat,
1949 of 1949 sub-cubes UNSAT, no satisfiable sub-cube anywhere.**

Run 2026-09-01 to 2026-09-26. Checkpoint
`docs/ladder/iota4_11.deg13.cryptominisat5.tsv`; operator log
`docs/ladder/deg13_sweep_note.md`; session record `docs/roadmap.md` §58.

---

## Abstract

The rung `ι(4,11) ≤ 31` was established previously under CaDiCaL, with
two-solver agreement on twenty of its twenty-one top-degree cubes. The
twenty-first, `deg(0) = 13`, had been decided by a single solver only. We
report the completed second opinion: the cube was split into its 1949
degree sequences and every one was refuted independently under
CryptoMiniSat 5.11.15. The split is exhaustive for the cube, so the cube
is UNSAT, confirming CaDiCaL's verdict on the one branch that lacked
corroboration.

The result is a confirmation, not a new bound. Only a satisfiable
sub-cube would have carried new information, and there was none. The
published bracket `27 ≤ ι(4) ≤ 71` is unchanged, and the driver's own
verdict line concerns `ι(4,11)`, a different quantity from `ι(4)`; the two
are not interconverted anywhere in this report. Both solvers ran without
proof logging, so by this repository's own standard (§56.8) the rung
remains a solver verdict and not a theorem — the second opinion raises the
number of independent solvers behind it from one to two and does nothing
else.

---

## 1. The decision problem

`ι(b)` is the largest `N` for which there exists a `b`-uniform family of
`N` distinct, pairwise intersecting members containing **no 3-sunflower**
— `IotaAtLeast` in `coq/Product.v:123`, with the matching upper-bound
predicate `IotaAtMost` in `coq/IotaRate.v:165`. `ι(b, g)` is the same
quantity with the ground set restricted to `g` points. So `ι(4, 11) ≥ 32`
asks whether 32 such 4-sets fit on eleven points, and a satisfying
assignment is a witness family. The question is decomposed by the degree
of a distinguished point, `deg(0)`; cubes `deg(0) ≥ 15` and `deg(0) = 14`
were closed earlier (§39, §43), and `PureLink.link_at_point_bounded` with
`g_three_at_most_26` excludes `deg(0) ≥ 27`, leaving `deg(0) = 13` as the
last cube of the rung to carry a single solver's word.

### 1.1 The split, and which of two covers it is

`deg(0) = 13` admits **two** distinct degree-sequence covers, and the
distinction is load-bearing:

| cover | size | asks for a family on | file |
|---|---|---|---|
| `--ladder` | 1939 | **exactly** eleven points | `docs/ladder/iota4_11.deg13.tsv` |
| default options | **1949** | **at most** eleven points | `docs/ladder/iota4_11.deg13.cryptominisat5.tsv` |

This run enumerated the 1949 cover. It is the strictly larger of the two:
1939 sequences are shared and ten more carry a degree-zero point, so
**UNSAT on all 1949 implies UNSAT on all 1939**, and the second opinion is
sound and marginally stronger than the cover it corroborates. The ten
extra sequences are redundant on independent grounds, being refuted
already by `ι(4,10) = 27 < 32`. Rows must never be merged between the two
files. See §52.1, which records the session that conflated them.

`all_points_used = FALSE` for this enumeration, so **the cube is UNSAT
only when all 1949 sub-cubes are UNSAT**. No prefix of the sweep licenses
any statement about the cube: at 39.66% decided, the remaining 1176 could
still have contained a satisfiable sequence.

---

## 2. Experimental setup

### 2.1 Software

| component | version | how obtained |
|---|---|---|
| CryptoMiniSat | 5.11.15 | `cryptominisat5 --version` |
| CaDiCaL (baseline, prior run) | 1.7.3 | `cadical --version` |
| Rust toolchain for the driver | rustc 1.94.1 (e408947bf 2026-03-25) | `rustc --version` |

Each `cryptominisat5` process is single-threaded — `--threads` is never
passed to the solver. `iota_sym --threads 4` is cube-level parallelism:
four solver slots run concurrently on distinct sub-cubes.

### 2.2 Driver invocation

```
./rust/target/release/examples/iota_sym 4 11 32 --only-deg 13 \
  --solver cryptominisat5 --seqprefix 11 --cubecap 2000 \
  --slice 60 --seconds 21600 --threads 4 \
  --checkpoint docs/ladder/iota4_11.deg13.cryptominisat5.tsv
```

`--seconds` is the **per-cube** budget, not a total; `--cubecap` bounds the
number of cubes enumerated, not the time. The figure shown is the final
value of a budget that was raised during the campaign (§2.4).

### 2.3 Platform, and what the cost column measures

The sweep ran in a four-core ephemeral session container, at times
alongside `cargo test --release` and `make verify`. **The cost column is
wall-clock seconds under contention**, settled from the source rather than
inferred: `iota_sym.rs` brackets each cube with `Instant::now()` /
`Instant::elapsed()`, so the figure spans the CNF clone, the DIMACS write,
the solver spawn, the solve and the parse. Hence

```
    cost  ≥  the solver process's elapsed time  ≥  its CPU time
```

which is the ordering that makes a running cube's observed CPU/elapsed
ratio a valid *lower* bound on its eventual recorded cost. These figures
are **not comparable with the CaDiCaL rows** in
`docs/ladder/iota4_11.deg13.tsv`, which were taken under different load.

### 2.4 The budget ladder

The per-cube budget was raised repeatedly during the campaign, from an
initial 600 s to a final 21600 s. Each rise is partly recoverable from the
checkpoint, because an `UNKNOWN` row is written exactly when a budget
expires, so each tight cost cluster marks a cap that was in force for part
of the campaign. `checkpoint_audit.py` reconstructs four such caps and two
clusters it declines to attribute:

| nominal cap, s | UNKNOWN rows | cost range, s | reading |
|---|---|---|---|
| — | 3 | 664.5 – 711.3 | diffuse; mechanism not established |
| — | 14 | 820.0 – 1046.8 | diffuse; mechanism not established |
| 1800 | 30 | 1807.5 – 1824.3 | a cap |
| 5400 | 19 | 5428.0 – 5459.3 | a cap |
| 10800 | 81 | 10853.3 – 10939.0 | a cap |
| 21600 | 22 | 21744.1 – 21813.4 | a cap |

The ladder is itself a result, reported in §52.3a: **at 1800 s the run had
stopped producing verdicts entirely and looked like a cube that had become
too hard.** It had not. Raising the cap converted fifteen consecutive
stalls, every one landing between 1872 s and 2781 s — just above the old
cap, nowhere near the new one. The operational rule that follows is that a
run of consecutive stalls is a statement about the budget, not about the
instance, until a larger budget has been tried.

### 2.5 The cap is soft, and by a proportion

Every tight cluster sits **above** its nominal cap, by an amount
proportional to the cap rather than by a fixed number of seconds:

| cap, s | n | over, s | over, % of cap |
|---|---|---|---|
| 1800 | 30 | 7.5 – 24.3 | 0.417 – 1.350 |
| 5400 | 19 | 28.0 – 59.3 | 0.519 – 1.098 |
| 10800 | 81 | 53.3 – 139.0 | 0.494 – 1.287 |
| 21600 | 22 | 144.1 – 213.4 | 0.667 – 0.988 |

The overshoot spans 3.2× as a fraction of the cap where it spans 28.5× in
raw seconds. **A decided cost slightly above its nominal cap is therefore
not an anomaly**, and exactly one of the 1949 final costs is above the
final cap, at 21678.5 s against 21600 s.

The mechanism is **not settled, and this report does not assert one.** A
deadline checked on a fixed period would overshoot by bounded *seconds*,
not by a fraction of the cap, so that explanation is excluded by the
observation. Two candidates survive: (i) `--maxtime` enforced against the
solver's CPU time while the checkpoint records the driver's wall time; and
(ii) a check interval that itself grows with runtime. CryptoMiniSat's
`--help` names no clock for `--maxtime`. Against (i), the wall-over-CPU
excess measured on 411 distinct in-flight cubes has median 1.608%, p5–p95
0.515%–4.367% and full range 0.144%–11.304%; the overshoot band sits
inside that range, so the two agree in *magnitude*, but the excess is far
more dispersed than the overshoot, which under (i) should inherit its
spread and does not. **The magnitudes are consistent with (i), the shapes
are not, (ii) is untested, and this evidence separates nothing.**

---

## 3. Protocol

### 3.1 Checkpointing and resumption

A row is appended the instant a sub-cube lands, so a reclaimed container
loses only work in flight. On resume against the same `--checkpoint`,
`UNSAT`/`SAT` rows are skipped and `UNKNOWN` rows are re-run, because
**`UNKNOWN` is a budget and not a verdict**. This is why the file holds
more rows than cubes.

### 3.2 Restart absorption

The campaign was interrupted repeatedly by container reclamation. The
operator log numbers restarts to **#56** and records **zero rows lost at
any of them**. Each absorption was checked the same way: the driver's own
stdout ends with a row and then `[killed]`, that row is the last row in
the file, the row count is equal on both sides of the teardown, and a
waiter armed at the pre-teardown count reports no landing. The relaunched
driver then prints its own recount (`checkpoint: N of 1949 cubes already
decided`) which was compared against an independent recount of distinct
`UNSAT` labels.

Two properties of this protocol are worth separating. The row-count
equality alone is *not* sufficient — a lost row and a clean teardown look
the same to it if the waiter missed a landing — which is why the waiter is
the independent half of the check and not a convenience.

### 3.3 Reading the checkpoint correctly

Four conventions are needed to read the file without error, each of which
cost a recorded mistake to establish:

1. **Rows land in completion order, never index order.** A row below the
   previous landing is a straggler, not a regression.
2. **Holes in the frontier are work in flight.** A long-running hole is
   not a stall; a stall is an `UNKNOWN` row written at the cap plus
   0.4–1.4%, never silence.
3. **Decided cost** = `max(cost)` over that label's non-`UNKNOWN` rows. 80
   labels carry multiple rows, and in 27 of them a naive maximum over
   *all* rows differs from the decided cost.
4. Say **"0 labels undecided-only"**, never "0 UNKNOWN": the file holds
   169 `UNKNOWN` rows, each superseded by a later `UNSAT` on the same
   label.

---

## 4. Results

### 4.1 Termination

The driver exited with **code 0**, printing

```
# g = 11: UNSAT after 33906.0s (1949 sequence cubes, 0 at the limit)
VERDICT UNSAT  iota(4,11) <= 31   (33906.0s)
```

The 33906.0 s is the final resumed pass, not the campaign. A zero exit
carrying a completion verdict is the opposite of a driver killed mid-run,
so the restart-absorption procedure of §3.2 does not apply to it and
nothing was relaunched.

### 4.2 The checkpoint, independently

The verdict was not taken from the driver's word. `checkpoint_audit.py`
re-resolves every row from the file and regenerates the cube list from the
binary's enumeration:

```
2118 real data rows, 1949 cubes in the regenerated list

I1 structure        rows malformed: 0
I2 fields           verdicts {'UNSAT': 1949, 'UNKNOWN': 169}, non-numeric costs 0
I3 resolution       unresolved labels: 0; distinct indices touched: 1949
I4 single decision  indices decided more than once: 0   (multi-row labels: 80)
I5 second opinion   agrees with shipped decided(): True   (1949 decided)
I6 no SAT           indices with any SAT attempt: 0

frontier contiguous 0..1948, highest decided 1948, holes []
done 1949 of 1949 = 100.0000%, remaining 0
undecided-only indices: 0   (UNKNOWN rows in file: 169, the rest superseded)

all invariants hold.
```

**I6 is the load-bearing invariant of the whole sweep.** There is no `SAT`
row in the file at all — not one superseded, not one retracted — and that
is the single observation the run existed to make.

### 4.3 Cost distribution over the 1949 decided sub-cubes

Computed from the checkpoint under the §3.3 definition of decided cost:

| statistic | value, s |
|---|---|
| minimum | 0.1 |
| 5th percentile | 352.1 |
| first quartile | 1178.1 |
| median | 2481.5 |
| mean | 3512.3 |
| third quartile | 4940.6 |
| 95th percentile | 10206.0 |
| maximum | 21678.5 |
| **sum** | **6845530.3** (1901.54 h) |

| threshold | sub-cubes |
|---|---|
| under 60 s | 17 |
| under 600 s | 224 |
| over 3600 s | 700 |
| over 10800 s | 71 |
| over 21600 s (the final cap) | 1 |

The sum is the sum of the 1949 **final** costs. It is **not** the
wall-clock cost of the campaign: cubes killed by restarts were re-run, the
169 superseded `UNKNOWN` rows are the record of that re-running
(`1949 + 169 = 2118`), and four solvers ran concurrently throughout. For
scale rather than for comparison, CaDiCaL decided the same cube whole in
85123.9 s (`docs/ladder/iota4_11.tsv`), and §40's uniform sample put a
floor of ≥ 3319 core-hours on the 1939-cover split under CaDiCaL. Running
a split is a deliberate choice to pay more total time for the ability to
stop and resume; that choice is what made this result reachable at all
after the whole-cube route failed twice (55.6 h to a crash, §51; a week to
nothing, §45.4).

### 4.4 An observation about solver costs, which is not evidence about `ι`

The sweep's blocks — the first four entries of a degree sequence — were
tracked for a monotonicity property of median solver cost across
neighbouring groups. At completion, all 171 blocks were decided; 53 were
testable; of those, 34 kept the property and 19 broke it. **All nineteen
breaks are upper-leg failures and not one is a lower-leg failure.** The
lower leg is readable in 102 blocks — the 53 testable plus 49 untestable
ones carrying both groups — and failed in none of them.

This is recorded because it was measured over its whole range rather than
sampled, and because the asymmetry is total. **It is a statement about
solver costs on this instance family, not about the Sunflower Conjecture,
not about `ι`, and not about any bound.** No inference from it is drawn
anywhere in this development, and the caveat is not softened by the count
being complete. Figures computed from the staged checkpoint at commit
`48c5787`.

---

## 5. Verification

Five independent checks stand behind §4, and they are listed with what
each does **not** cover.

1. **`checkpoint_audit.py`** re-resolves every row and regenerates the
   cube list from the enumeration, so a row naming a label outside the
   split fails I3. It does not check the solver's reasoning — see §6.1.
2. **`span_audit.py`** re-derives **every** figure the operator log
   asserts about hole-chain spans against the audit's own walk: durations,
   both ranks, both denominators, tie counts, chain shas, verdicts,
   comparison counts, the opening-width census prose and the monotonicity
   prose. It reports how many figures it checked and asserts contiguity of
   both tables' ordinals, so a pattern that silently misses a row fails
   rather than passing. At the final state: **1573 figures checked, 189
   closed spans walked, 110 spans-table rows, 124 monotonicity rows, every
   parsed figure in agreement.** It was adversarially validated — proved
   to fail on a wrong rank, a flipped verdict, a mutated hole chain, a
   deleted row, twelve census mutations and fifteen monotonicity-prose
   mutations, each mutation verified to have changed the file before its
   run was scored.
3. **`bank.py`** owns every state figure in the operator log and rewrites
   all of them from the *staged* blob in one run, refusing loudly rather
   than writing a figure it cannot justify. At completion it refused to
   rewrite the driver's process line, reporting `DRIVER LINE NOT
   REWRITTEN: pgrep -x iota_sym returned 0 pid(s)` — the guard behaving as
   designed: it will not invent a process id and will not silently keep a
   dead one.
4. **The two-clock finish test and the elapsed floor.** A cube's own
   elapsed clock and its replacement's start each bound its finishing
   instant with no reference to the file's write time; and `cost ≥ elapsed`
   is sound within a run. Both were used to bound in-flight cubes during
   the sweep. The floor is **destroyed by a restart** and was treated as
   such.
5. **`cnf_mtime_check.py`** validates the CNF-mtime method for pairing
   in-flight cubes with solver processes, which is what established
   whether a prediction's target was still unobserved at the moment the
   prediction was made.

A measured limitation of the instrumentation: the sampler's own clock
carries about one second of slop, demonstrated by one cube whose start,
read from two samples, gave adjacent *disjoint* one-second windows, and
corroborated independently by comparing `ps` elapsed against `now −
mtime`. All write-lag bounds derived here are therefore treated as two
seconds wide.

---

## 6. Limitations

### 6.1 No proof logs: this is a solver verdict, not a theorem

Neither solver was run with proof logging, so nothing here is machine-
checked in the sense this repository reserves that word for (§56.8, and
the `r*(3,3)` precedent in §57.1 where a CP-SAT verdict is held
conditional for exactly this reason). The honest statement of the rung's
standing is:

> `ι(4,11) ≤ 31` rests on solver verdicts. Every one of its twenty-one
> top-degree cubes now has agreement from two independent solvers. None of
> the twenty-one has a checked proof.

Replaying any of it with DRAT or VeriPB would be a strictly stronger
result and is not attempted here.

### 6.2 What the confirmation can and cannot do

A second opinion **can confirm and can never discover.** Had
CryptoMiniSat returned a satisfiable sub-cube, that would have refuted
CaDiCaL's verdict and been the finding of the campaign. It did not, in
1949 of 1949. The information content of agreement is the removal of a
single-solver dependency, and that is all of it.

### 6.3 Timings are not a benchmark

Every cost in §4.3 is wall time under four-way contention in a shared
container, with `cargo test` and `make verify` running at times alongside.
The figures are adequate for the soft-cap analysis, which is internal and
proportional, and are **not** a measurement of solver performance and not
comparable with the CaDiCaL rows.

### 6.4 The enumeration order makes early throughput misleading

The split runs lexicographically descending, and that order is **easy to
hard**, not hard to easy: a degree sequence with its mass concentrated on
few points is more constrained and so cheaper to refute, and those come
first. Measured at a fixed 1800 s cap, consecutive blocks of eight stalled
at 0%, 75%, 88%, 88%, 100%. Any rate read off the opening rows of a
checkpoint is an overestimate. This is why no completion estimate appears
in this report.

---

## 7. What did not move

**`27 ≤ ι(4) ≤ 71` is unchanged**, from `Product.iota_four_at_least_27`
and `PureLink.iota_four_at_most_71_if_iota_three_is_ten`. The driver's
verdict line is about `ι(4,11)`; `ι(4,11) ≤ 31` was already the standing
value before this run and remains it. **This sweep changed the number of
solvers behind one cube of one rung, and nothing else.**

No bound on `f(n,k)`, no exact value, no row of the `r*(m,3)` table, no
entry of the conjecture ledger, and no constant in `[65, 125]` moved. No
Coq module, theorem or axiom was touched: the axiom count is unchanged at
exactly `Sunflower.ALWZ.Rao20_lemma2`. Nothing about a long unbroken run
of `UNSAT` results licenses more than what the rows say.

---

## 8. Reproduction

The checkpoint and both audits need no build and no solver:

```
python3 docs/ladder/checkpoint_audit.py            # invariants I1-I6, frontier, caps
python3 docs/ladder/checkpoint_audit.py --spans all  # span record (~20 s)
python3 docs/ladder/span_audit.py                  # every span figure in the log
```

Re-running the sweep itself requires the driver and CryptoMiniSat, and the
command in §2.2 resumes rather than restarts against an existing
checkpoint. Expect the full campaign cost of §4.3, and note §6.4 before
extrapolating from a partial run.

To verify a single claim of this report rather than all of them, the
corresponding commit is the record: the completion is `48c5787`, whose
message carries the final figures as they were computed from the staged
blob.

---

## 9. Artifacts

| path | what it is |
|---|---|
| `docs/ladder/iota4_11.deg13.cryptominisat5.tsv` | the checkpoint: 2118 rows, one per landing. **The authoritative result.** |
| `docs/ladder/deg13_sweep_note.md` | the operator log, 38 680 lines, written as the sweep ran |
| `docs/ladder/checkpoint_audit.py` | re-resolves the checkpoint; six invariants; frontier, holes, caps, span record |
| `docs/ladder/span_audit.py` | checks every span figure the log asserts against the audit's walk |
| `docs/ladder/bank.py` | rewrites the log's state figures from the staged blob; refuses rather than guesses |
| `docs/ladder/refig.py` | refigures the spans table at a span close, reproducing carried rows at the old count first |
| `docs/ladder/cnf_mtime_check.py` | validates CNF-mtime pairing of in-flight cubes to processes |
| `docs/ladder/forward_test.py` | cube-list and label helpers, pinned to `REV_AS_RUN = 9528aa9` |
| `docs/ladder/safe_stdout.py` | makes a closed stdout non-fatal, so a truncated pipe cannot skip a script's side effects |
| `docs/ladder/cpu_ratio_samples.tsv` | append-only CPU/elapsed samples for in-flight cubes; 9076 lines, one of them a header |

The operator log is a working document and retains its running commentary,
including its own corrections. It is the narrative record; **the commit
history is authoritative over both it and this report.** Where this report
and a commit disagree, the commit wins.

---

## 10. Cross-references

| section | what it holds |
|---|---|
| `docs/roadmap.md` §52.1 | the two covers, 1939 against 1949, and the session that conflated them |
| `docs/roadmap.md` §52.2 | why the full split and not the prefix-3 split |
| `docs/roadmap.md` §52.3 | the cost of choosing a split over the whole cube |
| `docs/roadmap.md` §52.3a | the budget ladder, and why a binding cap looks like a hard cube |
| `docs/roadmap.md` §52.4 | what that session did not do — **superseded on the second opinion by §58** |
| `docs/roadmap.md` §58 | this run's session record |
| `docs/roadmap.md` §39, §43 | `deg(0) = 14` and the cubes from 15 up |
| `docs/roadmap.md` §40.2 | the contention caveat on ladder timings |
| `docs/roadmap.md` §50, §51 | the crash-versus-budget defects in the machinery that planned this run |
| `docs/roadmap.md` §56.8 | the rule that a solver verdict without a proof log is not a theorem |
| `STATUS.md` | the standing tables, and `two_cover_degree_sum` on what is left of the rung |
