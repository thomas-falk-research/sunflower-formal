## Claim

The `deg(0) = 13` branch of the `ι(4,11) ≥ 32` rung — the last of the
rung's twenty-one top-degree cubes to rest on a single solver — has been
refuted a second time, independently, by exhausting its full
degree-sequence split under CryptoMiniSat 5.11.15: **1949 sub-cubes, every
one UNSAT, no `SAT` row anywhere in the checkpoint.** The rung's agreement
therefore goes from twenty of twenty-one cubes to **twenty-one of
twenty-one**. About sunflowers themselves: nothing. `ι(4,11) ≤ 31` was
already the standing value and remains it, the verdicts still carry no
proof logs, and a second opinion can confirm but can never discover — only
a `SAT` from CryptoMiniSat would have been news, and there was none in 1949
of 1949. `docs/ladder/deg13_sweep_report.md` is the write-up and
`docs/roadmap.md` §58 the session record.

## What did not move

**`27 ≤ ι(4) ≤ 71` is unchanged at both ends**, from
`Product.iota_four_at_least_27` and
`PureLink.iota_four_at_most_71_if_iota_three_is_ten`. The driver's own
verdict line is about `ι(4,11)`, a different quantity from `ι(4)`, and this
branch does not interconvert them anywhere. `ι(4,11) ≤ 31` does not move
either: it was established before this run and this run corroborates it
rather than extending it.

No bound on `f(n,k)`, no exact value, no row of the `r*(m,3)` table, no
entry of the conjecture ledger, and no constant in `[65, 125]` moved.
`r*(3,3)` stays `{3, 4}` in the tables. **The axiom count is unchanged:
exactly `Sunflower.ALWZ.Rao20_lemma2`.** No Coq module, theorem, definition
or Rust test was added, removed or edited on this branch — the diff against
`main` is solver rows, the tooling that audits them, and prose.

And the rung is **still not a theorem.** Neither solver ran with proof
logging, so by the rule of §56.8 — the same rule that keeps `r*(3,3) = 3`
conditional in §57.1 — every one of the twenty-one cubes is a solver
verdict. Twenty-one cubes with two solvers each and no checked proof among
them is what this branch delivers, and nothing stronger.

## Machine-readable state

```toml
[state]
modules             = 52
audited_theorems    = 789
audited_definitions = 152
mutations           = 175
mutations_killed    = 172
rust_suites         = 43
axioms              = ["Sunflower.ALWZ.Rao20_lemma2"]

[gates]
# Recorded as actually run on this tree, not as hoped. The five that need
# no build were run and pass. The Coq and Rust gates are "not-run": this
# branch touches no Coq module, no Rust source and no tool, so there is
# nothing for them to discriminate, and a gate reported from a previous
# tree would be a claim about that tree. `docs/roadmap.md` 58.5 carries the
# same table for the same reason.
verify        = "not-run"
coqchk        = "not-run"
mutants       = "not-run"
rust          = "not-run"
statements    = "not-run"
docnumbers    = "pass"
ceilings      = "pass"
support15     = "pass"
audit11       = "pass"
audit-support = "pass"

[[claim]]
id       = "deg13-second-opinion-complete"
statement = "The full 1949-sequence split of the deg(0) = 13 cube at (b, g, t) = (4, 11, 32) is exhausted under cryptominisat5 with every sub-cube UNSAT, so the cube is UNSAT under a second solver."
kind     = "measurement"
evidence = "docs/ladder/iota4_11.deg13.cryptominisat5.tsv"
novelty  = "new-to-this-development"
search   = "none run: no novelty is claimed, this corroborates a verdict the development already had"

[[claim]]
id       = "deg13-no-sat-row"
statement = "No index in the checkpoint has any SAT attempt at all, superseded or otherwise, which is invariant I6 of the audit and the single observation the sweep existed to make."
kind     = "measurement"
evidence = "docs/ladder/checkpoint_audit.py"
novelty  = "not-new"
search   = "none run: an invariant over this repository's own data file"

[[claim]]
id       = "soft-cap-is-proportional"
statement = "The per-cube budget overshoots by 0.417 to 1.350 percent of the cap across four recovered caps, proportional to the cap rather than a fixed number of seconds, which excludes a deadline checked on a fixed period and leaves two candidate mechanisms that this evidence does not separate."
kind     = "measurement"
evidence = "docs/ladder/checkpoint_audit.py"
novelty  = "new-to-this-development"
search   = "none run: a property of this run's instrumentation, not of mathematics"

[[claim]]
id       = "span-audit-covers-the-log"
statement = "Every span figure asserted in the operator log is re-derived from the audit's own walk and agrees, 1573 figures at the final state, with contiguity of both tables' ordinals asserted so that a pattern which misses a row fails instead of passing."
kind     = "tooling"
evidence = "docs/ladder/span_audit.py"
novelty  = "new-to-this-development"
search   = "none run: tooling internal to this repository"

[[claim]]
id       = "closed-stdout-skipped-side-effects"
statement = "A truncated pipe closed stdout and killed three scripts before their note rewrite, git add and sample append while the pipeline still exited zero, which is now prevented rather than documented."
kind     = "correction"
evidence = "docs/ladder/safe_stdout.py"
novelty  = "new-to-this-development"
search   = "none run: a defect in this repository's own tooling"

[[claim]]
id       = "cost-monotonicity-asymmetry"
statement = "Of 53 testable blocks 34 keep and 19 break a median-solver-cost monotonicity property, all nineteen breaks are upper-leg failures and none is lower-leg, and the lower leg is readable in 102 blocks and fails in none; this is a statement about solver costs on this instance family and not about the conjecture, iota, or any bound."
kind     = "measurement"
evidence = "docs/ladder/deg13_sweep_note.md"
novelty  = "new-to-this-development"
search   = "none run: explicitly not a mathematical claim"
```

## Results

**The sweep terminated and two independent records agree.** The driver
exited with code 0, printing `# g = 11: UNSAT after 33906.0s (1949 sequence
cubes, 0 at the limit)` and `VERDICT UNSAT  iota(4,11) <= 31   (33906.0s)`
— the seconds being the final resumed pass, not the campaign. The verdict
was not taken from that. `checkpoint_audit.py` re-resolves every row from
the file and regenerates the cube list from the binary's enumeration, and
reports: 2118 data rows against 1949 cubes, verdicts `{UNSAT: 1949,
UNKNOWN: 169}` and nothing else, 0 indices with any `SAT` attempt, 0
unresolved labels, 0 indices decided twice, frontier contiguous `0..1948`,
holes `[]`, decided 1949 of 1949 = 100.0000%, all six invariants hold.

**The cover matters and is recorded.** The split enumerated is the 1949
cover (a family on *at most* eleven points), not the 1939 `--ladder` cover
(*exactly* eleven). UNSAT on all 1949 implies UNSAT on all 1939, so the
second opinion is sound and marginally stronger than the cover it
corroborates; the ten extra sequences are independently redundant, refuted
by `ι(4,10) = 27 < 32`. Rows are never merged between the two files. §52.1
is where this was established, and where the session that conflated them is
recorded.

**Cost distribution over the 1949 decided sub-cubes**, decided cost being
`max(cost)` over a label's non-`UNKNOWN` rows: min 0.1 s, Q1 1178.1 s,
median 2481.5 s, mean 3512.3 s, Q3 4940.6 s, max 21678.5 s, sum 6845530.3 s.
The sum is of final costs and is **not** the campaign's wall clock — cubes
killed by restarts were re-run, the 169 superseded `UNKNOWN` rows are that
record (`1949 + 169 = 2118`), and four solvers ran concurrently. Every
figure is wall time under contention in a shared four-core container and is
**not** comparable with the CaDiCaL rows.

**The budget ladder, at full scale.** The per-cube budget rose from 600 s to
21600 s. At 1800 s the run had stopped producing verdicts entirely and
looked like a cube that had become too hard; it had not, and raising the cap
converted fifteen consecutive stalls, every one landing just above the old
cap and nowhere near the new one. §52.3a called this and the completed run
confirms it. The operational rule: **a run of consecutive stalls is a
statement about the budget, not about the instance, until a larger budget
has been tried.**

**Fifty-six numbered container restarts, zero rows lost.** Append-on-landing
plus "`UNKNOWN` is a budget and not a verdict" held at every one. The check
was never the row count alone — that cannot distinguish a clean teardown
from a lost row — but the row count paired with a waiter armed at the
pre-teardown count reporting no landing, and the relaunched driver's recount
against an independent recount of distinct `UNSAT` labels.

## Negative results, with budgets

**The sweep is exhaustive, not stopped.** All 1949 sub-cubes are decided;
the budget was not left unspent and nothing is undecided. Say "0 labels
undecided-only", never "0 UNKNOWN" — the file holds 169 `UNKNOWN` rows,
each superseded by a later `UNSAT` on the same label.

**Exactly one sub-cube finished above the final cap**, at 21678.5 s against
21600 s, which is the soft-cap behaviour above and not an anomaly.

**The soft-cap mechanism is not identified**, and the branch does not claim
one. A fixed-period deadline is excluded by the proportionality. Of the two
survivors — `--maxtime` on solver CPU time read against a wall-clock record,
or a check interval growing with runtime — the wall-over-CPU excess measured
on 411 distinct in-flight cubes (median 1.608%, full range
0.144%–11.304%) agrees with the first in **magnitude** and disagrees in
**dispersion**, the second is untested, and **this evidence separates
nothing.**

**No proof log was produced, by either solver, for any cube of the rung.**
That is the standing negative and the reason §58.6 names replay as the only
real next step.

## Corrections

**A prediction of mine was over-specific and is withdrawn.** On the last
testable block I wrote that if either of two pending costs exceeded 811.6 s
the median would be `(811.6 + 850.8)/2 = 831.2` outright. Both landed above
811.6 and the median was 858.4. The equality holds only when *exactly one*
is above; the correct general form is the inequality. The block's BREAK
verdict never depended on it.

**A registered trigger's number moved under it.** "BREAK becomes certain
when any of idx 1900/1901/1902 passes 533.8 s" — none did, yet the break
arrived, because 533.8 was conditional on a bound that then rose, moving the
threshold to 425.2, which one of them had already passed. The logic fired;
the number was conditional and was not labelled as such.

**`checkpoint_audit.py` used to assert a soft-cap mechanism that contradicted
its own observation** — a deadline "checked periodically and overshot by the
lag" — when a fixed-period check overshoots by bounded seconds, not by a
fraction of the cap. The assertion is gone and the two surviving candidates
are named without being chosen between.

**A tally of a guard's firings was found short three times** and is deleted
rather than maintained, because a count of a mechanical event kept as prose
beside the mechanism is the same staleness the guard exists to prevent.

**`| head` on a script with side effects is banned**, not merely documented:
it closed stdout, the next `print` raised `BrokenPipeError`, and three
scripts died before their note rewrite, `git add` and sample append while
the pipeline exited zero because the status is `head`'s. Caught at idx 1522
by a one-row note-against-blob disagreement; 40 commits were re-checked and
all agreed, so nothing had been published wrong. `docs/ladder/safe_stdout.py`
makes a closed stdout non-fatal.

**§52.4 is superseded on one clause and says so in place.** Its "cube 13's
second opinion is still outstanding" was true when written and is kept as
the dated record with a pointer to §58; the rest of that paragraph still
holds.

## Reproduction

The result and both audits need no build and no solver:

```
python3 docs/ladder/checkpoint_audit.py              # invariants I1-I6, frontier, caps
python3 docs/ladder/checkpoint_audit.py --spans all  # span record (~20 s)
python3 docs/ladder/span_audit.py                    # every span figure in the log
```

The repository gates that need no build, all run on the final tree of this
branch and all passing:

```
make docnumbers      # 17 quoted numbers match the lists they count
make ceilings        # 9 routes costed, declared verdicts match the arithmetic
make support15       # 61 leaves, exact rationals, max leaf bound 15.9583 < 16
make audit11         # 139 cubes, 0 open, 0 witness rows
make audit-support   # 378 cubes regenerated and equal; needs `pip install
                     # ortools`, without which it exits 1 on the regeneration
                     # half while the row checks still pass
make prcheck PR_BODY=body.md
```

The Coq and Rust gates are reported `not-run` rather than carried over:

```
make -j4 verify      # 52 modules, Coq 8.18.0 -- no Coq source touched here
make coqchk
make statements
python3 tools/mutate.py
cd rust && cargo test --release
```

Re-running the sweep itself needs the driver and CryptoMiniSat, and resumes
rather than restarts against an existing checkpoint:

```
./rust/target/release/examples/iota_sym 4 11 32 --only-deg 13 \
  --solver cryptominisat5 --seqprefix 11 --cubecap 2000 \
  --slice 60 --seconds 21600 --threads 4 \
  --checkpoint docs/ladder/iota4_11.deg13.cryptominisat5.tsv
```

Expect the campaign cost above, and read §6.4 of the report before
extrapolating from a partial run: the enumeration goes easy-to-hard, so any
rate read off the opening rows is an overestimate.

## What a reviewer should attack

**The weakest link is that none of this is a proof.** Twenty-one cubes,
two solvers each, zero proof logs. If both solvers share a defect on this
instance family, agreement is worth nothing, and nothing here rules that
out. The branch says so in four places rather than one, but saying so is
not a mitigation.

**Attack the cover argument next.** Everything rests on "UNSAT on all 1949
implies UNSAT on all 1939". If that containment is wrong, the second
opinion is about a different object than the rung. §52.1 is the argument;
the ten extra sequences are the part to check, and the session that
previously got these two covers backwards is on record.

**Then the soft cap.** A decided cost above its nominal cap is treated as
benign. The report argues proportionality and names two mechanisms without
choosing; if the real mechanism were instead one that could terminate a
solver *early* while recording `UNSAT`, the verdicts themselves would be in
question. Nothing observed suggests that, and nothing observed excludes it
either.

**Least load-bearing, and least defended:** the cost-monotonicity
asymmetry of §58.3. It is 19 of 19 in one direction and 0 of 102 in the
other, which is exactly the shape that invites an inference about the
instances. No such inference is drawn, and a reviewer who thinks the
paragraph reads as if one were should say so — it is a statement about
solver costs only.

## Handover

`docs/roadmap.md` §58 carries the full handover; §58.6 is the "what is
owed" list and it is short, because nothing on this branch is owed. The
rung is as closed as solver verdicts can close it.

**Do not re-run this sweep.** It is complete, the checkpoint is the record,
and a re-run would cost the campaign again to learn nothing. **Do not
relaunch the driver**: `pgrep -x iota_sym` returning nothing is now the
expected state, and the restart-absorption procedure in the operator log
exists for a driver killed mid-run, not for a zero exit carrying a
completion verdict.

The next real step for `ι(4,11)` is the same one §57.2 names for
`r*(3,3)`: replay a solver verdict with a checked proof. Cube 13 is now the
best-corroborated of the twenty-one and therefore the least interesting to
replay; the case for replay runs through whichever cube is cheapest to log.

§57 remains the handover for the `r*(3,3)` line, which this branch does not
touch.
