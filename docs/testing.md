# Testing a formalization

A machine-checked proof is not a machine-checked *claim*. The kernel
guarantees that every proof follows from the definitions; it has
nothing to say about whether the definitions mean what their names
say. Every error this development has produced has been of the second
kind:

1. **A degenerate definition.** An early version defined spreadness by
   quantifying over all lists `T`, including lists with repeated
   entries. Taking `T = [x; x; ...; x]` then forces `w^t · deg{x} ≤
   |F|` for every `t`, so no member of a "spread" family may contain
   any element at all. Every proof about spread families still
   compiled — they were proofs about the empty family. The defect is
   now recorded as a theorem, `Spread.w_spread_legacy_degenerate`.

2. **A misquoted hypothesis.** The axiom standing in for the 2020
   spread lemma was stated with the *fractional* spread condition,
   where the source (Rao, Lemma 2) uses the *absolute* one together
   with a size hypothesis. The two are not the same, and the
   difference runs in the direction that matters for an axiom: the
   absolute form is stronger, so assuming a conclusion under the
   fractional form assumes more. Nothing in the build could notice.
   `Spread.RaoSpread_Spread` now machine-checks the implication, so
   the direction of the strengthening is itself a theorem.

Neither error was found by the kernel. Both were found by rereading
the source. This document describes the seven mechanisms added so that
a third one does not have to be.

None of them is a substitute for reading the paper. All of them are
cheaper than reading it again.

---

## 0. Independent re-checking — `make coqchk`

Before the definition-level checks, one thing worth tightening at the
kernel level.

`make verify` runs `Print Assumptions` on a list of theorem names
enumerated in the Makefile. That is exactly as complete as the list.
An `Admitted` lemma somewhere else in the development, a second
`Axiom`, or a global `Parameter` would not appear — the audit would
report every name on the list as closed, and pass. This is not
hypothetical: appending

```coq
Lemma smuggled_in : forall n : nat, n = n + 0.
Proof.
Admitted.
```

to `coq/Sets.v` compiles, and the `Print Assumptions` audit stays
green.

`coqchk` is a separate program from `coqc`. It re-typechecks the
compiled proof terms with its own kernel implementation — no
elaborator, no tactics, no unification — and prints a census of the
**whole library**:

```
* Theory: Set is predicative
* Axioms:
    Sunflower.ALWZ.Rao20_lemma2
* Constants/Inductives relying on type-in-type: <none>
* Constants/Inductives relying on unsafe (co)fixpoints: <none>
* Inductives whose positivity is assumed: <none>
```

CI gates on that axiom list being exactly one name, and on all three
escape hatches being empty. With the admit above in place the census
reads `Sunflower.Sets.smuggled_in` and the gate fails, which is the
point.

Two claims this makes good on that `Print Assumptions` alone does not:
"zero admits **anywhere**", and "no reliance on type-in-type, unsafe
fixpoints, or assumed positivity" — none of which anything checked
before.

---

## 1. Coherence theorems — `coq/Audit.v`

The cheapest defence is to ask the definitions questions whose answers
are known in advance, and check that the machine agrees. Nothing in
`Audit.v` is used to prove any bound; every theorem there exists to
fail if a definition drifts.

| Question | Theorem |
|---|---|
| Are `UpperBound` and `LowerBound` complementary? | `lower_bound_excludes_upper`, `lower_lt_upper` |
| Is `ContainsKSunflower` a property of the sets, or of the list encoding? | `ContainsKSunflower_equiv`, `ContainsKSunflower_perm` |
| Is a sunflower's core determined by its petals? | `sunflower_core_unique` |
| Is `Distinct` doing work beyond `NoDup`? | `distinct_strictly_stronger` |
| Is `UpperBound` ever false? | `no_upper_bound_below_exponential` |
| Is the axiom's conclusion ever false? | `spread_yields_disjoint_sandwich`, `no_spread_yields_disjoint_2_3_2` |
| Do the development's own bounds fit in one order? | `bounds_coherent_er`, `bounds_coherent_spread`, `bounds_coherent_f_2_3` |

Two of these deserve comment.

**The bounds-coherence corollaries are not restated arithmetic.** Each
is obtained by feeding two of the development's theorems to
`lower_lt_upper`. If the exponential lower bound and the Erdős–Rado
upper bound were mutually contradictory — if one of them were
misstated badly enough — then `bounds_coherent_er` would be a
derivation of `False` from machine-checked theorems, and would fail to
be provable in the form written.

**The axiom's shape is sandwiched.** `SpreadYieldsDisjoint n k r` is
the shape of `ALWZ.Rao20_lemma2`. If it held for every `r`, the
axiom's threshold hypothesis would be decoration and the axiom would
be assuming nothing. `spread_yields_disjoint_sandwich` pairs two
proofs:

* **false below `k-1`** — a family of `k-1` pairwise disjoint blocks
  is as spread as a family can be, satisfies every hypothesis when
  `r^m < k-1`, and obviously has no `k` pairwise disjoint members;
* **true above `n(k-1)`** — `SpreadReduction.spread_disjoint_above_
  elementary`, a strengthening of the elementary spread lemma to every
  `r` past that line.

So the axiom is asserting something about the gap in between: neither
vacuous nor already proved.

The disjoint-blocks family is blind at `k = 3`, where it only rules out
`r = 1`. The five-cycle `Audit.c5` rules out `r = 2` at uniformity
`m = 2`, which no family of singletons can — so the threshold genuinely
grows with the uniformity, which is the qualitative content of the
`log` factor in the published bound. That family came out of the search
described in §3.

`no_spread_yields_disjoint_2_3_2` is proved twice, by arguments that
share no step: once by counting ground-set elements (three pairwise
disjoint 2-sets need six, the cycle has five), and once through
`F23.two_triangles` and the reflective 3-sunflower detector, via
`no_k_disjoint_of_no_sunflower`. Two independent routes to the same
refutation is the point. If they disagreed, one of the two notions
would not mean what its name says.

## 2. A second opinion on the decision procedure — `coq/Reflect.v`

`Spread.rao_witness` decides spreadness by searching the sublists of
the *members* of `F`. That is what keeps the reduction constructive,
and `Spread.rao_witness_none` justifies it. But the justification is a
proof *about* `Spread.cands`: if `cands` enumerated too few candidate
violators, the procedure would report "spread" for families that are
not, and the reduction would be silently weakened rather than broken.
No proof in the development would fail.

`Reflect.rao_spreadb` is a second implementation sharing no code with
the first: it enumerates the subsets of an explicitly supplied ground
set. `Reflect.rao_witness_agrees` proves the two always return the same
verdict. That is a differential test between two independent search
strategies, discharged by the kernel rather than by sampling —
`rao_witness_complete` states the consequence directly: a `None`
verdict is never a false negative.

The mutation `cands-members-only` (§4) shrinks `cands` to exactly the
failure this guards against, and confirms the guard bites.

`Reflect.v` also collects the boolean certificates for the family
predicates, each proved in **both** directions. Soundness
(`b = true → P`) is all a proof needs. Completeness (`P → b = true`)
is what makes a `vm_compute` returning `false` count as evidence
*against* `P` — and every concrete refutation in `Audit.v` rests on
the completeness half. A check that can only ever succeed is not a
check.

## 3. Exhaustive falsification — `rust/src/testbed.rs`

For small parameters the spread hypothesis is decidable, so it can
simply be tested. `make testbed` enumerates every family of
`m`-subsets of a ground set of size up to 8, keeps those satisfying
every hypothesis of `SpreadYieldsDisjoint`, and checks whether each
really does have `k` pairwise disjoint members.

The search is a depth-first walk over families. Both constraints that
define a counterexample are hereditary — degrees only grow when
members are added, and so does the matching number — so backtracking
the moment either breaks visits exactly the constrained families and
no others. A vertex-degree counting bound prunes branches that can no
longer reach the size threshold. The whole grid runs in about twenty
seconds.

What it proves and what it does not: the search is complete for
families over the given ground set and says nothing about larger ones.
That is the right trade, because counterexamples to a misstated finite
hypothesis are small. The published lemma's own threshold is
`Θ(k log(km))`; a statement error large enough to matter shows up well
within reach.

The gates in `rust/tests/spread_axiom.rs`, in increasing order of what
they would catch:

* **The search is right.** It is validated against unpruned
  enumeration of every single family, on both the counterexample
  verdict and the largest constrained family
  (`search_matches_brute_force`).
* **Coq theorems, re-derived computationally.** No counterexample above
  the proved-sufficient threshold `m(k-1)+1`; the empirical threshold
  never exceeds it; `RaoSpread` plus the size hypothesis implies the
  fractional condition; the two spread decision procedures agree; `k`
  pairwise disjoint members and a `k`-sunflower with empty core are
  the same thing. Each of these fails if the Rust reading of a Coq
  definition differs from the Coq one — which is exactly a
  misstatement.
* **Coq refutations, re-derived.** The counterexample families named in
  `Audit.v` are found by the search; on five points *every*
  counterexample at `(m,k,r) = (2,3,2)` is a relabelling of the
  five-cycle, which is what makes it the natural one to formalise.
* **Non-vacuity at the published threshold.** Circulant graphs supply
  families satisfying every hypothesis of the axiom at
  `r = k·log₂(km+1)` — taking the most demanding `α = 1` — so the
  axiom is not assuming the empty statement. This is the degeneracy
  of §0 checked at a real parameter rather than a toy one.

The empirical threshold table is printed into the build log:

```
  ground  m   k   empirical r*   proved sufficient   refuted r
       4  1   2              1                   2   -
       6  1   3              2                   3   1
       8  1   4              3                   4   1,2
       8  1   5              4                   5   1,2,3
       4  2   2              1                   3   -
       5  2   3              3                   5   1,2
       6  2   3              3                   5   1,2
       7  2   3              3                   5   1,2
       8  2   3              3                   5   1,2
       8  2   4              4                   7   1,2,3
       6  3   2              1                   4   -
       6  3   3              2                   7   1
       7  3   3              3                   7   1,2
       8  3   3              3                   7   1,2
```

`r*` is the least `r` above which no counterexample exists; the next
column is `m(k-1)+1`, proved sufficient in Coq. `r*` must never exceed
it, and at `m = 1` it is exactly `k-1`, matching
`Audit.spread_yields_disjoint_needs_r` on the nose.

Three things the table is checked for beyond that.

**The refuted `r` form a prefix.** Nothing forces this: raising `r`
weakens the spread hypothesis and simultaneously raises the size
threshold `r^m`, so the two hypotheses pull in opposite directions, and
a refuted `r` above an unrefuted one would mean the axiom's threshold
cannot be read as "large enough `r`" at all. At uniformity 2 the prefix
property follows from the Chvátal–Hanson formula; at uniformity 3 there
is no formula, and `the_refuted_set_of_r_is_a_prefix` is search.

**The `k = 2` row at uniformity 3 is decided by one member.** No `r` is
refutable there, and the reason is the **Fano plane**: seven lines on
seven points, every point on three and every pair on exactly one, so
`deg T <= r^(3-|T|)` holds in all three clauses at `r = 2` — the last
with equality. It is intersecting, so it has no two disjoint members,
and nothing on seven points does better. It has seven members where the
size hypothesis asks for more than `r^m = 8`, and misses by one.
`the_fano_plane_misses_the_size_hypothesis_by_one` pins every part of
that. A size hypothesis mis-transcribed as `>=` rather than `>` would
turn the Fano plane into a counterexample to the axiom — which is what
the `syd-nonstrict-size` mutation asks of the Coq statement, so the two
checks meet on the same family.

**Where the search stops is not arbitrary.** At `(m, k, r) = (3, 3, 3)`
a counterexample needs more than 27 members of size 3 with every vertex
in at most `r^(m-1) = 9` of them, hence at least `ceil(3*28/9) = 10`
vertices. Ground 10 is therefore the first ground set that could hold
one, and it is exactly where the search stops finishing within an hour.
So the uniformity-3 rows are complete over ground sets that provably
cannot contain a counterexample, and say nothing past that line.

### A second thing falsified before it was proved

The same machinery, pointed at a statement rather than at the axiom.
`LinkCharacterisation.sunflower_iff_link_matching` says a family has a
`k`-sunflower exactly when some link of it has `k` pairwise disjoint
members. Before any of it was written in Coq,
`rust/tests/link_characterisation.rs` enumerated the equivalence against
the brute-force pairwise-intersection detector in `sunflower.rs` — which
knows nothing about links — over every family on five and six points at
uniformities 2 and 3, over every family of *arbitrary* sets on four
points, and over a deterministic sample at ground 7. The witnesses are
checked to cross over in both directions, not only the two booleans.

It found something. Under uniformity the equivalence is insensitive to
whether the empty petal counts: at uniformity `m` at most one member can
equal a given core, so the empty petal never has a second petal to be
disjoint from. Without uniformity it does, and the equivalence needs it
to count — `{1}, {1,2}, {1,3}` is a 3-sunflower with core `{1}` whose
first member contributes the empty petal.
`Sunflower.pairwise_disjoint_sunflower` carried a nonemptiness
hypothesis that excluded exactly that case, and it was decoration in
three other lemmas and in `Audit.no_k_disjoint_of_no_sunflower` besides.
Deleting it was the first commit of the Coq work, not a repair after the
fact.

### A third: the direct sum, and where the exhaustive grid stops

`rust/tests/direct_sum.rs` does the same job for
`DirectSum.sum_family_no_sunflower`: every pair of `k`-sunflower-free
families drawn from small ground sets, summed and handed to the same
brute-force detector, which knows nothing about direct sums. The pair
count is *pinned* (`assert_eq!(pairs, 4266)`) rather than bounded from
below, and the derivation is written out in the test, because the
failure mode of an exhaustive test is that it quietly stops being
exhaustive.

One cell of the grid is excluded and the comment says which: at `k = 4`
every one of the 64 subfamilies of `K_4`'s edges is 4-sunflower-free, so
`(4,2) x (4,2)` is 4096 pairs whose sums have 36 members apiece, each
needing `C(36,4) = 58905` quadruples decided. A silent truncation there
would read as "covered everything".

The suite also pins the two hypotheses. Uniformity: `{0}, {0,1}` and
`{2}, {2,3}` are sunflower-free on disjoint ground sets and their sum is
not — the same counterexample `Audit.uniformity_is_needed_in_the_direct_sum`
carries into the kernel. Cross-disjointness: overlapping ground sets
make the concatenation repeat a point, so `is_valid_family` fails before
any sunflower question is asked.

Two things came out of writing it rather than out of the proof, and both
were errors in the *test*, which is the failure mode a test suite has:

* a claim that collapsing `two_triangles` by `x mod 3` creates a
  3-sunflower. It does not — it creates duplicate members, so the image
  is not a family at all. That is a real fact about why injectivity is
  needed, but it is a different one, and the test now checks both
  (`{0,1}, {0,2}, {3,4}` merged at `3 -> 0` is the case that genuinely
  creates a sunflower);
* a claim that the largest sum in the grid has 36 members. It has 16: at
  `k = 3` a subfamily of `K_4` needs maximum degree at most 2, which
  caps it at the 4-cycle. The 6-edge families only survive at `k = 4`,
  which is the excluded cell.

Neither was a problem with the theorem. Both would have made the suite
claim more coverage than it had.

### And one the mutation runner found, in the Coq

`sum_family_no_sunflower` was stated with six hypotheses:
`Uniform a F1`, `Distinct F1`, `Uniform b F2`, `Distinct F2`, the two
sunflower-freeness assumptions, and cross-disjointness. The mutation
`directsum-drop-uniformity` was written to check that the *second*
uniformity was load-bearing, and the runner reported it killed — but
reading the failure showed the kill came from the call site in
`lower_bound_sum`, not from the proof. The proof never used
`Uniform b F2`, nor `Distinct` on either side.

So the theorem was stronger than its statement: only the family split
off the front has to be uniform, and neither has to be distinct. The
statement was narrowed to what the proof needs, the mutation retargeted
at `Uniform a F1` (where it is killed by the mathematics, at the step
that needs `|A| = a`), and the sharper claim enumerated in
`rust/tests/direct_sum.rs` with `F2` ranging over families of arbitrary
subsets. This is the manifest doing the job the header describes: a
hypothesis no theorem is sensitive to is one that should not be there.

The same run turned up a second thing. `lowerbound-at-least` — the
development's one genuine survivor, which weakens `LowerBound`'s
`length F = m` to `>=` — was killed by the new file, because two of its
proofs discharged a size obligation by `reflexivity` and by `rewrite`ing
with the length equation. Neither is sensitive to the *content* of
`LowerBound`, only to its shape. They now finish with `lia` and `nia`,
and the survivor is a survivor again.

The two mutations that establish the tests bite, run by hand before the
suite was committed:

| Mutation of `link.rs` | Killed by |
|---|---|
| drop the empty petal from `link` | the non-uniform enumeration only — both uniform suites pass |
| restrict candidate cores to `∅` and the singletons | uniformity 3, the non-uniform enumeration, and the ground-7 sample — uniformity 2 passes, which is `two_uniform_only_small_cores` |

Neither is in `tools/mutations.toml`: that manifest perturbs Coq
definitions, and these perturb the Rust oracle. They are recorded here
because "the check would have caught it" is a claim, and an unrun claim
is worth what an untested proof is.

## 4. Mutation testing — `tools/mutate.py`

The three mechanisms above test the definitions the development *has*.
Mutation testing asks a different question: **is each hypothesis in
each definition doing any work at all?**

The procedure is the standard one, pointed at definitions rather than
code. Weaken one hypothesis — drop a `NoDup`, turn `=` into `≥`, swap
`<` for `≤`, flatten an exponent — rebuild, and see whether anything
breaks.

* A mutation that is **killed** identifies a load-bearing hypothesis,
  and names the file that depends on it.
* A mutation that **survives** identifies a hypothesis nothing in the
  development is sensitive to. Sometimes benign; sometimes it means a
  condition is decorative, which is the shape of a misstatement.

One entry is a **positive control**: `canary-alpha-rename` renames a
bound variable in `Sets.Subset`, which by alpha-equivalence is not a
change to the development at all, and is declared `survived`. Without
it, a harness whose sandbox failed to build for some unrelated reason
would report every mutation killed and pass with flying colours — and
the `survived` code path would never execute, since nothing else in
the manifest exercises it. The runner warns if the manifest has no
control.

`tools/mutations.toml` records, for each mutation, the question it
asks and the outcome expected. The runner checks the expectations, so
the manifest is a **regression test on the load-bearingness of every
hypothesis**, not merely a report: if a future refactor makes some
hypothesis stop mattering, CI fails.

It also refuses to run against a stale manifest. Each `find` string
must occur exactly once in its file; a mutation that silently failed
to apply would report as run and make the whole exercise meaningless.

### Two kinds of kill

Mutation testing a proof assistant has a wrinkle that mutation testing
a program does not: a build can break for reasons that have nothing to
do with the mathematics. `apply H` fails when the goal has turned from
`length F = m` into `length F ≥ m`, even though the statement is still
true and still provable. A harness that counts that as a kill
over-reports — it credits a hypothesis with mattering when only a
tactic noticed.

So a mutation may declare `repairs`: purely tactical edits, touching
no statement, that adapt the proof scripts. If the development builds
again once they are applied, the kill was script level and the runner
reports `killed-script` rather than `killed`. That distinction is
machine-checked, not asserted.

No mutation in the current manifest lands there, and the story of how
that changed is the argument for not leaving one there.

`lowerbound-at-least` weakens `LowerBound`'s `length F = m` to
`length F ≥ m`. It used to break the build in four places, all of them
`apply H` steps whose goal had changed shape, and it was declared
`killed-script` with those four steps as repairs. The mathematics was
never involved: the two forms define the same predicate, and
`Audit.LowerBound_ge_equiv` proves it — from a sunflower-free family
of size at least `m`, its first `m` members are a sunflower-free family
of size exactly `m`. That theorem was written *because* the mutation
asked the question.

The four repairs were an artefact of how those proofs were written, and
artefacts of that kind do not stay put. Adding
`CliqueLowerBound.two_cliques_lower_bound` — a theorem about cliques,
with no bearing on whether `LowerBound`'s equality matters — introduced
a fifth brittle step, turned the outcome into `killed`, and failed the
build. The five steps are now written as `rewrite …; lia`, which proves
the goal in either form, and the mutation is declared `survived`: what
it reports is now a property of the definition rather than of the
tactic scripts.

`repairs` remains part of the manifest format, because the wrinkle it
addresses is real. The lesson is that a script-level kill is a debt,
not a resting place — the next unrelated theorem pays interest on it.

### Current results

42 mutations, all with the outcome the manifest declares: 40 killed
outright, one genuine survivor (`lowerbound-at-least`, for the reason
above), and one control surviving as it must. The mutations that
matter most:

| Mutation | Asks | Dies in |
|---|---|---|
| `spread-drop-nodup` | Does re-injecting the historical degeneracy still break the build? | `Spread.v` |
| `cands-members-only` | Would a too-small candidate enumeration be noticed? | `Spread.v` |
| `raospread-flat-exponent` | Is the `r^(m-\|T\|)` exponent load-bearing, or would a flat `r^m` do? | `Spread.v` |
| `raospread-off-by-one` | Does loosening the degree cap by one break anything? | `Spread.v` |
| `distinct-is-nodup` | Is set-distinctness needed, or would literal distinctness do? | `ErdosRado.v` |
| `syd-nonstrict-size` | Is the size hypothesis `r^m < \|F\|` strict where it is used? | `SpreadReduction.v` |
| `reduction-off-by-one` | Is the `+1` in `f(m,k) ≤ r^m + 1` load-bearing? | `SpreadReduction.v` |
| `axiom-exponent` | Is the exponent in the derived modern bound checked by the reduction? | `ALWZ.v` |
| `rao-two-nodup-not-distinct` | Is `Distinct` what collapses the spread condition to a degree bound at uniformity 2, or would `NoDup` do? | `TwoUniform.v` |
| `star-sunflower-uniformity-3` | Is uniformity 2 load-bearing, or are sunflowers about degrees at every uniformity? | `TwoUniform.v` |
| `clique-matching-slack` | Weakens a *true* lemma by one. Does the parity argument need the matching bound to be tight? | `CliqueLowerBound.v` |

Run it with:

```bash
make mutants                      # all of them, 4 parallel builds
tools/mutate.py --only spread-drop-nodup
tools/mutate.py --json out.json   # machine-readable results
```

Each mutant is a full rebuild in a sandbox copy; the working tree is
never touched. A full pass takes about a minute.

---

---

## 5. Statement baselines — `tools/statements.py`

Everything above asks whether a definition *means* something. This asks
the blunter question underneath it: is the statement still the one that
was reviewed?

Nothing else here can tell. A theorem whose hypothesis quietly weakened
compiles, reports `Closed under the global context`, passes `coqchk`,
and — if the weakening is one no other theorem exercises — survives
mutation testing too, because mutation testing perturbs the *current*
source and asks what breaks. It has no memory of what the source used
to say. That is the gap: both historical errors were introduced by
writing a statement, not by breaking one, and a check that only ever
looks at HEAD cannot see the difference.

So `tools/audited.txt` names what is audited, and
`tools/statements.txt` records what each name currently says:

```
1f71b1599cd9eb36  def ALWZ.Rao20_lemma2
    *** [ Rao20_lemma2 : exists alpha : nat, 1 <= alpha /\ (forall n k r : nat,
    1 <= n -> 2 <= k -> alpha * k * PeanoNat.Nat.log2_up (S (k * n)) <= r ->
    SpreadYieldsDisjoint n k r) ]
```

`make statements` regenerates and diffs; CI gates on it. A statement
that moves without the baseline moving in the same commit fails the
build, so changing what the development claims becomes a deliberate act
with a reviewable one-line diff — separated from the several hundred
lines of tactic churn it would otherwise hide in. That separation is
the point. Both historical errors would have been visible at review
time as a changed line in this file rather than found by rereading the
source months later.

Two kinds of entry, because for a definition the body *is* the
statement:

| | printed with | records |
|---|---|---|
| `thm NAME` | `Check` | the type, not the proof term — so refactoring a proof moves nothing |
| `def NAME` | `Print` | the body, so a weakened `RaoSpread` shows up here even though every theorem naming it still compiles unchanged |

The `def` entries are chosen for that second column: the axiom first,
then the spread layer where both errors lived, then the core
definitions every bound is stated against, then the conjecture itself
so that "what is open" cannot drift either.

The tool also checks that every `Theorem`, `Corollary` and `Example` in
`coq/Audit.v` is on the list. That file exists to be audited, so a
statement there that no target names is a check nobody runs — and the
guard is not hypothetical, it was written after an entry was silently
dropped from the list while it was being moved out of the `Makefile`.

**What it does not catch.** A change to a definition no entry names.
And a change that is genuinely equivalent but printed differently: the
Coq printer is the oracle, so a notation change moves hashes even when
nothing else did. It is a tripwire, not a semantics — the complement of
mutation testing, which asks whether a hypothesis is load-bearing where
this asks only whether it is still there.

## 6. The numbers in the prose — `tools/docnumbers.py`

One level up from statement baselines. `tools/statements.txt` stops a
theorem's *statement* from drifting; this stops the *description of the
development* from drifting away from the development.

Every count in `README.md` and `STATUS.md` — how many Coq files, how
many audited theorems, how many mutations and how many of them are
killed — is a hand-copied consequence of a list elsewhere in the
repository. When this check was written, three of them were already
wrong: the README said 19 Coq files against 22, and `STATUS.md` said 21
modules in two places. Each was true when it was written.

So `tools/docnumbers.py` derives each count from the list that defines
it (`_CoqProject`, `tools/audited.txt`, `tools/mutations.toml`) and
checks it against a manifest of where that count is quoted. A pattern
that matches *nothing* is also a failure, so deleting the sentence is
not a way to pass. `make docnumbers` runs it; CI gates on it.

Its own limits, stated because they are the same kind of gap: it sees
digits, not words, so "the seven mechanisms added" above is unchecked;
and a count that no entry names is unchecked by construction, which the
run reports rather than passes over.

This is the same fix, one level down, that the workflow already got: the
audited-theorem count used to be hardcoded in the CI file and is now
reported by `make print-assumptions` from its own list.

## What this does not cover

Worth being explicit, since the point of the exercise is honesty about
what is checked:

* **The axiom itself is still an axiom.** The testbed shows its shape
  is true at small parameters and its hypotheses are satisfiable at the
  published threshold. It does not show the lemma is true, and cannot.
  Discharging it means formalising Rao's encoding argument.
* **The search is bounded.** Ground sets up to size 8 (9 in one
  check), uniformity up to 3. A counterexample first appearing at larger parameters would be
  missed.
* **Mutations are hand-written.** The manifest covers the definitions
  the two historical errors touched, and the arithmetic in the
  reduction. It is not generated, and it is not exhaustive over the
  space of possible perturbations.
* **Coherence theorems test consistency, not truth.** They would catch
  two definitions that contradict each other. They would not catch two
  definitions that are consistently wrong in the same direction — for
  that there is no substitute for the source.

## Reproducing

```bash
make verify     # build + Print Assumptions audit + statement baselines
make coqchk     # independent re-check of every module, whole-library census
make mutants    # perturb each definition, check what breaks
make testbed    # exhaustive falsification + differential checks
make statements # every audited statement against tools/statements.txt
make docnumbers # every number the prose quotes against the lists it counts
cd rust && cargo test --release   # everything on the Rust side
```

CI runs these as separate jobs on every push, with `RUSTFLAGS=-D
warnings` on the Rust side.

## Known gaps in the checking itself

* **One Coq version.** Only 8.18, the version `apt` ships on
  Ubuntu 24.04. The portability claim is untested against 8.19+; a
  matrix would need opam and roughly an order of magnitude more CI
  time.
* **No `clippy`.** The Rust side denies warnings but does not lint.
* **The audit list is complete only for `coq/Audit.v`.** That file is
  checked exhaustively; everywhere else `tools/audited.txt` is curated
  by hand, so a theorem added elsewhere can still go unaudited. Driving
  the list from source annotations is the fix, and is on the roadmap.

### A fifth: checking a reconstruction against the literature

`rust/tests/intersecting.rs` tests something unusual — not a statement
about to be proved, but a *reading* of a paper nobody here has read.

The Abbott–Hanson–Sauer rate of `3.162...` was reverse-engineered into a
substitution recursion whose fixed point is `iota(b)^(1/(b-1))`, with
`iota(b)` the largest *intersecting* sunflower-free `b`-uniform family.
A reconstruction like that is a guess, and the way to treat a guess is
to look for the ways it could be wrong:

* it predicts `iota(2) = 3` with the doubling equal to `two_triangles`,
  the family behind the proved value `f(2,3) = 7`. Measured: 3, and the
  doubling is `two_triangles` relabelled (`Audit.doubling_at_b_2_is_two_triangles`);
* it predicts a rate of `iota(3)^(1/2)`, so the published `3.162` means
  `iota(3) = 10`. Measured exhaustively: 10, first attained on six
  points and stable to twelve;
* it predicts the substitution is sunflower-free *only* because the
  inner family is intersecting. Both halves are checked: the
  construction is sunflower-free at two instances (`g(4) >= 54`,
  `g(6) >= 600`) and stops being so the moment one member of the inner
  family is swapped for a disjoint one.

Three independent predictions, three hits, and the failure mode is
exercised rather than assumed. That is what the confidence rests on —
not on the reconstruction being obvious, which it is not.

The doubling half is then proved in Coq (`Intersecting.doubling_lower_bound`)
and its hypothesis pinned by a counterexample
(`Audit.intersecting_is_needed_in_the_doubling`). **The substitution half
is not proved**, and the difference is a factor in the rate: `20^(1/3)`
proved against `10^(1/2)` verified. `docs/roadmap.md` §5 says so.

### A fourth: measuring where a question starts

`rust/tests/ground_set.rs` is a different use of the same machinery. It
does not falsify a statement about to be proved; it measures a quantity
nobody here knew — `N(m,g)`, the largest `m`-uniform 3-sunflower-free
family on `g` points — because `coq/SliceRank.v` shows that where that
sequence plateaus is the one fact standing between the Naslund–Sawin
bound and the sunflower conjecture at `k = 3`.

Three guards, because a search is easier to believe than to check:

* **against what is already proved.** `N(1,g)` must stabilise at 2 and
  `N(2,g)` at 6, which are `f(1,3) = 3` and `f(2,3) = 7` — both exact
  values with machine-checked proofs. A search disagreeing with
  `F23.f_2_3_eq_7` would be broken, and this is the cheapest way to
  find that out;
* **against full enumeration.** At parameters small enough to enumerate
  every subfamily, branch-and-bound must return the same maximum. The
  pruning is where a max-search goes wrong, and the bound it uses is
  the weak one, so this is not a formality;
* **against itself.** `N(m,g)` is non-decreasing in `g` — a family on
  `g` points is a family on `g+1`. A violation would mean the search
  pruned something it should not have.

The measurement then fed back into the Coq. `N(3,9) = 14` is the
exhaustive maximum at nine points, and its witness transcribes to
`SliceRank.lower_bound_3_3_14`: `f(3,3) >= 15`, where the direct sum
reaches 13. The Coq side re-derives sunflower-freeness from the family
with the reflective detector, so nothing is taken on the search's word —
what the search supplied is a candidate, not a proof.

It also corrected a claim written here one session earlier. The
Abbott–Hanson–Sauer construction is reported to be seeded by a 3-uniform
family of size 10; that had been written up as contradicting the direct
sum's 12 at the same uniformity. `N(3,6) = 10` exactly — the seed is a
maximum on *six* points and the direct sum's 12 lives on eight. Two
different quantities, no contradiction, and the note said otherwise
until something computed both.
