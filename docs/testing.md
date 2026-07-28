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
the source. This document describes the four mechanisms added so that
a third one does not have to be.

None of them is a substitute for reading the paper. All of them are
cheaper than reading it again.

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
       6  1   3              2                   3   1
       8  1   4              3                   4   1,2
       5  2   3              3                   5   1,2
       8  2   3              3                   5   1,2
       7  3   3              3                   7   1,2
```

`r*` is the least `r` above which no counterexample exists; the next
column is `m(k-1)+1`, proved sufficient in Coq. `r*` must never exceed
it, and at `m = 1` it is exactly `k-1`, matching
`Audit.spread_yields_disjoint_needs_r` on the nose.

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

Exactly one mutation in the current manifest lands there.
`lowerbound-at-least` weakens `LowerBound`'s `length F = m` to
`length F ≥ m` and the build breaks in four places, all of them
`apply H` steps whose goal changed shape. Replacing them with
`rewrite H; lia` restores it. The mathematics was never involved: the
two forms of `LowerBound` define the same predicate, and
`Audit.LowerBound_ge_equiv` proves it — from a sunflower-free family
of size at least `m`, its first `m` members are a sunflower-free family
of size exactly `m`.

That theorem was written *because* the mutation asked the question.
Which is the methodology working: a perturbation, an unexpected
result, and a new theorem making the answer precise.

### Current results

23 mutations, all with the outcome the manifest declares: 22 killed
outright, one killed at script level only, none surviving. The
mutations that matter most:

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

Run it with:

```bash
make mutants                      # all of them, 4 parallel builds
tools/mutate.py --only spread-drop-nodup
tools/mutate.py --json out.json   # machine-readable results
```

Each mutant is a full rebuild in a sandbox copy; the working tree is
never touched. A full pass takes about a minute.

---

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
make verify     # build + Print Assumptions audit (49 closed theorems)
make mutants    # perturb each definition, check what breaks
make testbed    # exhaustive falsification + differential checks
cd rust && cargo test --release   # everything on the Rust side
```

CI runs all three as separate jobs on every push.
