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

### A fourth: the sandwich, falsified step by step

`rust/tests/iota_sandwich.rs` does the same job for
`Intersecting.sunflower_free_star_bound` — `g(b) <= 2b iota(b)` — and it
is the first suite here written to falsify a proof's *steps* rather than
only its conclusion. The argument has four places it could be wrong, and
each is a separate test:

1. a maximal disjoint subfamily of a sunflower-free family has at most
   two members;
2. its union has at most `2b` points and meets every member;
3. some point lies in at least `|F|/(2b)` members — the conclusion,
   checked over *every* point rather than through the cover, so a broken
   cover argument cannot make it pass;
4. the star at a point is `b`-uniform, intersecting and sunflower-free.

Splitting it that way is what makes a failure diagnostic instead of just
red. It also means step 3 is an independent check on steps 1 and 2
rather than a restatement of them.

The sample is the point. Exhaustive maxima are few and highly
structured — `N(3,9)` is one family — so most of it is randomly grown
*maximal* sunflower-free families, forty per `(ground, uniformity)` from
a fixed seed. Nothing was found: the statement survived, and the Coq
proof went in first time.

Two things it records that the theorem does not. The worst observed
ratio `|F| / maxdeg(F)` is pinned per uniformity — 2, 3, 2.75 against
the proved 2, 4, 6 — so how loose the bound is stays visible and a
change in the sample is a failing assertion rather than a silent drift.
And the arithmetic the equivalence turns on, `2b C^b <= (2C)^b`, is
checked numerically before it is proved in Coq; without it the sandwich
says nothing about exponential rates.

Cost, recorded because it shaped the suite: `N(3,9)` takes a quarter of
an hour and `N(3,8)` takes eighteen seconds, so the exhaustive maxima
stop at ground 8 for uniformity 3 and every one is computed once and
cached. The first version of the file recomputed them inside a loop and
did not finish.

### A fifth: a measurement that chose between two hypotheses

`rust/tests/iota_ground.rs` is not falsification. It is the case where
the search decided *which theorem to prove*, and it is worth separating
from the rest for that reason.

`coq/SliceRank.v` had carried `GroundBounded` — "an extremal
sunflower-free `m`-uniform family lives on `O(m)` points" — as the one
hypothesis that would turn the polynomial method into the conjecture at
`k = 3`, together with an honest note that the measurements do not
support it: the `m = 3` row of `N(m,g)` is still climbing at `g = 3m`.
The same question asked of *intersecting* families answers differently:

```
  g                3  4  5  6   7   8   9  10  11  12  13  14
  N(3,g) general:  1  4  6 10  12  12  14   ?   ?   ?   ?   ?
  iota(3,g):       1  4  6 10  10  10  10  10  10  10  10  10
```

Equal at six points, apart from seven on. Every entry exhaustive; the
intersecting row is *instant* even at fourteen points, where the general
one stops finishing at ten. That contrast is the whole reason
`coq/IotaGround.v` exists, and it was a measurement before it was a
theorem.

The suite also does something the falsification suites do not: it checks
a *consequence of tightness*. `IotaGround.link_degree_ground_bound`
gives `b|F| <= g N(b-1,g-1)`, and where that holds with equality the
family must be regular — degrees sum to the maximum and each is capped
at it. So the test computes the degree sequence and asserts regularity
**only at the rows where it independently found equality**, and pins the
set of tight rows. A bound that had quietly become loose, or a witness
that had stopped being extremal, breaks it in a way a size assertion
would not.

One prediction was made from the arithmetic and confirmed by the search
rather than the other way round: `iota(4,9) = 27` is exactly
`9 * N(3,8) / 4 = 9 * 12 / 4`, so the extremal family had to be
12-regular. It is.

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
development's first genuine survivor, which weakens `LowerBound`'s
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

### A sixth: the structure of the extremal families

`rust/tests/iota_structure.rs` is the falsification suite for
`coq/Product.v`, and it does three jobs the earlier suites do not.

**It falsifies the cone before the cone was proved.** Every
3-sunflower-free family over six `(ground, uniformity)` pairs — 35548 of
them, a count that is *pinned*, since the failure mode of an exhaustive
test is that it quietly stops being exhaustive — is coned and handed to
`intersecting::verify`, which shares no code with the construction:
uniformity, distinctness, intersecting-ness and sunflower-freeness are all
re-derived. `link [p] (cone p F) = F` is checked as *literal* equality over
the same enumeration, which is what `Product.link_of_cone` claims.

**It kills closed forms, as assertions.** `docs/roadmap.md` §5 tabulates
the measured `iota` values; eight guesses at a formula for them are
evaluated and each failure is asserted, so a future session cannot
re-propose one the data already refutes. `C(2b-1,b-1)` dies at `b = 4`,
`3^(b-1)` at `b = 3`, the rest at `b = 2`. The trap is asserted too: all
`b`-subsets of `[2b-1]` is intersecting and matches the
complementary-pair ceiling, and *contains a sunflower* from `b = 3` on.

**It pins the structure, and one of the pins is a differential test.** The
automorphism group orders come from a backtracking search whose prune is
complete — assign point images one at a time and check `deg(S) = deg(pi(S))`
for every subset `S` of the assigned points, which for a distinct uniform
family *is* `pi(F) = F`, so a surviving permutation needs no final check.
All nine orders were checked against `nauty` (`dreadnaut` input is emitted
by `examples/iota_structure --nauty`) and agree. That is what the two
identifications rest on: `iota(3) = 10` is the unique simple 2-(6,3,2)
design with `|Aut| = 60`, and `iota(4,9) = 27` is the Abbott–Hanson–Sauer
substitution with `|Aut| = 1296 = 6 * 6^3` — the exact order that
construction's symmetry predicts and nothing else would have.

One bug the 128-bit path was written to fix, recorded because it is the
same class as the truncation above: the tree-path table on `u32` masks
reported "32 members on a 32-point support" from `b = 6`, against the 63
points the construction actually uses. A silent overflow that reads as
data. `structure::verify_128` and `tree_paths_128` are the repair, and the
test asserts the support size rather than only the member count.

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

**It has now been killed by accident five times**, and the fourth and
fifth were *different* mechanisms, so the standing rule needs all three
halves stated.

* **Consuming a `LowerBound`.** Do not discharge a size obligation by
  `reflexivity`, `apply`, or `rewrite` on the length equation. Finish
  with `pose proof …; lia`, which proves the goal from `=` or from `≥`.
* **Producing a family of a given size.** `Compression.compression_would_give_ground_bounded`
  takes a `LowerBound m 3 j` apart and has to hand `GroundBounded` a
  family of length *exactly* `j`. Passing the family straight through
  works only if `LowerBound` pinned the size — so the proof was sensitive
  to the equality, through no fault of its own, and killed the survivor.
  The fix is the content of `Audit.LowerBound_ge_equiv` written out at
  the point of use: take `firstn j` of the family, which is uniform,
  distinct, grounded and sunflower-free because all four pass to
  subfamilies. **A proof that needs a family of an exact size must trim
  one, not assume one.**
* **Producing a `LowerBound` from a family already in hand.**
  `Product.ground_bounded_implies_iota_ground_bounded` builds
  `LowerBound b 3 (length H)` out of an intersecting witness and closed the
  size clause with `assumption`, which finds `length H = length H` and not
  `length H >= length H`. The fix is `lia`, which proves either. So the rule
  covers *producing* a `LowerBound`, not only consuming one.

**It happened a third time**, which is the reason this section is worth
its length. `IotaRate.every_construction_is_within_2b_of_iota` and
`Audit.bounds_coherent_star_bound` both destructure a `LowerBound` and
then `rewrite <- Hlen` to turn `length F` into `m` — again a step that
works against `=` and not against `>=`, again in theorems with no
bearing on the question the mutation asks, and again a red build. Both
now `pose proof` the bound and finish with `lia`. Interest is still
being paid on a debt cleared two sessions ago; the standing rule is that
*no* proof may discharge a `LowerBound` size obligation by `reflexivity`,
`apply`, or `rewrite` on the length equation.

`repairs` remains part of the manifest format, because the wrinkle it
addresses is real. The lesson is that a script-level kill is a debt,
not a resting place — the next unrelated theorem pays interest on it.

**And it happened a fifth time, in a new predicate, which is the argument
for writing the mutation at the same time as the definition.**
`Product.IotaAtLeast` is `LowerBound` with an intersecting clause, so
`iotaatleast-at-least` asks it the same question. (The fifth accidental
kill of `lowerbound-at-least` itself came from the same file, and is the
third bullet above.) Declared `survived` — the
two forms define the same predicate, and `Product.IotaAtLeast_antitone`
proves it — the runner reported `killed` **twice**, and both kills were
brittle proofs rather than mathematics:

* `iota_one_at_least_one` and two witness lemmas discharged
  `length H = N` by `reflexivity` or `vm_compute; reflexivity`;
* `iota_at_least_g_pred` finished with `exact HlenG`, and
  `iota_at_least_doubles` with `rewrite Hlen`;
* `iota_ground_bounded_bounds_the_general_row` had to hand out a family of
  size *exactly* `j` and passed one through — the second half of the
  standing rule, and the fix is the one it names: trim with `firstn`, do
  not assume.

All five now finish with `lia`, `nia` or antitonicity, and the mutation
survives. Writing it in the same commit as the definition is what caught
them; the four earlier accidental kills were all found weeks later by
unrelated theorems.

### Current results

167 mutations, all with the outcome the manifest declares: 164 killed
outright, two genuine survivors (`lowerbound-at-least`, for the reason
above, and `iotaatleast-at-least`, which asks the same question of
`Product.IotaAtLeast` — see below), and one control surviving as it must. The mutations that
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
| `cone-does-not-add-the-apex` | Is the added point what forces intersecting-ness, or does something else? | `Product.v` |
| `cone-freshness-not-required` | Does `cone_Uniform` actually need `Fresh`, or does the uniformity come from elsewhere? | `Product.v` |
| `iotaatleast-drop-intersecting` | Is the intersecting clause in `IotaAtLeast` load-bearing, or decoration? | `Product.v` |
| `stepbounded-additive` | Is `iota(b+1) <= D * iota(b)` load-bearing, or would an additive step do? | `Product.v` |
| `spreadthreshold-piece-drop-r-bound` | Is `m - 1 <= r` what makes the meets-A-twice branch fit under the stated bound on an intersecting piece? | `SpreadThreshold.v` |
| `spreadthreshold-quadratic-drop-slack` | Is the `+2` in `2r + 3n² + 2 <= r² + 4n` real arithmetic or slack? | `SpreadThreshold.v` |
| `spreadthreshold-cover-off-by-one` | Is `2n` the sharp value of the cover argument for `r*(n,3)`, or is there another one in it? | `SpreadThreshold.v` |
| `greedyclosed-drop-the-level-factor` | Is the `m!` in Erdős–Rado exactly the factor `m` the greedy cover pays once per level? | `Profile.v` |
| `er-profile-drop-the-factorial` | Is Erdős–Rado's profile greedy-closed because of the factorial, or would the bare power do? | `Profile.v` |
| `profile-witness-forgets-the-level` | Is the level-indexing `B (m - \|T\|)` what makes the recursion profile-preserving? | `Profile.v` |
| `greedy-matching-off-by-one` | Does the development notice if "at most `k-1` disjoint members" is stated as `k`? | `Profile.v` |

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

## 7. What each route can possibly reach — `tools/ceiling.py`

The checks above all ask whether something is true. This asks whether
something is *worth doing*, and it is the only gate here that can fail a
build over a plan rather than over a proof.

Rule 14 of `docs/reading.md` says a route's ceiling is computed in the
first hour, not the sixth session; rule 20 says it is costed against the
record rather than against the last bound the development can name, and
that the comparison is one of *shape* — constant, logarithmic, linear.
Both were prose, and prose does not fail a build. So each route now
declares, in `tools/ceiling.py`, the best `f(n,3)` it could produce if
every open step in it went perfectly, expressed as the base `b` in
`bⁿ` — and the tool evaluates that declaration in exact integer
arithmetic against Erdős–Rado 1960, against the record, and against the
conjecture, at several `n`.

The verdict is classified by the measured exponent `g` in
`b(n) ≈ n^g`: `1` is linear, `0` is a constant threshold. A route that
improves the constant and keeps the exponent has not moved the problem,
and the classification says so rather than reporting a smaller number.
A route whose declared verdict disagrees with its own arithmetic fails
the build. `make ceilings` runs it, `make verify` includes it, and CI
gates on it.

What it made checkable that was previously a judgement call: of the 9
routes this development has built or considered, **6 lose to 1960 in
their own best case**, one equals it, and the remaining two reach the
record shape or better. That ratio was not knowable from any single
session's notes, and it is now a line the tool prints — `9 routes
costed; 2 can reach the record or better` — rather than an impression.
(Both counts in that sentence are themselves gated, by §6's
`tools/docnumbers.py`, against `tools/ceiling.py`'s own route list.)

`--linear` adds the number underneath the classification. A route with
`r*(n,3) ≤ c·n` gives `f(n,3) ≤ (cn)ⁿ + 1`, and Erdős–Rado is
`2ⁿn! + 1 ~ √(2πn)·(2n/e)ⁿ`, so a linear route beats 1960 exactly when
`c < 2/e = 0.7357588823…`. Each of the six losing routes above is of
that form, with `c` in `{2, 2, √3, 1, 1, 1}`. The best of them, `c = 1`,
would have to fall by a factor of `1.36` to reach the threshold. That is
a number, not an opinion, and it is why "linear" is a verdict here
rather than a description.

What it cannot check: whether a declared ceiling is *achievable*. It
takes each route's own best case at face value and computes what that
best case is worth. A route that declares an optimistic ceiling and
fails to reach it passes this gate and fails in the mathematics.

## 8. The pull request itself — `tools/prcheck.py`

One more level up. `tools/statements.txt` stops a theorem's statement
from drifting; `tools/docnumbers.py` stops the prose in the tree from
drifting away from the lists it counts; this stops the *pull request*
from drifting away from the branch it is about.

That is the one document a reviewer forms an opinion from, and until
this was written it was the only one nothing checked. Every failure
mode the repository has already had in prose is available there in a
harder-to-notice form, because a pull request body is written once,
read once, and never regenerated: a count copied from a previous
session, a theorem cited by a name a rebase renamed, a claim of novelty
with no search behind it.

So `.github/pull_request_template.md` carries a required TOML block, and
`tools/prcheck.py` enforces four things against it:

| check | against |
|---|---|
| counts — modules, audited theorems and definitions, mutations, killed mutations, Rust suites, declared axioms | `_CoqProject`, `tools/audited.txt`, `tools/mutations.toml`, `rust/tests/`, and `^Axiom` in `coq/*.v` |
| every claim's `evidence` resolves | an audited Coq name, a Rust `#[test]` function, a mutation id, or a path that exists |
| `novelty = "new-mathematics"` carries a real `search` | rule 17 of `docs/reading.md`, as a gate rather than as an intention |
| `## What did not move` is present and non-empty | the section itself |

`make prcheck` checks the template still parses; `make prcheck
PR_BODY=body.md` checks a real body. CI runs the first on every push —
a template that stops parsing would otherwise fail every later pull
request for a reason having nothing to do with its own branch — and the
second on every pull request, reading the body through the environment
rather than interpolating it into the script, since a pull request body
is text anyone who can open one controls.

It lives in `.github/workflows/prcheck.yml` rather than as a job in
`verify.yml`, for one reason worth recording: a gate on the body has to
re-run when the body is *edited*, and a workflow has a single `on:`.
Adding `edited` to `verify.yml` would rebuild everything — including the
hour-long mutation suite — every time someone fixed a typo in a
description, which is the kind of cost that gets a gate switched off.

It found something the first time it was run, which is the only reason
to believe it does anything: six `Example`s in `coq/Counting.v` were
never added to `tools/audited.txt`, so a claim citing one of them
resolved to nothing. They were unaudited, not wrong — but the audit
list is the thing that says so, and it did not.

**What it cannot check**, stated in the same spirit as the sections
above: whether the prose is true, whether a claim's sentence matches
the theorem it cites, or whether the verdict is honest. A body can
satisfy every mechanical check and still overstate what the branch did.
The sections are ordered to make that awkward — `What did not move`
comes second, before the results — but ordering is a nudge, not a
check, and this document should not pretend otherwise.

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
make ceilings   # every route's best possible bound, against the record
make prcheck    # the pull request template; PR_BODY=body.md for a real one
cd rust && cargo test --release   # everything on the Rust side
cargo run --release --example iota_structure   # the extremal families, dumped
cargo run --release --example iota_extend      # the iota table past the search
```

CI runs these as separate jobs on every push, with `RUSTFLAGS=-D
warnings` on the Rust side, plus once more against the *merge commit*
when a pull request is opened — the one tree no push ever builds, and
the only place a conflict with `main` that is invisible on either side
alone can show up.

Once per push, not twice. A push to a branch with an open pull request
fires both `push` and `pull_request:synchronize`, and the two carry
different `github.ref` because they check out different trees, so no
concurrency key can merge them. On commit `d524766` that duplication
cost 1h28m *and* 1h32m of runner time for the same 150 mutations.
`verify.yml` therefore does not subscribe to `synchronize`.

**The saving is one job instead of two — half the runner minutes, and
the check-run count went 12 to 6. That is the whole of it, and the
explanation that used to be attached here was wrong.** This paragraph
said the two jobs were slow because they contended with each other. The
very next measurement refutes that: on `b0f9d25` the mutation job ran
*solo* and took **1h36m04s**, slower than either contended run and
slower than the 1h20m "reference", which was itself a contended run on
`2decd53`. The job varies by about a quarter of an hour on GitHub
runners for reasons none of these measurements isolate. The duplication
was real and removing it saved real money; the causal story about
*why the numbers looked the way they did* was a comparison against a
baseline carrying the same defect it was being used to measure. See
`docs/reading.md` rule 28. `prcheck.yml` does, and must: pushing a commit changes
the counts the pull request body asserts, so the gate has to re-read
the body against the new tree, and eight seconds of a runner is not the
same kind of cost.

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

### A seventh: a target with a number in it

`rust/tests/sharp_conjecture.rs` is not falsification of a statement
about to be proved. It is the *target* `coq/Sharp.v` names — the sharp
conjecture `iota(b)^2 <= 10^(b-1)`, i.e. that Abbott–Hanson–Sauer is
optimal — kept in a form a future session can check against in one line.

Three jobs, and the third is the one that earns it a place here.

* **The thresholds are tabulated and pinned.** `threshold(b)` is the
  least family size at uniformity `b` that refutes; the values at
  `b = 4..9` are written out by hand *and* computed, because a threshold
  table that silently drifted is exactly the failure mode a future
  session would not notice. The integer square root is by bisection with
  an upper limit that has to clear `10^(b-1)` at the largest `b` any
  caller uses — the first version returned a plausible wrong answer at
  `b = 27` rather than failing.
* **Every construction is rebuilt, not quoted.** The rows of the `iota`
  table are reconstructed from their seeds and re-verified by
  `structure::verify_128` before being measured against the threshold.
* **None of them refutes, and that is asserted.** It is forced — the
  substitution's own fixed point is `10^(1/2)` — so the assertion is
  there to stop a bigger number being mistaken for a better rate. The
  `b = 8` row of `docs/roadmap.md` §11.6 is *not* rebuilt, and its
  absence from the rebuilt list is asserted too, because it is recorded
  there as unverified.

### An eighth: the maximality campaign, checked three ways

`rust/tests/extension.rs` is the falsification suite for
`coq/Maximal.v`, and it exists because the campaign's answer is a
negative — "nothing can be added" — which is the kind of answer that is
easiest to get wrong by asking the wrong question.

* **The reduction is checked, not assumed.** The whole method rests on a
  candidate interacting with the family only through its trace on the
  support. So for every trace of the small rows — 327 of them, a count
  that is pinned — the trace verdict is checked against *actually
  building* the extended family and handing it to
  `structure::verify_128`. If the reduction were wrong the two would
  disagree.
* **The verdict is taken twice.** A minimal-hitting-set enumeration and
  a brute-force trace walk must agree; the third method, SAT with two
  solvers required to agree on UNSAT, lives in
  `examples/extend_ahs.rs` because it shells out. At `b = 9`, where
  10,000 members are built and 10,001 would beat 1972, the brute force
  is `1.4e8` traces and is not run — so that row is the hitting-set
  method cross-checked against SAT, and the test says so.
* **The mechanism is pinned, not just the answer.** `tau` of each
  substitution family equals its uniformity *and* equals the product of
  the factors' covering numbers. That multiplicativity is why the answer
  is no, so a construction that changed would show up here rather than as
  a different verdict.
* **And the counter-reading is pinned too.** Maximal is not maximum: the
  Fano plane is maximal intersecting with seven members against
  `iota(3) = 10`, and a six-member maximal intersecting *sunflower-free*
  family exists. Both were found here and checked here before being
  transcribed into Coq.

One entry runs in the other order and says so in the file:
`Maximal.regular_intersecting_ground_bound` was proved before it was
enumerated — it is three lines from `Pigeonhole.pigeonhole_family` and
was written as the explanation of a measurement rather than as a
conjecture. The enumeration was added afterwards and found no
counterexample, which is weaker evidence than the usual order gives.

### A ninth: a measurement that was already there, and was being read wrong

`rust/tests/star_defect.rs` is the falsification suite for
`coq/StarDefect.v`, and it is the one entry here that exists because an
*existing* check was being over-read.

`rust/tests/iota_sandwich.rs` has pinned the worst observed
`|F| / maxdeg(F)` per uniformity since the sandwich went in — 2, 3, 2.75
against the proved 2, 4, 6 — as evidence of how loose the `2b` factor is.
Read one way that row is a curiosity. Read another it is the whole
conjecture: a *constant* bound on that ratio gives `g(b) <= c g(b-1)` and
hence `c^b`. Nobody had asked whether it stays flat.

It does not, and the suite is built to make the refutation checkable
rather than plausible:

* **The chain identity is checked, not assumed.** `|F|` is the product of
  the ratios down the greedy chain — checked as a *telescope* (each
  level's maximum degree is the next level's size) rather than as a
  running product, because the individual ratios are not integers and an
  integer product silently truncates. The first version of the example
  did truncate, and printed `24` where the family has 27 members.
* **Multiplicativity is checked in exact rational arithmetic.**
  `rho(G) rho(H) = rho(substitute(G,H))` is asserted as
  `gn * hn * fden == fnum * gd * hd`, never as a float comparison, on all
  six buildable pairs.
* **The tower is built, not extrapolated.** `rho = 4` at `b = 9` is
  measured on the actual 10,000-member family, which is re-verified by
  `structure::verify_128` first. The `b = 27` row has `10^13` members and
  is arithmetic only; the test asserts that it is out of reach rather
  than quietly skipping it.
* **The proved ceilings are checked on everything.** `rho <= 2b` for
  sunflower-free and `rho <= b` for intersecting families, on nine
  constructions. A violation would be a counterexample to
  `Intersecting.sunflower_free_star_bound` or to
  `Intersecting.intersecting_link_bound`, so this is a differential test
  against the Coq side rather than a sanity check.
* **The two numbers the Coq rests on are rebuilt.**
  `StarDefect.star_bounded_needs_c_at_least_five` uses exactly `54` and
  `12`; both are recomputed here from the seed.

The suite ran before any of `coq/StarDefect.v` was written, which is the
order the rest of this document asks for and the order the previous
entry did not manage.

### A tenth: a symmetry-breaking encoding, and why every restriction in
###           it needs its own falsifier

`rust/tests/symbreak.rs` guards `rust/src/symbreak.rs`, and it is the
suite whose subject can be wrong in the one direction nothing else here
catches.

Everything else in this file falsifies a *statement*: a bound that is
too strong, a hypothesis that is not load-bearing, a count that has
drifted. A symmetry-breaking encoding is different. It is a claim that
a family may be *assumed* to look a certain way, and if that claim is
wrong the solver returns **UNSAT** — the verdict no witness can
contradict, on an instance that was never searched. A wrong restriction
does not produce a wrong object anyone can inspect; it produces a
correct-looking negative.

Four restrictions and one split, each with its own failure mode:

* **The order counters.** A degree comparison is encoded as an
  implication between "at least `k`" literals, and a sequential counter
  usually encodes only one direction — enough to *assert* a threshold,
  useless to *compare*. With the wrong direction every comparison is a
  no-op: the run is sound and slow, and reports nothing. So both
  directions are checked against a brute-force count, for every `k` and
  every prefix length, by asking the solver for the two configurations
  that must be impossible.
* **The restrictions themselves** — maximum degree at point 0, sorted
  blocks, exactly `t` members, the intersecting degree floor, the
  lexicographic tie-break. Every one is run on and off at every
  parameter small enough to decide twice, and the verdicts are required
  to match. This is the control §9 of `docs/roadmap.md` asked for on the
  degree cap and did not get.
* **The cube splits.** Two of them: on `deg(0)`, and on the exact degree
  *sequence*. A split is a cover or it is nothing, and a missing cube
  also reads as UNSAT. The `deg(0)` cubes are checked to abut and to
  start at the floor the encoding asserts, without the solver. The
  degree-sequence cubes are checked against a brute-force sweep over
  every vector in range, by code sharing nothing with the recursion that
  generates them.
* **The ladder.** Asking the question one support size at a time is only
  a cover because a family on at most `g` points has a support of some
  size `s <= g` and relabels onto `[s]`. The rungs below the frontier are
  re-decided against `intersecting::iota`, the exhaustive
  branch-and-bound, which shares no code with the encoder, the solver or
  the driver.

What none of it checks is the *solver*. An UNSAT here is cadical's word,
and the repository's standing rule for that verdict — `sat::solve_agreed`,
two independent solvers required to agree — is affordable per instance
and was not run across the whole ladder. `docs/roadmap.md` §33.5 says so
where the result is reported.

### An eleventh: a proof whose case split is the thing that can be wrong

`rust/tests/support.rs` guards `coq/Support.v`, and the interesting part
of it is not the theorem.

The theorem — support `≤ (4b−3) + (b−2)n` — is a bound, and a bound is
easy to falsify: enumerate families, compute supports, compare. That is
done, exhaustively, on 127 466 families. It would also have passed if the
proof were wrong, because the bound is not tight and a weaker argument
would still have produced a true inequality on every small case.

What the proof actually turns on is a *construction*: a core of at most
`4b−3` points that **every member meets twice**. That is the step a
falsifier has to attack, so the test rebuilds the core from the family
alone — no shared code with the Coq development — and asserts the
property directly. Three things it pins that the bound alone would not:

* **The link cover never exceeds two members.** The proof needs it,
  because three pairwise disjoint members of a link lift to a sunflower
  with empty core. If it could be three the core would be too wide and
  the bound would be false at some `n` beyond the sweep.
* **The core width `4b−3` is attained.** At `b = 2` it is exactly five.
  A constant that is never reached is a constant nobody has checked, and
  the next session would not know whether it could be lowered.
* **Both branches of the case split are exercised, with their counts.**
  The proof splits on whether some member meets the anchor in exactly one
  point; only one branch builds a link cover at all. 7 293 families take
  the first branch and 120 168 take the second, and both numbers are
  asserted. A sweep that happened to hit only one branch would leave half
  the proof unfalsified while reporting a clean pass — and that is
  exactly the failure mode a case analysis has.

The sweep stops where it stops for a measured reason, and the reason is
in the file: `(7,4)` has 35 333 735 families and `(8,4)` has more than
forty million. Beyond that the families are **sampled**, deterministically,
and the assertions say sampling rather than exhaustion. Fourteen thousand
samples at four larger parameters is not a proof of anything and is not
written as though it were.


### A twelfth, and it is a gap rather than a check: an external binary

`rust/tests/spread_threshold.rs` shells out to a SAT solver in
`the_witnesses_are_reachable_by_search` and `sat_and_dfs_agree`. With
`cadical` absent from `PATH` both panic on
`Os { code: 2, kind: NotFound }` — not skipped, not reported as an
unmet dependency, just *failed*, in the same shape a broken proof
fails in.

That happened for real: session N+12's container was rebuilt mid-run and
the solver went with it, and the first reading of the failure had to be
"is this a regression?" before it could be "is this the environment?".
Nothing in the suite distinguishes the two, and the cost is a wrong
first hypothesis at exactly the moment a gate result is being reported.

The honest statement of the gap: **two of the 370 tests are not
hermetic.** `make -j4 verify`, `make coqchk` and `python3 tools/mutate.py`
need nothing but Coq; `cargo test --release` needs `cadical` on `PATH`,
and `docs/roadmap.md`'s reproduction block says so. A future session
that wants the suite to be self-describing should make those two skip
with a named reason when the binary is missing, so that a failure in
that file always means what it appears to mean.

`rust/tests/cube_budget.rs` (§49) is the first suite written that way. It
needs `cadical` for one test and guards it:

```rust
    if !have_solver() {
        eprintln!("cadical not installed; skipping");
        return;
    }
```

so a missing solver reads as a skip and a failure in that file always
means the mathematics. `spread_threshold.rs` still does not, and the gap
above stands until it does — one suite adopting the convention is not the
convention being adopted.

### A thirteenth: a sampled census is not a census, and the test has to
### say which one it is

`rust/tests/palvolgyi.rs` asserts that every 27-member intersecting
sunflower-free 4-uniform family a random fill finds on nine points is a
relabelling of `Product.iota4`. Six hundred thousand fills, every hit
canonicalised under all `9! = 362 880` relabellings, one orbit.

That is a strong test and it is **not** the statement it looks like.
The statement it looks like is *"the 27-member family on nine points is
unique up to relabelling"*, which would be a theorem. What the test
actually checks is *"no counterexample is reachable by this process
within this budget"* — and the process is a random fill, which visits
only the maximal families its own basin structure lets it reach. The
exhaustive census was attempted three times and did not finish
(`docs/roadmap.md` §36.3), so the theorem is unproved and the test is
evidence for it.

The same file has a second instance of the same shape, and it is the
sharper one. Over a million fills the size spectrum at `(4, 9)` shows
579 hits at 24, **zero at 25 and 26**, and 19 at 27. Two exact zeros
flanked by hundreds is not noise, and the natural reading — no maximal
family on nine points has 25 or 26 members — is very likely true. It is
still not proved, and
`the_fill_reaches_twenty_seven_but_almost_never` asserts the zero with
a message that names it as a measurement rather than a fact.

The rule this suggests is about wording, not about coverage:

> **A test whose assertion is stronger than its evidence must say so in
> the assertion's failure message.** "No maximal family of size 25 or 26
> was ever reached" and "no maximal family of size 25 or 26 exists" are
> different claims, and the first is the one 10⁶ fills support. A
> failure message that states the weaker claim tells the next reader
> what a failure would mean; one that states the stronger claim invites
> them to treat a sampling artefact as a refutation.

This is the counting-argument counterpart of rule 13 — a search reported
as an answer — applied to a passing test rather than to a failing
acquisition.

### A fourteenth: an assertion the suite could not reach, and the move
###                that let it

`rust/tests/cube_budget.rs` (§49) checks a scheduling decision rather than
a mathematical statement, and that is unusual enough to say why it is
here. The decision is *skip the phase-two re-run of a cube that did not
refine, when phase two adds no budget*. The saving is real — twelve hours
per hard cube — but the risk is not the time. It is that a cube skipped
for want of budget is still **undecided**, and a rung with an undecided
cube that forgot it would report **UNSAT**. UNSAT is the verdict no
witness contradicts, so nothing downstream would catch it.

The first version of the suite could not check that. `phase_two_adds_budget`
was a library function and the split counts came from `sequence_cubes`, so
four of five tests reached their subject — but the fifth thing, that the
skipped cubes are carried into the verdict, lived in
`examples/iota_sym.rs`, and **an integration test cannot reach an example
binary**. It was checked by running it and reading the output, which is an
observation in a roadmap section, not an assertion in a suite: it would
not have failed if a future edit dropped the `carried` term.

The fix was not more tests, it was moving the code. The phase-two
assembly is pure given the stalled set, so it is now
`symbreak::plan_phase_two` returning a `PhaseTwo { fine, carried,
refined }`, with `PhaseTwo::at_limit` as the one place the verdict rule
lives. `a_carried_cube_cannot_become_an_unsat` then says it directly: at
`(4,11,28)` with a cap of 300, equal budgets carry six cubes and
`at_limit(0) == 6`, so an all-UNSAT phase two is still not UNSAT; a
bigger phase-two budget re-runs the same six and `at_limit(0) == 0`. Both
plans account for every stalled cube.

**The general rule this suggests.** When a check cannot be written
because the logic sits in a binary, that is a fact about where the logic
sits, not about what can be checked. Two of the three defects §49 found
were in code no suite could reach — the double-run in the driver, the
checkpoint collision in `tools/rung.sh` — and the shell script is still
unreached.

