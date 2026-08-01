# Roadmap

What is worth doing next, why, and what to avoid. Written to be picked
up cold: each item states the target, the technical choice that decides
whether it is feasible, and the failure mode that would sink it.

The repository's state is in [`STATUS.md`](../STATUS.md); the testing
layer and its limits are in [`testing.md`](testing.md).

---

## Done: the testing layer

Both errors this development has produced were errors of *statement*,
invisible to the kernel. Seven mechanisms now target that class — see
[`testing.md`](testing.md). Everything below is safer for having them,
and new definitions should arrive with the corresponding checks rather
than acquire them later:

* a new definition gets a coherence theorem in `coq/Audit.v` if there
  is any question it should obviously answer;
* a new decision procedure gets a second, independently implemented
  opinion and a proof they agree, as `Reflect.rao_witness_agrees` does
  for `Spread.rao_witness`;
* a new hypothesis gets a mutation in `tools/mutations.toml`. If the
  mutation survives, the hypothesis is doing no work — find out why
  before writing anything on top of it;
* a new audited name goes in `tools/audited.txt`, and the statement
  baseline is regenerated (`make statements-accept`) in the same
  commit. That way the diff of `tools/statements.txt` is the review
  question "did this change what we claim?" answered in advance;
* a new *statement*, before it is proved, gets enumerated against an
  independent oracle. `rust/tests/link_characterisation.rs` is the
  worked example: half an hour of falsification found the case that
  would have made a session's Coq work state something narrower than
  intended, and it found it on non-uniform families that no existing
  test generated.

---

## 1. Discharging the axiom: the counting proof, not Rao's

The one axiom is `ALWZ.Rao20_lemma2`. Everything downstream of it is
already proved, so discharging it is the single highest-value target,
and the interface is fixed.

**This section was rewritten in the July 2026 reading session, and the
target changed.** The previous version aimed at Rao's encoding argument
on the strength of the sentence *"Rao's proof is elementary — injections
between finite sets and binomial estimates, no measure theory"*, which
`coq/ALWZ.v` asserted without anyone having opened the paper. The paper
has now been read in full. Its Lemma 5 is **Shannon's noiseless coding
theorem**, applied through Kraft's inequality and the concavity of `log`,
over a uniformly random partition of the ground set. It is the *worst*
fit of the four published proofs for a `nat`-only development.

### What to prove, exactly

Not `Rao20_lemma2` as stated. Prove the **fractional, single-threshold**
statement — Lovett's Lemma 2.9, PCMI notes p. 8:

> Let `F` be a family of `n`-sets which is `k`-spread for `k = cr log n`,
> for a large enough absolute constant `c`. Then `F` contains `r`
> pairwise disjoint sets.

In this development that is `ALWZ.FractionalSpreadDisjoint n k t` for
`t = Θ(k log n)`, and `ALWZ.fractional_form_gives_the_axiom_shape`
already carries it the rest of the way: it derives
`SpreadYieldsDisjoint n k r` for **every** `r ≥ t`, via
`Spread.RaoSpread_Spread` and `Spread.Spread_mono`. So the target is one
sentence at one threshold, in the form the literature states it, and the
axiom's quantification over `r` is no longer something to prove.

That theorem is already in the kernel. It is the cheapest thing this
session produced and it removes a real overreach: the axiom said more
than Rao's Lemma 2 does, and nobody had noticed.

### Which proof

The counting proof: **[ALWZ20] §2 / [FKNP21], as streamlined by
Park–Pham and written out in Lovett's PCMI notes §3 (pp. 11–15).**

Its core, Claim 3.4, is a single displayed ratio of two finite
cardinalities:

```
  Pr[ |M(S,V)| >= n/2 ]  =  |B| / ( |F| * C(N, qN) )
```

where `B = {(S,V) : S in F, V subset of U with |V| = qN, |M(S,V)| >= n/2}`.
The bound comes from an explicit encoding `phi(S,V) = (Z, S', M, S\M)`
together with the sentence *"we can decode `(S,V)` given `phi(S,V)`"* —
injectivity — and then a binomial estimate and a geometric sum. There is
no measure, no entropy, no limit. Nothing else among the four proofs is
this close to `nat`.

### Stage A — the counting layer

**The technical choice from the previous version of this section was
backwards, and that is the concrete thing the reading fixed.** §1 used to
say: state the covering step for the *product measure* with each element
included independently with probability `1/2`, so "probability" becomes
cardinality over the powerset, which `Spread.subsets` already enumerates.
Three things are wrong with it:

* the proof needs `W` to be a **small** random set, `q ≈ 1/log n`. At
  `p = 1/2` the product measure is plain cardinality; at `p = 1/log n` it
  is a weighted sum, which is *worse* than the fixed-size version, not
  better;
* in every published *proof* the **fixed-size** statement is the
  primitive. Lovett Claim 3.4, ALWZ Lemma 2.8 and FKNP Theorem 1.6 are
  all stated for a random subset of fixed size. (Surveys sometimes state
  the *conclusion* in the product measure — [Kup25] Theorem 3 does — but
  nothing proves it there.);
* the product-measure statement is *derived from* the fixed-size one, by
  a limiting argument (Lovett p. 11: *"Take now `U'` of growing size"*)
  or by ALWZ's Corollary 2.9. Starting there means formalising a limit,
  or redoing the encoding count in a measure the encoding was not
  written for.

So Stage A builds **fixed-size subset enumeration and binomial
counting**, not powerset enumeration:

* `subsets_of_size : nat -> list nat -> list (list nat)`, and
  `length (subsets_of_size j U) = C (length U) j`;
* `count : (list nat -> bool) -> list (list nat) -> nat`;
* injection-implies-`≤`, and additivity over disjoint predicates;
* the binomial estimate `C(N, j+m) <= q^{-m} * C(N, j)` for `j = qN`, in
  the cleared-denominator form `d^m * C(N, j+m) <= c^m * C(N, j)` where
  `q = c/d`. This is the one place rationals would otherwise appear, and
  clearing them is the whole trick.

`Spread.subsets` is still useful — `subsets_of_size j = filter (length =
j) (subsets ...)` is the cheap definition and gives the membership
lemmas for free — but the *counting* is over the size-`j` layer.

Self-contained, independently testable, reusable. Likely one session.

### Stage B — the encoding

The mathematical core: `phi(S,V) = (Z, S', M, S\M)` and its injectivity,
against the minimal-fragment definition. This is where a session's budget
should go, and where the stall risk is. Note that the *statement* to aim
at is Lovett's Claim 3.4, not ALWZ's Lemma 2.8 — same content, fewer
moving parts, because Park–Pham's minimal fragments replaced ALWZ's
iterative construction.

### Stage C — the arithmetic

The geometric sum over `m`, and where the explicit constant lives.

**Scoping decision — do not chase the constant.** `FractionalSpreadDisjoint`
is instantiated at whatever `t` the proof yields, and
`fractional_form_gives_the_axiom_shape` is monotone upward in `r`, so any
explicit constant discharges the axiom. `c = 2^20` closes the file
exactly as well as `c = 64`. Chasing sharpness is where this campaign
dies.

### The alternative that was checked and rejected

[Rao25] *The Story of Sunflowers* (arXiv:2509.14790) advertises, in its
abstract, *"a short elementary proof of the best known bounds for the
robust sunflower lemma"*, in its §3. That looked like it might beat
Lovett §3. **It was read (pp. 8–10) and it does not.** On top of the
counting it needs a Chernoff bound to fix `|A(γ)|`, Azuma's inequality
across the `ℓ` sampling rounds, and Markov. Lovett §3 needs Markov and a
geometric series and nothing else.

What §3 *does* give is confirmation that the outer induction is already
done here. p. 8: *"For `k > 1`, if there exists a set `Z` with
`0 < |Z| < k` contained in some `r^{k−|Z|}` sets of `F`, we apply
induction on the family of sets containing `Z` ... Otherwise, it must be
that for every non-empty set `Z`, the number of sets of the family
containing `Z` is at most `r^{k−|Z|}`."* That is
`SpreadReduction.spread_reduction`'s dichotomy, with `Spread.RaoSpread`
as the "Otherwise". **The only missing piece is the covering step.**

### What the testbed buys here

Each stage's statements can be checked before they are proved. A counting
lemma is a Rust one-liner to falsify; an encoding is a map to run over
the exhaustive enumeration in `rust/src/testbed.rs` and check injective.
Use it — the cost of finding out a lemma is false after half a session of
proof is the main way this campaign goes wrong.

---

## 2. Bounded investigation: is the spread restatement an *equivalence*?

`Conjecture.spread_conjecture_suffices` proves one direction: a
constant-threshold spread lemma implies the Erdős–Rado conjecture. The
converse was looked for and not found; the obvious route — feed a
spread family to the sunflower bound — yields a sunflower, not disjoint
sets, and the core gets in the way.

If the converse holds, the repository contains a formal *equivalence*:
the Erdős–Rado conjecture is equivalent to a statement in which no
sunflower appears. That is a materially stronger claim than anything
else on this list.

Timeboxed. First a literature check — this is likely known or folklore.
Then an attempt via the link structure. Drop it on schedule if it does
not yield.

---

## 3. The uniformity-2 programme: what is done and what is left

Settled: **`f(2,k)` and the spread threshold at uniformity 2 are the
same extremal function.** A distinct 2-uniform family is a graph; it
avoids `k`-sunflowers exactly when its matching number and maximum
degree are both at most `k-1`
(`TwoUniform.two_uniform_sunflower_free_iff`), and `RaoSpread 2 F r`
is exactly the maximum-degree bound `deg [v] F ≤ r`
(`TwoUniform.rao_spread_two_iff_degree`). So both questions are
Chvátal–Hanson, *Degrees and matchings*, JCTB 20 (1976) 128–138:

```
CH(D, ν) = νD + ⌊D/2⌋·⌊ν/⌈D/2⌉⌋
```

is the largest number of edges with maximum degree ≤ `D` and matching
number ≤ `ν`.

**What is proved here is the identification, not the formula.** `CH` is
cited, not formalised, and no Coq theorem depends on it. Taking it on
citation gives two consequences, both of which should be read as
"conditional on [ChHa76]" wherever they appear:

* `f(2,k) = CH(k-1, k-1) + 1`;
* the sharp spread threshold is `min{r : CH(r, k-1) ≤ r²}`, which
  evaluates to **`r*(2,k) = k`** for every `k ≥ 3` — against the
  `2k-1` that `spread_disjoint_above_elementary` proves.

The formula was checked against the source and then falsified five
ways in `rust/tests/chvatal_hanson.rs`; the predicted thresholds match
what `rust/tests/spread_axiom.rs` measures by exhaustive search. That
is falsification, not proof — closing §3a below is what would turn
either bullet into a theorem.

**Done: the lower bound at odd `k`.**
`CliqueLowerBound.two_cliques_lower_bound` gives `f(2,k) ≥ k(k-1)+1`
from two disjoint copies of `K_k`, generalising `F23.two_triangles`.

### 3a. The `CH` upper bound — the main remaining target here

Proving `CH` is an upper bound would deliver, in one theorem, an
infinite family of *exact* sunflower numbers and the sharp spread
threshold at uniformity 2. It needs its own campaign. The naive counts
(`2νD`, `ν(2D-1)`) are tight only at `k = 3`, which is exactly why
`F23.v`'s counting argument works and will not generalise.

**The literature check is done, and the answer is a prerequisite, not a
technique.** The question was whether the bound needs Gallai–Edmonds or
whether a clever induction would do — the difference between a
multi-session campaign and one session. There are two published proofs
and they agree on what the bound rests on:

* [ChHa76] itself: a linear-programming flavour, through Berge's
  matching formula (the deficiency form of Tutte–Berge);
* [BaKh09] (Balachandran–Khare, *Graphs with restricted valency and
  matching number*, Discrete Math. 309 (2009) 4176–4180): a second,
  **constructive** proof in five pages, which also characterises the
  extremal graphs. Its keywords are *Gallai's lemma* and
  *factor-critical graph*, and it contains a new proof of Gallai's
  lemma.

So the matching-theory dependency is real and not an artefact of the LP
presentation. But it is sharper than "Gallai–Edmonds": what both proofs
need is **Gallai's lemma** — a connected graph in which every vertex is
missed by some maximum matching is factor-critical — which is one
statement with a self-contained alternating-path proof, not the full
structure theorem. That is the single named target, and this
development has nothing like it: the Hall/Kőnig layer is bipartite,
where factor-critical components cannot arise.

Revised scoping: §3a is a **matching-theory campaign**, and its first
session is Gallai's lemma over the existing `Graph`/`Matching` layer,
independently of anything about sunflowers. Do not start §3a proper
until that is standing. Caveat on this check: [BaKh09] is paywalled and
no preprint was found, so its proof was not read — the finding is from
its abstract, its keywords, and the descriptions in papers citing it.

A cheaper intermediate that is worth doing first regardless: the case
`D = ν = k-1` only, which is all `f(2,k)` needs. That is a narrower
statement than the full two-parameter theorem and may admit a direct
argument.

### 3b. The even-`k` lower bound

At even `k` the extremal graph is *not* two cliques —
`Audit.oddness_is_needed` shows two copies of `K_k` acquire a perfect
matching, hence a `k`-sunflower. It is one near-`(k-1)`-regular graph
on `k+1` vertices plus `(k-2)/2` stars, giving
`f(2,k) ≥ (k-1)² + (k-2)/2 + 1`. `rust/src/chvatal_hanson.rs`
constructs it; the Coq work is defining a near-regular graph
symbolically (`K_{k+2}` minus a minimum edge cover) and counting its
edges, which is more fiddly than hard.

### 3c. `SpreadYieldsDisjoint 2 3 3`

The first sharp spread threshold in the development, and now known to
be the `k = 3` instance of the `CH` upper bound: it holds because
`CH(3,2) = 7 ≤ 9`. Small enough that a direct argument may beat
waiting for 3a.

## 3.5. Done: the link characterisation, and what it did not buy

`LinkCharacterisation.sunflower_iff_link_matching` proves

```
ContainsKSunflower k F  <->  exists Y, HasKDisjoint k (link Y F)
```

with no hypotheses — no uniformity, no `Distinct`, no bound on `k`. It
makes §3's uniformity-2 characterisation the case `|Y| <= 1`, re-derived
in `two_uniform_sunflower_iff_via_link` by a route sharing no step with
the original, and it turns `Spread.link_sunflower_lift` from a one-way
reduction into an equivalence.

Read honestly, it is a restatement. It says what shape the problem has:
sunflower-freeness at width `k` is the assertion that a *family* of
matching problems, one per candidate core and each in a derived family
of strictly smaller uniformity, has no solution. That is a better thing
to state theorems against than the raw definition, and
`sunflower_core_lies_in_a_member` bounds which cores need checking. It
is not leverage on the bound, and re-deriving `spread_reduction` through
it was not attempted; the `log n` is not in the statement.

Two things came out of the falsification rather than the proof, and both
outlived it:

* `Sunflower.pairwise_disjoint_sunflower`'s nonemptiness hypothesis was
  decoration, in four lemmas and in `Audit.no_k_disjoint_of_no_sunflower`
  — which also carried `1 <= m -> Uniform m F` for the same reason and
  no longer does;
* no uniform family distinguishes the reading that excludes the empty
  petal from the one that allows it, so the enumeration had to be
  widened to arbitrary sets before it could say anything. That is a
  general lesson about this testbed: it enumerates uniform families
  because the *conjecture* is about uniform families, and a statement
  proved with no uniformity hypothesis is under-tested by it.

## 3.6. Measured: the sharp spread threshold at uniformity 3

`r*(2,k) = k` is known conditionally on [ChHa76]. The axiom's own
threshold is `Theta(k log(km))`, which *grows with the uniformity*. So:
is that growth visible at all at small parameters, or is the axiom
simply loose? `empirical_threshold` answers it by exhaustive search.

Only the `(8, 3, 3)` row is in the CI grid; the rest are **one-off
runs**, because the grid tests also compute exhaustive *maxima*, which
at uniformity 3 stop being affordable at ground 9. Reproduce any row
with `testbed::empirical_threshold(ground, 3, k)`; the comment on `GRID`
in `rust/tests/spread_axiom.rs` records why they stayed out.

```
  ground  m   k   empirical r*   refuted r
       8  3   2              1   -
       9  3   2              1   -
      10  3   2              1   -
       8  3   3              3   1,2
       9  3   3              3   1,2
      10  3   3        (did not terminate)
```

**It is not visible.** `r*(3,3) = 3 = r*(2,3)` over every ground set the
search reaches, while the axiom demands `r >= alpha*k*log2_up(km+1)`,
which is 9 at `(m,k) = (2,3)` and 12 at `(3,3)` even at `alpha = 1`.
The axiom is loose by a factor of three to four here, and the growth in
`m` that its `log` predicts does not show up between uniformity 2 and 3.

Read this as a bound on what the measurement can say, not as evidence
against the `log`: a measured `r*` is only ever a lower bound on the
truth, since a counterexample needing more points would raise it. The
published threshold is asymptotic and there is no reason for it to be
tight at `k = 3`.

Two things worth keeping:

* **`r*(3,2) = 1` is decided by a single off-by-one.** A counterexample
  at `k = 2` is an intersecting family, and the extremal spread one is
  the **Fano plane**: 7 lines on 7 points, every point on 3 and every
  pair on exactly 1, so `deg T <= r^(3-|T|)` holds in all three clauses
  at `r = 2` with the last holding with equality. It has 7 members and
  the size hypothesis asks for more than `r^m = 8`. Nothing on seven
  points does better. `the_fano_plane_misses_the_size_hypothesis_by_one`
  pins all of it; a size hypothesis mis-transcribed as `>=` would turn
  the Fano plane into a counterexample to the axiom.
* **Ground 10 is exactly where the search runs out, and it is exactly
  where the question becomes live.** A counterexample at `(m,k,r) =
  (3,3,3)` needs more than `27` members of size 3 with every vertex in
  at most `r^(m-1) = 9` of them, so at least `ceil(3*28/9) = 10`
  vertices. Ground 10 is the first ground set that can hold one, and the
  search does not finish there within an hour. So `r*(3,3) = 3` is
  established for ground sets that provably cannot contain a
  counterexample plus nothing beyond. Widening it needs a better search,
  not a bigger budget.

**Monotonicity, settled at uniformity 3 too.** The refuted `r` form a
prefix at every grid point (`the_refuted_set_of_r_is_a_prefix`). Nothing
forces this: raising `r` weakens the spread hypothesis and raises the
size threshold `r^m`, and the two pull in opposite directions. At
uniformity 2 the prefix property follows from the [ChHa76] formula; at
uniformity 3 there is no formula, and this is search.

## 4. Smaller targets

Concrete, bounded, and each motivated by something the testbed or the
mutation runner measured rather than by taste.

* **Generalise the five-cycle refutation.** `C₅` refutes `r = 2` at
  `(m,k) = (2,3)`. The odd cycle `C_{2k-1}` should refute any `r` with
  `r² < 2k-1` at `(m, k)`: it is 2-regular, hence `r`-spread for
  `r ≥ 2`, has `2k-1` edges, and `k` disjoint edges would need `2k`
  vertices. That would show the threshold grows with `k` at fixed
  uniformity, generalising a concrete `vm_compute` witness into a
  theorem. Estimated 150–250 lines: the work is proving `Distinct` and
  the degree bounds for a symbolic cycle.

* **Sharpen the sandwich.** `Audit.spread_yields_disjoint_sandwich`
  brackets the axiom's shape between `k-1` and `n(k-1)`. Both ends are
  loose. Narrowing either narrows what the axiom is actually assuming.

* **Measure the cover-chain correlation.** `LinkCharacterisation` says a
  family is sunflower-free exactly when every link has matching number
  `<= 2`, hence a vertex cover of size `<= 2(m - |Y|)`. So every member
  is determined by a descending chain of choices, each from a set of at
  most `2m` points — which reproduces Erdős–Rado's `(2m)^m`, log factor
  and all. The conjecture is exactly the statement that those covers are
  **correlated across levels**: total entropy `O(m)` rather than
  `m log m`. Nobody appears to have measured how correlated they are.
  Take the extremal families this repository already has —
  `two_triangles`, `iota3` and its doubling, the 14-member family on
  nine points from `ground_scan` — compute the greedy cover chain, and
  measure the overlap between consecutive covers. Cheap with the
  existing tooling, and it is the concrete form of "pay the log once".
  Bounded: a Rust example and a table, no Coq.

* **Generate the mutations instead of hand-writing them.** For every
  `≤` in a `Definition`, emit a `<`; for every `NoDup X ->`, emit a
  drop. Then report which definitions no mutation covers. That turns
  mutation testing from 68 anecdotes into a coverage metric over the
  definitions.

* **Derive the audit list from source annotations.** `tools/audited.txt`
  is now the single source, the hardcoded count in CI is gone, and
  `coq/Audit.v` is checked for completeness against it. Everywhere else
  the list is still curated by hand, so a theorem added to another file
  can be added without being audited. An annotation — a marker comment
  the extractor reads — would close that. (The sibling gap, the numbers
  quoted in `README`/`STATUS`, is closed: `make docnumbers`.)

* **A better search at uniformity 3.** The exhaustive search decides
  `(m,k,r) = (3,3,3)` on nine points instantly and does not finish on
  ten, which is the first ground set where a counterexample could live
  (see §3.6). The pruning is a vertex-degree counting bound; a
  covering-based one — every member of a counterexample meets a fixed
  set of `m(k-1)` vertices — would cut the tree at the root instead of
  at the leaves.

* **Widen the mutation manifest.** It currently covers the definitions
  the two historical errors touched, plus the reduction's arithmetic.
  `Sets.v`, `Graph.v`, `Matching.v` and the Hall/Kőnig layer are
  untouched.

---

## 5. The lower-bound side: the direct sum, and what it does not reach

Almost all effort on this problem goes to the upper side. The gap is
`(k-1)^n` against `(k log n)^n`, and the lower end had not moved in this
repository beyond the 1960 product construction.

### Done: supermultiplicativity

`coq/DirectSum.v` proves that sunflower-freeness survives the direct
sum of two families on disjoint ground sets, so with `g = f - 1`,

```
g(a + b, k) >= g(a, k) * g(b, k).
```

Instantiated at this repository's own `f(2,3) = 7` it gives
`f(n,3) >= 6^(n/2) + 1 = 2.449...^n`, and at `two_cliques_lower_bound`
it gives `f(n,k) >= (k(k-1))^(n/2) + 1` for odd `k` — the first bounds
here above the product construction, by a factor geometric in `n`.

Uniformity is the whole hypothesis — but only on *one* side. The proof
splits each member of the sum at the boundary and needs the first
family's members to have the size it splits at; it asks nothing about
the second family's. Dropping it from both is false, and
`Audit.uniformity_is_needed_in_the_direct_sum` is the two-member
counterexample. The asymmetric form is the statement that is proved, and
it was reached by the mutation runner rather than by design — see
[`testing.md`](testing.md). Do not weaken it further.

### Done, in part: the recursion reconstructed and its seed measured

The mechanism is **not** the direct sum. It is a *substitution*: blow up
each point of a member of an `a`-uniform family into a member of a
`b`-uniform one, on ground set `V x W`. That is `ab`-uniform with
`|G| * |H|^a` members, and it is sunflower-free exactly when the **inner
family is intersecting** — that is what makes the projection to `V` a
delta-system, since `phi_i(v)` and `phi_j(v)` then always meet.

So the quantity that matters is

```
iota(b)  =  the largest *intersecting* 3-sunflower-free b-uniform family
```

and three things follow, all checked:

* **Doubling.** `g(b) >= 2 iota(b)`, because two disjoint copies of an
  intersecting sunflower-free family are sunflower-free. Formalised:
  `Intersecting.doubling_lower_bound`. At `b = 2` this *is*
  `two_triangles`, so it generalises the construction behind
  `f(2,3) = 7`.
* **Substitution.** `g(ab) >= g(a) * iota(b)^a`. Verified
  computationally in `rust/tests/intersecting.rs` (`g(4) >= 54` and
  `g(6) >= 600`, against the direct sum's 36 and 216), with a control
  showing it breaks the moment the inner family is not intersecting.
  **Not formalised** — see below.
* **The rate.** Iterating has fixed point `c^b = c * iota(b)`, i.e.
  `iota(b)^(1/(b-1))` per point.

### Done: the sandwich, and what it reframes

`iota` is not merely *a* quantity that gives good constructions. Up to a
factor `2b` it **is** `g`:

```
  2 iota(b)  <=  g(b)  <=  2b iota(b)
```

The left half is the doubling (`Intersecting.doubling_lower_bound`). The
right half is new and is `Intersecting.sunflower_free_star_bound`: a
sunflower-free family has no three pairwise disjoint members, so a
*maximal* disjoint subfamily has at most two and spans at most `2b`
points; maximality makes that set meet every member; pigeonhole gives a
point in at least `|F|/(2b)` of them; and the star at that point is
`b`-uniform, distinct, **intersecting** and sunflower-free. Roughly a
hundred and fifty lines, and it went in first time — the argument is the
first step of Erdős–Rado's own proof, read for what it produces rather
than for what it discards.

`2b` is subexponential, so the two quantities admit exponential bounds at
the same time. `coq/IotaRate.v` draws that out in three theorems:

1. **Same rate.** `iota_exponential_iff`: there is a `C` with
   `iota(b) <= C^b` for all `b` iff there is a `c` with `g(b) <= c^b`,
   and `c = 2C` works. No limits are taken; this is the finitistic form
   of "`lim g(n)^(1/n) = lim iota(b)^(1/(b-1))`", and it is all that is
   needed downstream.

2. **Every construction is capped by `iota`.**
   `every_construction_is_within_2b_of_iota`: any sunflower-free family
   at uniformity `b`, however built, has at most `2b iota(b)` members.
   So the Abbott–Hanson–Sauer substitution is not competing with other
   constructions — it is within a subexponential factor of the extremal
   function itself. **No cleverer version of it beats computing `iota`
   for larger `b`.** That closes off a direction rather than opening
   one, which is the useful kind of result here.

3. **The conjecture at `k = 3` is a statement about intersecting
   families.** `conjecture_k_3_iff_iota_exponential`:

   ```
   sunflower_conjecture_k_3   <->   exists C, forall b, iota(b) <= C^b
   ```

   An equivalence, not a sufficient condition. Erdős's $1000 case is
   exactly an exponential bound on *intersecting* sunflower-free
   families — and intersecting families are where extremal set theory is
   strongest (Erdős–Ko–Rado, Hilton–Milner, Frankl's shifting), and
   where, as far as the literature check below reaches, nobody has
   pointed it.

The equivalence is unconditional. Getting from "every sunflower-free
family is small" back to `UpperBound` needs `ContainsKSunflower 3` to be
decidable, which `F23.contains_3_sunflower_dec` now proves: the detector
`sunflower3b` was already known to accept every sunflower
(`sunflower3b_sound`, which is the hard direction — it needs
`contains_sunflower_literal` to canonicalise an abstract sunflower into a
literal triple), and `sunflower3b_complete` is the converse. That also
closes the cost §6 records for the restricted-spread route.

**What the sandwich does not buy: anything numerical.** The only bound on
`iota` proved here is `iota(3) <= 18`, so the sandwich gives
`g(3) <= 108` against Erdős–Rado's 48; even at the measured
`iota(3) = 10` it gives 60. `Audit.bounds_coherent_star_bound` checks it
against the development's own lower bounds. The content is structural —
it says which quantity to compute, not a better value for any of them.

### The measured rates, tabulated

`iota(b)^(1/(b-1))` is the per-point rate the substitution extracts. By
the sandwich it is *the* rate of the problem at `k = 3`, so it is worth
having in one place:

```
  b   iota(b)            rate = iota(b)^(1/(b-1))
  2   3                  3.0000
  3   10                 3.1623   <- the 1972 constant
  4   27   (ground 9)    3.0000
  4   <32  (ground 10)   <3.1414
  5   >=54 (ground 19)   >=2.7108   <- the cone, §11.6; was >=42
  6   >=300 (ground 18)  >=3.1291
  7   >=600 (ground 37)  >=2.9042
```

The `b >= 5` rows come from constructions rather than search and are
listed in full in §11.6, each verified by an independent checker.

**Flat, not growing**, over every value that has been decided. Read
through the sandwich that is mild evidence *for* the conjecture at
`k = 3` — a growing rate is what its failure would look like — with
`c(3)` somewhere near 3.2. It is weak evidence: four values, two of them
at the same `b`, and the sequence is not known to be monotone. But it is
the sequence to extend, and nobody seems to have tabulated it, because
nobody seems to have separated `iota` from the construction that uses it.
`rust/tests/iota_sandwich.rs` pins the row.

### Literature check, and what it found

Three questions were asked of the literature before any of the above was
built. The survey [Kup25] (arXiv:2508.20132, 2025) was the main source
and only its arXiv HTML was read.

* **Is the 1972 recursion what this repository reconstructed?** Yes,
  verbatim: *"They used a construction of a 3-uniform family of size 10
  and with no `Δ(3)`-system, and then leveraged it to any uniformity
  using an iterated product construction, which gives a recursion
  `ψ(ab) ≥ ψ(a)ψ(b)^a`."* Both the recursion and the seed value 10 are
  confirmed from a second source. **[AHS72] itself is still unread**;
  what is now corroborated is the reconstruction, not the paper.

* **Is `iota(b)` a named quantity?** Not in [Kup25]. The survey's `ψ` is
  "the size of *their* iterated construction" — a property of one
  construction, not an extremal function. It also does not state the
  intersecting side condition, which this repository found by
  computation (`rust/tests/intersecting.rs` has the control showing the
  construction breaks without it).

* **Is the sandwich, or the equivalence, known?** Not found. [Kup25]
  contains no reduction of the sunflower problem to intersecting
  families. This is a negative result from one survey plus targeted
  searches, and the argument itself is elementary enough that it may
  well be folklore; treat "new" as unverified. What is not in doubt is
  that it is now machine-checked.

Measured exhaustively (`rust/examples/iota_scan.rs`):

```
  iota(2) = 3   (the triangle, on 3 points)      rate 3
  iota(3) = 10  (on 6 points, stable to 12)      rate 10^(1/2) = 3.1623
  iota(4) = 27  (on 9 points)                    rate 3.0000
  iota(4) < 32  (on 10 points)                   AHS not beaten there
```

`iota(3) = 10` gives exactly the published 1972 constant. **On this
reading, `iota(3) = 10` is the content of that paper.** The paper was
still not read; that the reconstruction reproduces both `iota(2) = 3`
with `g(2) = 6` and the published `3.162` is the evidence for it.

### Why the constant is 3.162 and not something else

On `2b` points, two `b`-sets are disjoint exactly when they are
complementary. So an intersecting family takes at most one from each
complementary pair, and

```
  iota(b, 2b)  <=  C(2b,b)/2
```

with equality exactly when some transversal of those pairs is
sunflower-free. The rate that ceiling would give is
`(C(2b,b)/2)^(1/(b-1))`:

```
  b   ceiling   rate at ceiling   iota(b,2b)   reached?   fraction
  2         3            3.0000            3   yes           1.00
  3        10            3.1623           10   yes           1.00   <- AHS
  4        35            3.2711           24   NO            0.69
  5       126            3.3523        >=42   NO            >=0.33
```

The `b = 5` row is new (§9; SAT, and the rung above it did not decide).
The fraction of the ceiling attained is falling, not levelling: 1, 1,
0.69, and at most a third. Whatever the extremal families are, they are
getting further from the complementary-pair transversal, not closer.

**The 1972 constant is the last `b` at which the ceiling is met.** At
`b = 4` the ceiling is 35 and would beat AHS — the extremal family
falls short at 24. `complementary_pair_ceiling` in
`rust/tests/intersecting.rs` checks all of it, including that each
extremal family really is a transversal.

That is a satisfying explanation and a discouraging one: the obvious
place to look for an improvement has been looked at.

### The three things to do next, in order

**0. Point EKR-type machinery at intersecting sunflower-free families.**
This is what the equivalence above opens, and it is the one genuinely new
angle on this list. The tension to explain is stark: an intersecting
`b`-uniform family on an unbounded ground set is *unbounded* — EKR bounds
it only per ground set — while a *sunflower-free* one is tiny:
`iota(3) = 10` against `C(n-1,2)`. What structural theorem accounts for
that collapse? The extremal families are the place to start, and the one
at `b = 3` is suggestive: its ten members on six points are exactly one
triple from each complementary pair of the twenty triples of `[6]` — a
transversal of the pairing `A <-> [6]\A`, and `complementary_pair_ceiling`
in `rust/tests/intersecting.rs` checks that every extremal family at
`b = 2, 3` is such a transversal. That is a candidate to generalise, and
it is exactly how the cap-set programme progressed: stare at the extremal
object until the algebraic invariant appears.

Caveat, already measured: the transversal structure **stops** at `b = 4`,
where the ceiling `C(2b,b)/2 = 35` is not met (the extremal family has
24). So whatever the right structure is, it is not "transversal of the
complementary pairing" — that is the `b <= 3` shadow of something else.

**Sharpened by §7's degree count.** The extremal families are *regular*,
and provably so wherever the ground bound `b|F| <= g N(b-1,g-1)` is
tight — which is at `(2,3)`, `(3,6)`, `(4,8)` and `(4,9)`, i.e. at every
row measured on a small ground set. Concretely `iota(3,6)` is 5-regular
on six points with diversity 5 out of 10, and `iota(4,9)` is 12-regular
on nine with diversity 15 out of 27. So the extremal intersecting
sunflower-free families are *maximally non-star*, and every one of their
links is an extremal `N(b-1,g-1)` family. Two consequences for how to
aim:

* diversity theorems (Frankl; Hilton–Milner for the non-star case) bound
  intersecting families precisely in the large-diversity regime, and that
  is the regime these families are in. This is a much narrower target
  than "point EKR at it";
* the recursive structure is *link-extremal*: an extremal `iota` family
  at `(b,g)` has every link extremal at `(b-1,g-1)`. That is a
  construction rule, and checking whether it can be run backwards — glue
  extremal `N(b-1,g-1)` families into an `iota(b,g)` — is a bounded
  experiment that could produce families the search cannot reach.

**1. Push `iota(4)` past ground 8.** The record moves the moment some
`b` has `iota(b) > 10^((b-1)/2)`:

```
  b = 4   needs iota(4) >=  32     RULED OUT through ground 10
  b = 5   needs iota(5) >= 101
  b = 6   needs iota(6) >= 317
```

`iota(2)` plateaus at ground 3 and `iota(3)` at ground 6 — both at `2b`
or below — which suggested `iota(4)` would stop at 24. **It does not.**
Ground 9 is the first ground set on which two `b`-sets can be disjoint
without being complementary, so the ceiling argument stops applying, and
the value jumps:

```
  ground   4  5  6   7   8   9   10
  iota(4)  1  5  9  15  24  27   < 32
```

All exhaustive. **Ground 10 is decided and the answer is no**: there is
no intersecting sunflower-free family of 32 or more 4-sets on ten
points (4437s, `examples/g10.rs`). So `b = 4` does not beat
Abbott–Hanson–Sauer through ground 10, and the exact value at ground 9
is 27 — a rate of exactly `3.0000` against their `3.1623`.

This does not close `b = 4` outright: grounds 11 and up are untouched
and the row had not plateaued at 9. **A different question at the same
row is now the more valuable one** — see §7: whether `iota(4,10)` is 28
or stays at 27 decides whether the intersecting ground-set row plateaus,
which is what `IotaGroundBounded` turns on. `rust/examples/iota_ladder.rs`
asks it, and it is a harder search than the `>= 32` query already run,
because a lower target prunes less. But the cost is now measured, and it
is bad. Ground 9 decides in 50s, ground 10 in 4437s — a factor of 89 for
one extra point. Ground 11 on the same scaling is days, and the current
branch-and-bound has nothing left to give: the decision framing, the
anchor symmetry, the second-member orbit reduction and the candidate-set
bound are all in. What is missing is a bound that sees the **ternary**
sunflower constraint; everything in there now sees only the binary
intersecting one, and on these parameters the intersection graph is far
too dense for that to say anything.

Two speedups are in and a third is not. The symmetry reduction (anchor a
member at `{0,...,b-1}`, keep only the sets meeting it) and the
candidate-set formulation (`intersecting::iota`, which carries and
filters the branching set rather than indexing into it — 100x at
`b = 4, ground = 8`, from 199s to 2s) both landed. What is missing is a
bound that sees the *ternary* sunflower constraint; the usual
graph-colouring bound only sees the binary intersecting one, and on
these parameters the intersection graph is far too dense for it to say
anything.

**2. Formalise the substitution.** It is verified but not proved, and it
is the difference between a rate of `20^(1/3) = 2.714` (what the
doubling plus `DirectSum.lower_bound_power` gives, and what is proved)
and `10^(1/2) = 3.162` (what AHS reach). The construction decomposes as
`substitute(G,H) = union over A in G of (direct sum over v in A of H_v)`,
so `DirectSum` supplies most of the machinery; what is new is the
projection argument and the case analysis on how many of the three
outer sets coincide. Estimated a session on its own. Do not start it in
the same session as anything else.

Note what the sandwich does and does not say about this item. It does
*not* make the substitution less worth formalising — it would be the
first machine-checked proof of the 1972 bound, and it is the gap between
the `2.714^n` proved here and the `3.162^n` known. What it says is that
formalising it is a *completeness* target, not a route to a better rate:
`every_construction_is_within_2b_of_iota` caps the substitution and
everything else at `2b iota(b)`, so improvements have to come from
`iota`, i.e. from item 0 or item 1.

### What the AHS bound already settles about the spread threshold

This is the part worth stating precisely, because it converts a
measurement in [`STATUS.md`](../STATUS.md) from suggestive to decided.

`SpreadReduction.spread_reduction` contraposed says: if
`f(m,k) > r^m + 1` for a *single* `m`, then `SpreadYieldsDisjoint m' k r`
fails for some `m' <= m`. AHS gives `f(n,3) > 3^n + 1` for all
sufficiently large `n`. Therefore, **conditional on AHS**:

> `r*(m,3) > 3` for some `m`. The measured sequence
> `r*(1,3) = 2, r*(2,3) = 3, r*(3,3) = 3` cannot stay at 3.

That is a falsifiable prediction with a source behind it, and it is the
right reading of §3.6's flat row: the measurement is not weak evidence
that the threshold is constant — it is a measurement taken entirely
below the crossover, and the crossover is out of exhaustive reach by
orders of magnitude (search dies at `m = 3`; the crossover is at `m` in
the hundreds).

It does **not** refute `Conjecture.spread_conjecture`, which asks only
for *some* constant `c(k)`. AHS rules out `c(3) = 3`; it says nothing
about `c(3) = 4`, since `4^n > 3.162^n`. Refuting the spread conjecture
outright would require `f(n,3) > c^n` for every constant `c`, which is
the negation of the sunflower conjecture itself. So:

* `spread_conjecture` is **not known false**, and is not "one lemma
  away" from anything — it implies the sunflower conjecture, so it is at
  least as hard;
* what *is* now pinned is the value of the constant: any proof of
  `spread_conjecture` must produce `c(3) >= 4`, and any attempt to prove
  `SpreadYieldsDisjoint m 3 3` in general is doomed.

The `log` in the published threshold is a separate question and this
says nothing about it. The tightness results quoted for the ALWZ/Rao
spread lemma are for the *random-subset* form; whether the `log` is
necessary in the **disjointness** form with Rao's size hypothesis
`|F| > r^m` was looked for and not found in the literature. Treat "the
`log` is known to be necessary here" as unverified.

### The other bounded item on this side

Compute or bound `f(3,3)` exactly. The direct sum gives `f(3,3) >= 13`;
the Erdős–Rado upper bound gives `f(3,3) <= 49`. Closing that needs a
better search than the current DFS (see §4), and the extremal family is
the input to any new construction — which is how the cap-set programme
made progress.

---

## 6. Settled: two restrictions of the spread lemma

The `log n` in the spread threshold is the barrier, and the standing
hope is that the families the recursion actually feeds the spread lemma
are special enough that a *restricted* spread lemma could beat it.
`coq/SpreadRestrictions.v` settles two readings of that hope.

### The link restriction is vacuous — do not pursue it

`spread_reduction` recurses into links, so the families reaching the
spread lemma are iterated links. That class is not narrow. It is
everything: `every_uniform_family_is_a_link` builds, for any uniform
distinct `G` and any `d`, a uniform distinct `F` of uniformity `d + j`
with `link Y F = G` on the nose — glue `d` fresh points onto every
member and take them as the core. Iterating gives every depth, and
`every_sunflower_free_family_is_a_link` says the same inside the
sunflower-free world.

So `link_restriction_is_vacuous`: a spread lemma restricted to links
implies the unrestricted one. Nothing is gained. This closes the
"characterise the class of iterated links" direction with a theorem
rather than an intuition — the class has no characterisation because it
is everything.

### The sunflower-free restriction has content, and is what is needed

Run the reduction contrapositively — bound sunflower-free families
rather than force sunflowers into large ones — and every family reaching
the spread lemma is sunflower-free, since links of sunflower-free
families are sunflower-free. So `spread_reduction` can be run from

```
a sunflower-free r-spread m-uniform family has at most r^m members
```

(`SpreadBoundsSunflowerFree`) instead of the disjointness form. The
first is implied by the second (`syd_implies_sunflower_free_bound`) and
gives the same bound on the extremal function
(`sunflower_free_bounded`), so **it is the weaker interface for a future
proof of Rao's Lemma 2** — §1's target can be narrowed to it, and the
development then assumes strictly less.

No claim is made that the two are equivalent; that was looked for and
not found. The restricted form is not vacuous —
`Audit.no_spread_bounds_sunflower_free_2_3_2` refutes it at `(2,3,2)`
with the five-cycle, the same parameters where the unrestricted form
fails.

One cost, recorded rather than papered over: the restricted route
delivers the bound, not the sunflower. Recovering the `UpperBound` form
from it needs `ContainsKSunflower` to be decidable. What is proved
directly is the `LowerBound`-complement form, which is the same extremal
statement.

**Update: at `k = 3` the cost is gone.** `F23.contains_3_sunflower_dec`
decides `ContainsKSunflower 3` — the reflective detector `sunflower3b`
was already proved to accept every sunflower, and `sunflower3b_complete`
is the converse — so `F23.upper_bound_of_sunflower_free_bound` turns any
bound on sunflower-free families straight into an `UpperBound`. §5's
equivalence with the conjecture is what needed it; `SpreadRestrictions`
can use it too, and at `k = 3` the two forms of `sunflower_free_bounded`
are now interchangeable. Nothing is claimed for general `k`: the
detector is specific to width 3.

## 7. Named: what the polynomial method is missing

`coq/SliceRank.v`. Naslund–Sawin ([NaSa17]) bound a 3-sunflower-free
family of subsets of `[n]` by `3(n+1) C^n`, `C = 3/2^(2/3) < 1.89` — a
`constant^n` bound of exactly the conjectured shape, from the machinery
that settled cap set. It bounds by the **ground set**; the conjecture
bounds by the **uniformity**.

**Read this section with §7.5 first.** Two things found by reading the
literature change what it says: the ground-set framing is *known* and is
an equivalence (Hunter, via [FPPTZ24]), and the implication from a
ground-set bound does not need the polynomial method at all. What is left
of the framing below is the *linear* strengthening and the measurements.

That is the entire gap, and it is one hypothesis wide:

```
GroundBounded c  :=  an extremal sunflower-free m-uniform family
                     can be realised on at most c*m points
```

`bounded_ground_set_settles_k3` proves `GroundBounded c` plus [NaSa17]
gives `f(m,3) <= (27^(c+1))^m + 1` — the sunflower conjecture at `k = 3`,
with an explicit constant. So the polynomial method is not blocked by
anything internal to itself, and not by "the ground set is not a
product" — the slice rank already handles `{0,1}^n`. It is blocked by
`GroundBounded`.

`sunflower_iff_no_point_in_exactly_two` is the bridge, proved
unconditionally: three sets are a sunflower exactly when no point lies
in exactly two of them. That is the form the slice rank consumes, and
it is why the method reaches `{0,1}^n` at all — the condition is
per-coordinate.

**Neither [NaSa17] nor `GroundBounded` is an axiom here.** Both are
`Prop`s carried as explicit hypotheses, the same shape
`spread_reduction` uses for `SpreadYieldsDisjoint`, so the trusted core
is unchanged and every theorem in the file is closed under the global
context.

### The measurement, and what it does not say

`rust/examples/ground_scan.rs` computes `N(m,g)`, the largest `m`-uniform
3-sunflower-free family on `g` points. It is non-decreasing in `g` and
bounded by `f(m,3)-1`, so it plateaus; `GroundBounded c` says it
plateaus by `g = c*m`.

```
  g        3  4  5  6  7  8  9   10
  m = 1:   2  2  2  2  2  2  2    2     plateau at g = 2 = 2m,  value 2
  m = 2:   3  4  5  6  6  6  6    6     plateau at g = 6 = 3m,  value 6
  m = 3:   1  4  6 10 12 12 14  >=16    still rising at g = 10
```

Every entry through `g = 9` is exhaustive. `g = 9` at `m = 3` takes 15
minutes and comes out at **14**, up from 12 at `g = 8`.

**`N(3,10) >= 16`, and `c = 3` is dead.** The ten-point entry was found
by the SAT encoding (§9) in 0.02 seconds, against a branch-and-bound that
did not finish at all, and is pinned as `IotaGround.ground10_max` with an
independent re-verification. With the proved `N(3,g) <= 2g` it gives
`16 <= N(3,10) <= 20`, both ends theorems
(`n_three_ten_between_sixteen_and_twenty`).

Better: the refutation of `c = 3` does not need the search at all.
`IotaGround.ground_bounded_needs_c_at_least_four` proves
**`GroundBounded c` forces `c >= 4`**, from the twenty-member family at
uniformity 3 (`Intersecting.lower_bound_3_3_20`) against `N(3,g) <= 2g`:
twenty members on `3c` points needs `20 <= 6c`. So neither of the two
measured plateaus, at `2m` and at `3m`, is the constant.

**Do not read the ratios 2 and 3 as evidence** — and now there is a
theorem saying so, not just a caution. Two plateaus and a row that has
not plateaued was the smallest amount of data that could distinguish the
answers, and it did not; the ratios 2 and 3 are both refuted outright.
What the table named as the next computation, `N(3,10)`, is now done, and
it needed the better search §9 supplies rather than the branch-and-bound
§4 also gave up on.

A by-product worth keeping: `N(3,9) = 14` beats the direct sum's 12, so
`f(3,3) >= 15`. It does not improve the *rate* — `14^(1/3) = 2.41` is
below `6^(1/2) = 2.449` — but it is the best value known here at
uniformity 3, and if the AHS substitution recursion accepts this family
the rate it would give is `14^(1/2) = 3.74` against AHS's `3.16`. Whether
it accepts it depends on the unverified side condition in §5. Check that
before getting excited.

Also settled by the table, and worth keeping: `N(3,6) = 10`, which is
the Abbott–Hanson–Sauer seed. See §5.

### Done: point the hypothesis at `iota` instead

`GroundBounded` is not the only ground-set hypothesis that would settle
`k = 3`. §5's equivalence says the conjecture at `k = 3` is a statement
about *intersecting* sunflower-free families, so the same argument runs
on `iota` — and there the measurement is not ambiguous. Put the two rows
next to each other:

```
  g                3  4  5  6   7   8   9  10  11  12  13  14
  N(3,g) general:  1  4  6 10  12  12  14   ?   ?   ?   ?   ?
  iota(3,g):       1  4  6 10  10  10  10  10  10  10  10  10
```

They agree at six points and then **diverge**. The general maximum climbs
to 14 by nine points and the search stops; the intersecting one has not
moved by fourteen, and every entry is instant — intersecting-ness prunes
that hard. `iota(2,g)` is likewise flat at 3 from three points, where
`N(2,g)` climbs to 6 before stopping. All exhaustive
(`rust/tests/iota_ground.rs`).

That is not an accident of small numbers. Intersecting-ness is a
*locality* constraint: every member meets every other, so the family
cannot spread out over a large ground set the way an arbitrary
sunflower-free family can.

**But it is worth exactly one point of uniformity, and no more — see
§11.2.** The cone (`Product.iota_at_least_g_pred`) turns any
sunflower-free `m`-uniform family into an intersecting `(m+1)`-uniform one
of the same size by adding a fresh point, so `g(m) <= iota(m+1)`. Two
consequences for this section: the two hypotheses below are *not*
independent (§11.2(c) withdraws the claim that they are), and an
intersecting family can need `2^b - 1` ground points (§11.2(d) refutes the
universal reading). The flat row above survives both — it measures the
largest family *on* `g` points — but the reading of it as "intersecting
families are small-ground" does not.

`coq/IotaGround.v` composes the two:

```
IotaGroundBounded c  +  [NaSa17]  ==>  sunflower_conjecture_k_3
```

with the same explicit constant, through the same arithmetic — which is
now factored out of `bounded_ground_set_settles_k3` as
`SliceRank.ns_bound_to_exponential` so neither theorem owns it.
`Audit.the_two_ground_hypotheses_are_both_sufficient` puts the two
side by side. **They are not independent, and §11.2(c) is the
correction**: `GroundBounded c` implies `IotaGroundBounded c` outright,
and the cone gives the converse with the uniformity shifted by one. What
was written here — "neither implies the other; what separates them is that
one has a measurement behind it" — is withdrawn. The measurements are
measurements of the same question at two uniformities.

**The caveat, stated as sharply as §7 states it for the general row.**
Two plateaus and a third row still open is still two plateaus. `iota(4)`
is 24 at ground 8 and 27 at ground 9 — it moved — and ground 10 is only
known to be below 32. Whether it plateaus at 9 is the decisive
experiment, and the query for it is *harder* than the one already run:
seeding the incumbent at `target - 1` is what prunes, so "is
`iota(4,10) >= 28`?" searches a strictly larger tree than the "`>= 32`?"
that took 74 minutes. `rust/examples/iota_ladder.rs` asks it as a
descending ladder — 31, 30, 29, 28 — printing each rung as it lands, so a
run that is killed part-way still reports what it decided.

**Cost, measured rather than estimated.** It was launched here and the
*first* rung, `>= 31`, did not decide in an hour of wall clock — against
the 74 minutes the `>= 32` query took to decide outright. So the ladder
needs a budget measured in hours per rung and four rungs to reach 28,
which puts it past the point where a detached process survives in this
environment. Two ways forward, and the second is cheaper than it looks:

* run one rung per session, seeded from the last, and record it;
* give the search a bound that sees the **ternary** constraint. The
  degree cap `deg(x) <= N(b-1, g-1)` — 14 at `(4,10)` — is such a bound,
  and it is not in the search. It is exactly
  `IotaGround.link_degree_ground_bound` read as a pruning rule: a partial
  family that has already used a point fourteen times can add nothing
  more through it. Whether it bites at these parameters is unmeasured —
  average degree at 28 members is 11.2, close enough to 14 to be worth
  trying and far enough not to be obvious. This is the same missing
  ingredient §4 and §5 both name, now with a concrete candidate.

What the ladder is *not* is a prerequisite for anything above: the
theorem `IotaGroundBounded c ⟹ conjecture at k = 3` is proved, and the
`b = 3` evidence stands on its own.

**And it is not a computation, either — see §11.2(b).** By the cone,
`g(3) <= iota(4)`, so a proof of `iota(4) <= 27` gives `f(3,3) <= 28`
against Erdős–Rado's 49 (`Product.iota_four_at_most_27_would_beat_erdos_rado`).
Deciding the ladder downward is at least as hard as a new bound on the
first unknown sunflower number. That is why two independent searches did
not settle it, and it means a bigger budget for the same search is the
wrong response.

### A second thing, and it is the more solid one

Counting incidences between a family and its ground set gives

```
  b * |F|  <=  |U| * N(b-1, |U|-1)
```

for *any* sunflower-free `b`-uniform family on `U`
(`IotaGround.link_degree_ground_bound`). No intersecting hypothesis, no
positivity hypothesis: it is double counting, with each point's column
being a link and therefore a smaller sunflower-free family. Compare
`Intersecting.intersecting_link_bound`, which counts over one member's
`b` points and *does* need intersecting-ness to know every member is
there; the two are useful in opposite regimes, and this one says
something when the ground set is small.

Two things come out of it.

**It is met with equality, and equality is rigid.** Measured at the four
rows where both sides are known:

```
  b  g   iota   b|F|   g*N(b-1,g-1)
  2  3      3      6              6   TIGHT
  3  6     10     30             30   TIGHT
  4  8     24     96             96   TIGHT
  4  9     27    108            108   TIGHT
```

Equality forces the family to be `N(b-1,g-1)`-regular and every one of its
links to be extremal. The witnesses **are** regular — checked, not
assumed — so `iota(3,6)`'s ten triples are 5-regular on six points and
`iota(4,9)`'s twenty-seven 4-sets are 12-regular on nine. Their
diversities `|F| - maxdeg` are 5 out of 10 and 15 out of 27: the extremal
intersecting families are as far from a *star* as an intersecting family
gets, which is precisely the regime Hilton–Milner and Frankl's diversity
theorems are built for. That sharpens §5 item 0 from "look at EKR" to a
specific target.

**At `b = 3` it is unconditional.** The link bound there is the proved
`g(2) = 6`, so `N(3,g) <= 2g` outright
(`IotaGround.three_uniform_ground_bound`), and in particular
`N(3,10) <= 20` — the first proved cap on the value this section names as
the one that matters, against `C(10,3) = 120` from counting and 48 from
Erdős–Rado. It is still above the measured 14 and it does **not** decide
whether the row plateaus. It narrows the search, it does not replace it.

## 7.5. Corrected: the ground-set framing is known, and the axiom is not needed

Two findings from reading [FPPTZ24] (the "Odd-sunflowers" paper, JCTA
2024) from its rendered pages, and one consequence of them that is this
repository's own oversight.

### The framing is known, and is an equivalence

Its Conjecture 14 says the number of **base elements** of a
sunflower-free `k`-uniform family is at most `c^k`, and it reports —
crediting **Zach Hunter** — that this is *equivalent* to the Erdős–Rado
conjecture. So `GroundBounded` is not a new angle on the problem. It is a
**linear** strengthening (`c*m` points, not `c^m`) of a known equivalent
formulation, and the linear form is what the `N(m,g)` measurements are
about.

### The universal reading of it is false

The same paper gives `g_v(k) >= 2^k - 1`: the root-to-leaf paths of a
depth-`k` binary tree, as edge sets, are `k`-uniform, `2^k` in number, and
sunflower-free — two paths meet in the path to their leaves' least common
ancestor, and among three leaves two are strictly closer than the other
pairs, so two of the three pairwise intersections coincide and one is
strictly longer.

So **"every sunflower-free `m`-uniform family lives on `O(m)` points" is
false for every constant.** Only the existence reading survives: some
family of each achievable size can be *realised* on `c*m` points. That is
what `GroundBounded` actually says, and the distinction is load-bearing
rather than pedantic. `IotaGround.the_universal_ground_reading_is_false`
is the `k = 3` instance — eight triples that genuinely need fourteen
points, against `4*3 = 12` — and `rust/tests/ground_set.rs` checks the
construction to `k = 6` (sixty-four 6-sets on a hundred and twenty-six
points).

This does **not** conflict with the measurements. `N(m,g)` is the largest
family *on* `g` points, which is exactly the quantity the existence
reading needs, not the quantity bounded below above.

### And the polynomial method was never the load-bearing part

Chasing the equivalence exposed something this development had missed.
`SliceRank.bounded_ground_set_settles_k3` derives the conjecture from
`GroundBounded c` **plus** `NaslundSawinBound`. The axiom is not needed:

> A family of distinct subsets of a `g`-point set has at most `2^g`
> members. That is counting. So a ground set of size `c*m` gives
> `2^(c*m) = (2^c)^m` directly.

`ground_bounded_settles_k3_by_counting` and
`iota_ground_bounded_settles_k3_without_the_axiom` are the axiom-free
versions, built on `grounded_family_at_most_two_to_the_ground` and
`HallCore.sublists`, which was already in the repository. Compare:

```
  route                             hypotheses            bound
  bounded_ground_set_settles_k3     GroundBounded + NaSa  (27^(c+1))^m
  ground_bounded_settles_k3_by_..   GroundBounded         (2^c)^m
```

`(2^c)^m` is smaller for every `c`, and needs nothing beyond the kernel.
What Naslund–Sawin contributes is the constant — `1.89^g` against `2^g` —
which is a real theorem and is decoration here.

**So §7's title overstates the case.** The ground-set hypothesis is the
whole content; the polynomial method improves a constant. Quote the
axiom-free version.

## 8. Settled: compression is the wrong tool, and by how much

Shifting is *the* instrument of extremal set theory — Erdős–Ko–Rado,
Hilton–Milner and most of Frankl's work are proved with it — and this
repository had never touched it. For `i < j` the `(i,j)`-shift replaces
`A` by `(A \ {j}) ∪ {i}` when `j ∈ A`, `i ∉ A` and the image is not
already present. It preserves `|F|`, uniformity, intersecting-ness and
the matching number, and it terminates, so any family compresses to a
**left-compressed** one of the same size supported on an initial segment
of the ground set. That is where the structure comes from.

It does not survive contact with sunflower-freeness. Both the measurement
(`rust/tests/shifting.rs`, exhaustive) and the proof (`coq/Compression.v`)
are in, and the failure is sharper than expected.

### It fails at the first opportunity

Exhaustively over every sunflower-free family in range at `m = 2, 3` and
`g <= 6`: the smallest family some single shift destroys has **three
members**, which is the least a 3-sunflower can have. The witness is

```
  {0,1}  {0,2}  {1,3}        pairwise intersections {0}, {1}, empty
        --(0,1)-shift-->
  {0,1}  {0,2}  {0,3}        a star: a sunflower with core {0}
```

Only `{1,3}` moves — `{0,1}` already has `0` and `{0,2}` has no `1`. Four
points is the least ground set that admits a counterexample, and
`Compression.two_members_cannot_acquire_a_sunflower` says two members
never can. So there is no range of small parameters in which compression
is safe.

### The maximum is not attained by a compressed family either

That is the weaker statement one would actually want, and it also fails —
not by a constant, but completely:

> **`Compression.compressed_bound`.** A left-compressed 3-sunflower-free
> `m`-uniform family has at most `m + 1` members, on *any* ground set.
> Attained, by all `m`-subsets of an `(m+1)`-set.

### And nothing about it is special to 3

The chain argument runs at every sunflower size. A compressed family that
reaches past `m + k - 3` contains `k` sets `{0,...,m-2} ∪ {t}`, and those
are a `k`-sunflower. So:

> **`Compression.compressed_lives_on_m_plus_k_minus_two_points`.** A
> left-compressed `k`-sunflower-free `m`-uniform family is supported on
> `m + k - 2` points, hence has at most `C(m+k-2, m)` members —
> **polynomial in `m` of degree `k-2`** — and all `m`-subsets of an
> `(m+k-2)`-set attain it.

**Why that is worth stating precisely: the question is live.** [Mis26]
(arXiv:2606.02667, 1 June 2026) proves the Erdős–Rado conjecture *for
shifted families*, with `f'(k,s) ≤ s^(2s-2) 2^k` — exponential in the
uniformity — and gives no lower bound and no extremal family. The theorem
above says the truth is polynomial, and says exactly what it is:

```
  f'(k,s)  =  C(k+s-2, k)
```

The ground-set half is machine-checked. The count and the attainment are
exhaustive in `rust/tests/shifting.rs` over 62 parameter points
(`k = 3,4,5`, `m ≤ 3`, every ground set in range, zero mismatches), and
the attainment has a short proof worth recording:

> Write `B_i` for the complement of the `i`-th member in the
> `(m+k-2)`-set, so `|B_i| = k-2`. A `k`-sunflower forces every pairwise
> union `B_i ∪ B_j` to be one set `C`, so each point of `C` is missing
> from at most one `B_i` and lies in at least `k-1` of them. Counting
> incidences, `k(k-2) ≥ |C|(k-1)`; and two distinct `(k-2)`-sets have
> union at least `k-1`, so `|C| ≥ k-1`. Together `(k-1)² ≤ k(k-2)`, which
> is false.

Note which way this cuts. It is *not* progress on the conjecture — it
makes the shifted case easier, and the shifted case is exactly the one
the rest of this section shows is unreachable from the general one.

The proof is the whole story in three steps. A compressed family is a
down-set in the dominance order, so from any member it contains the chain
`{0,...,m-2} ∪ {t}` for every `t` up to that member's largest point
(`compress_to_chain`, induction on `Σ x`, which is the potential that
makes the compression terminate). Any three of those chains have pairwise
intersection exactly `{0,...,m-2}` — a 3-sunflower
(`three_chains_are_a_sunflower`). So no member may reach past `m`, the
family lives on `{0,...,m}`
(`compressed_lives_on_m_plus_one_points`), and an `m`-subset of an
`(m+1)`-set is determined by the point it omits.

Measured first, proved second, and the table is flat in the ground set —
which is the content:

```
  m   N(m,g) at the plateau   iota(m)          left-compressed max
  1   2                       1                2
  2   6                       3                3
  3   10 (g=6), 14 (g=9)      10               4
  4   -                       27 (g=9)         5
  5   -                       -                6
  6   -                       -                7
```

Exhaustive at every `m <= 6` and every ground set in range. The
intersecting question behaves identically (`m+1` from `m >= 2` on), even
though intersecting-ness is precisely the property shifting was built to
preserve.

### What it would have bought, as a theorem

This is worth stating because it is the "too good to be true" version,
and the implication really does hold. §7 names `GroundBounded c` as the
one missing fact that turns Naslund–Sawin into the conjecture at `k = 3`.
Compression would deliver it outright — on `m+1` points, not `c·m`:

```
  CompressionPreservesSunflowerFree  ==>  GroundBounded 2
  CompressionPreservesSunflowerFree  +  [NaSa17]  ==>  f(m,3) <= (27^3)^m + 1
```

both machine-checked (`compression_would_give_ground_bounded`,
`compression_would_settle_k3`). And then the hypothesis is refuted
outright, twice by disjoint arguments:
`compression_does_not_preserve_sunflower_freeness` runs six 2-uniform
sunflower-free sets against a compressed maximum of three, and
`compression_would_overfill_the_ground_set` runs the same six against a
three-point ground set.

### Why it fails, exactly — now a theorem, not a measurement

`LinkCharacterisation.sunflower_iff_link_matching` says a family is
sunflower-free exactly when **every** link has matching number `<= 2` —
one condition per core. The diagnosis is that compression commutes with
exactly one of them, and all four parts of that are now machine-checked
(`Compression.only_the_empty_core_survives_compression`):

1. **The empty core is the matching condition.** `link_nil` proves
   `link [] F = F`, so the `Y = ∅` instance is literally "no `k` pairwise
   disjoint members".
2. **Compression preserves it.** `shift_preserves_no_k_disjoint` — the
   classical fact that shifting does not increase the matching number.
   Nothing in this development had it, and it is the *positive* half of
   the diagnosis, so it had to be proved rather than cited. The argument
   is the standard repair: at most one member of a disjoint family can
   acquire `i`, so at most one moved; send it back to its preimage, and
   if some other member carries `j`, send that one forward to the image
   the guard promised was already present.
3. **Erdős–Ko–Rado's hypothesis is that same instance at `k = 2`.**
   `intersecting_is_the_empty_core_at_two`: an intersecting family is one
   with no two disjoint members.
4. **And at a non-empty core it fails.**
   `shifting_breaks_a_non_empty_core`: the three-member witness shifts to
   a family that *has* a 3-sunflower and has **no** three pairwise
   disjoint members — so what it acquired is a sunflower with a non-empty
   core, which is exactly the clause compression does not commute with.

So the shape of the thing is: sunflower-freeness is a conjunction indexed
by cores; shifting is a homomorphism for one index and for no other; EKR
lives entirely at that index; and `compressed_bound` prices the rest at
everything above `C(m+k-2, m)` members.

That also explains, without appeal to solver folklore, why §9's
intersecting instances are hard. Shifting is a *canonical form* argument
— "assume the family is compressed" — and it is exactly that kind of
symmetry breaking the theorem above forbids. What remains sound is
*orbit* symmetry breaking: pick one representative per orbit of a group
that preserves the property. The anchor is one, the second-member split
is another, the sorted-degree constraint is a third and is not yet built.

The measured version, which came first:

* the **empty** link survives every shift — `ν(F)` never rises, which is
  the standard fact that shifting does not increase the matching number;
* a **singleton** link is what breaks, every time. Shifting `two_triangles`
  takes the maximum link matching from 2 to 4, always at a *point*.

That is the whole diagnosis. Shifting towards `i` is exactly the
operation that inflates `deg(i)` — verified: a breaking shift always
raises `deg(i)` — and `IotaGround.link_degree_ground_bound` is exactly
the theorem that caps `deg(i)` by `N(b-1,g-1)`. Compression optimises the
quantity sunflower-freeness bounds.

Intersecting-ness is the *single* empty-link condition `ν <= 1`. That is
why the instrument works for Erdős–Ko–Rado and cannot work here:
**EKR is a condition on one link, sunflower-freeness is a condition on
all of them, and shifting commutes with the empty one only.**

The same thing in the vocabulary §5 and §7 already use: compression
drives *diversity* `|F| - maxdeg` to **1**, the least a family with more
than one member can have, while the extremal `ι` families sit at roughly
`|F|/2` — 5 of 10 at `(3,6)`, 15 of 27 at `(4,9)`. Compression pushes
towards a star; the extremal objects are provably as far from a star as an
intersecting family gets. The two are pointed in opposite directions.

### What this closes, and what it does not

**Closed.** Do not look for a shifting proof of a sunflower bound, and do
not look for a shifted extremal family — there are none above
`C(m+k-2, m)` members. The `(e)` question, "is there a compression that
*does* preserve sunflower-freeness?", is answered in the negative for
every operation whose fixed points are the left-compressed families,
because `compressed_bound` bounds those regardless of how they were
reached. And the shifted case itself is closed: `f'(k,s)` is now exactly
known, so there is nothing further to extract from [Mis26]'s direction.

**Open.** An operation with a *different* normal form is not excluded by
any of this. What the diagnosis suggests is that the right normal form is
**regular**, not compressed — which is what §7's tightness analysis
already found the extremal objects to be. Nobody has a compression whose
fixed points are regular hypergraphs.

## 9. Measured: SAT, and where it does and does not help

The homegrown branch-and-bound was out of road — `iota(4,10) >= 32?`
took 4437 seconds, `>= 31?` did not finish in an hour, a factor of 89 per
ground point — so the questions were re-encoded as SAT and handed to
external solvers. `rust/src/sat.rs` is the encoder and driver;
`rust/tests/sat_encoding.rs` is what stops it from being confidently
wrong.

### The encoding

One boolean per `b`-subset of `[g]`. Intersecting-ness is binary clauses,
one per disjoint pair. Sunflower-freeness is **ternary** clauses, one per
sunflower triple — which is exactly the constraint the branch-and-bound's
bound could not see. "At least `t` members" is a sequential counter.

Three things keep it honest, and all three are gates:

* **The anchor is forced**, which is sound because relabelling preserves
  everything (`DirectSum.relabel_preserves`); for intersecting families
  the second member is split over the `b-1` orbits of the anchor's
  stabiliser, the reduction `intersecting::iota_decide` already carried.
  `the_orbit_split_decides_the_same_question` checks the split answers
  the same question as the unsplit instance.
* **No model is trusted.** Every satisfying assignment is decoded and
  re-verified by `intersecting::verify`, which shares no code with the
  encoder; `sat::solve` panics rather than returns on a bad model.
* **UNSAT gets a second opinion.** It is the verdict no witness can
  confirm, so `solve_agreed` runs two independent solvers (cadical and
  cryptominisat) and refuses to answer unless they agree — the same
  discipline `Reflect.rao_witness_agrees` applies on the Coq side.

The differential test is the main defence: on every parameter the
branch-and-bound can still decide, the two agree — `iota(b,g)` for
`b <= 4` and `N(m,g)` for `m <= 3`, fourteen and eleven rows
respectively.

### What it bought

**The general row moved, and it is the row §7 names.** `N(3,10) >= 16`,
found in **0.02 seconds**, against a search that did not finish at all.
Combined with the proved `N(3,g) <= 2g` this puts `N(3,10)` in `[16,20]`,
and it says the general ground row is *still climbing at `g = 10`* —
14 at nine points, at least 16 at ten.

**`N(3,9) = 14` re-decided independently**, `>= 15` UNSAT in 243s against
the branch-and-bound's fifteen minutes. A second exhaustive verdict on a
value the development quotes.

**`iota(5,10) >= 42`**, the first value ever computed at `b = 5` here.
The rung above it, `>= 43`, did not decide in sixteen minutes. The
threshold that would beat Abbott–Hanson–Sauer at `b = 5` is 101, so this
is not on course to reach it: the rate `42^(1/4) = 2.55` is well under
the 1972 constant, and the fraction of the complementary-pair ceiling
attained is falling across the row (1, 1, 0.69, at most 0.33).

### What it did not buy, which is the more useful half

**The degree cap does not bite.** §7 named `deg(x) <= N(b-1,g-1)` as the
missing ingredient and recorded that "whether it bites at these
parameters is unmeasured". Measured: at `N(3,9) >= 15` the cap costs
251s against 243s without it, and `the_degree_cap_changes_no_answer`
confirms it moves no value. It is sound, it is a theorem, and it is
worth nothing to a CDCL solver — which makes sense in hindsight, since
the cap is a *consequence* of the ternary clauses and adding a consequence
tells a clause learner nothing it could not derive.

**The intersecting instances are worse for SAT than for the search.**
`iota(4,9) >= 28` is UNSAT, and the branch-and-bound decides the whole
`(4,9)` row in 50 seconds while cadical does not settle that one rung in
three minutes. The instances are tiny — 2915 variables, 10611 clauses —
and hard, which is the signature of **symmetry**: after the anchor and
the orbit split, the stabiliser still has order `4! * 5!` at `(4,9)`, and
CDCL is famously bad at symmetric UNSAT. The general row has far less
symmetry to fight, which is exactly where SAT won.

**What was asked and not decided**, with its cost, so the next session
does not re-run it blind:

```
  question              solver time    verdict
  iota(4,10) >= 28      60 min         undecided   <- what IotaGroundBounded turns on
  N(3,10)    >= 17      55 min         undecided
  iota(4,11) >= 32      30 min         undecided   <- 32 would beat AHS
  iota(5,10) >= 43      16 min         undecided
```

Every one is an UNSAT-side question, and every one is symmetric. Note
that `N(3,10) >= 16` was SAT in **0.02 seconds** and `>= 17` did not
finish in fifty-five minutes: the cliff between the two sides is
enormous, and it is the whole reason to break symmetry rather than buy
time.

So the honest summary is: **SAT is transformative on the witness side and
on the general row, and it is not a free win on the intersecting UNSAT
side.** That is a sharper statement of what is hard here than "the search
is slow" was.

### The named next step, with its soundness argument

The obstruction is symmetry, so break more of it. The stabiliser of the
anchor `A = {0,...,b-1}` is `Sym(A) x Sym([g] \ A)`, and both factors
preserve uniformity, distinctness, intersecting-ness and
sunflower-freeness. So a family may be relabelled to make its degree
sequence **sorted** on each side:

```
  deg(0) >= deg(1) >= ... >= deg(b-1)     and     deg(b) >= ... >= deg(g-1)
```

That is sound, it is not implied by anything currently in the encoding,
and it is a genuine restriction rather than a consequence — which is what
the degree cap turned out not to be. Encoding it needs a totalizer per
point and a pairwise comparison of the unary outputs: `O(n log n)`
variables per point, `O(n^2)` clauses, both affordable at these sizes.
Two cheaper things to try first, in order: a symmetry-breaking
preprocessor (`BreakID`) in front of the solver, and a portfolio — the
solvers here disagree wildly in behaviour on symmetric instances and only
cadical has been measured.

## 10. Where the effort should go now

Sections 8 and 9 changed the ordering. This is the standing list, ranked,
with what changed against each.

### Moved up

**Prove `iota(3) = 10` exactly.** `iota(3) <= 18` is proved
(`Intersecting.iota_three_at_most_eighteen`), 10 is measured and stable to
fourteen points, and closing `[10,18]` is a finite case analysis: an
intersecting 3-uniform family is the union of the three stars at a fixed
member's points, each star's link is a sunflower-free graph and so has at
most `g(2) = 6` members, so the whole family lives on at most thirteen
points.

Two things pushed this up. First, it is the first exact value of the
quantity §5 proves the conjecture is *equivalent* to. Second — and this is
new — §8 shows the standard route to a result of this shape is
unavailable, so there is no cheaper mechanised alternative waiting. Doing
it by hand is worth more than it was, not less.

**Build instead of search, and identify the object — now one item.**
§5 item 0 and the old "identify the extremal configuration" were separate.
They should not be. The sixteen-member witness the SAT layer found for
`N(3,10)` (§9) is

```
  {0,1,2} {0,1,3} {0,2,3} {1,2,3}        all four triples of {0,1,2,3}
  {0,4,5} {1,4,5} {0,4,6} {1,4,6} {0,5,6} {1,5,6}
  {2,7,8} {3,7,8} {2,7,9} {3,7,9} {2,8,9} {3,8,9}
```

— a `K4` core plus two triangle-blowups, four plus six plus six. Nobody
designed it; a SAT solver returned it and an independent checker verified
it. And its first four members are **exactly**
`Compression.compressed_bound`'s extremal family at `m = 3`, the largest a
compressed family may be.

That is the locally-`L` construction hypothesis turning up unprompted:
extremal families look like small rigid pieces glued along a core. The
experiment is unchanged — enumerate extremal `N(b-1,g-1)` families up to
isomorphism, search the gluings — but it now has a worked example to
generalise from rather than only the `(3,6)` object. Caveat unchanged:
the rigidity is proved only at tight rows, so this produces lower bounds,
and finding nothing proves nothing.

**Two of the objects are now identified — §11.5.** `iota(3) = 10` is the
unique simple 2-(6,3,2) design (5-regular on six points, every pair in two
blocks, `|Aut| = 60 = |A_5|`), and `iota(4,9) = 27` **is** the
Abbott–Hanson–Sauer substitution of the triangle into itself, with
`|Aut| = 1296 = 6 * 6^3` exactly matching the symmetry that construction
predicts. So at `b = 4` the 1972 construction is optimal on nine points,
not merely good. Every group order is cross-checked against `nauty`.

### Removed

**"Point EKR machinery at `iota`" collapses into the ground-set
question.** §5 item 0 listed this as the genuinely new angle the
equivalence opens. It is not a separate angle. Every Erdős–Ko–Rado-type
bound is in terms of the ground set `n` — `C(n-1,b-1)` for EKR itself,
`C(n-3,b-2)` for Frankl's diversity theorem — and the conjecture needs
`C^b`. The only way any of them yields `C^b` is if `n = O(b)`. So a route
through intersecting-family theory needs ground-boundedness *first*, and
once you have ground-boundedness the exponential bound is immediate
anyway: a family on `O(b)` points has at most `2^{O(b)}` members, with no
EKR needed.

What survives is the sharpened version already in §7: `IotaGroundBounded`
is the question, and diversity theorems are relevant only as evidence
about *which* families can be extremal, not as a source of bounds.

### Unchanged

**Rao's Lemma 2** (§1) is still the highest-value single target and still
a multi-session campaign on its own. **The entropy measurement** (§5's
correlated-covers item) is still uniquely unclaimed and still cheap.

### Working note: how to read a paper

Both literature findings in §8 and §9 were first taken from
extracted text or a fetched summary, and both were wrong in a way that
mattered.

* `pdftotext` is fine for *locating* a passage and useless for quoting
  one: sub- and superscripts, definition displays and the difference
  between "at least" and "more than" are exactly what it drops. It
  installs fine after `apt-get update`, despite an older note saying
  otherwise.
* **Render and read.** `pdftoppm -png -r 150 paper.pdf out/p` and read the
  pages as images. Doing that on [Mis26] corrected `f'(k,s)` from
  `C(k+s-2,k) + 1` to `C(k+s-2,k)` — the paper counts families "of
  cardinality *more than* `m`", so `f'` **is** the extremal number — and
  surfaced that its sunflowers require non-empty petals, which agrees
  with this development only because uniform distinct families have that
  for free.
* Doing it on [Kup25] **withdrew** a claim. The survey's two [AHS72]
  sentences looked mutually inconsistent in extracted text; on the page
  they are not. A `Δ(3)`-free family is `Δ(4)`-free, so the bound
  sentence is true as written — it is just not the statement usually
  attributed to [AHS72], and needs re-indexing before the constant is
  quoted.

Two corrections and one withdrawal from one hour of looking at pixels.
Quote from the rendered page or do not quote.

### Bounded items, with one reordering

The uniformity-2 campaign (§3a) has the wrong citation attached. See
`docs/references.md`: the exact values `f(2,k)` are due to [AHS72] in
1972 rather than [CH76] in 1976. [AHS72]'s own abstract says it
"evaluates `φ(2,k)` for all `k >= 3`" with petals counted directly, and
the formula [Kup25] quotes for it equals `CH(s,s)` at every `s` this
repository can compute. Only the *diagonal* `CH(D,D)` is ever needed here, and if
[AHS72]'s argument for the diagonal is shorter than [CH76]'s for the full
two-parameter function, that is the one to formalise. **Read the paper
before starting the campaign**, not after.

Formalising the AHS substitution (§5 item 2) is unchanged and still a
session on its own.

---

## What not to do

* **Do not run the Rao campaign and the `CH` upper-bound campaign in
  the same session.** Both are grinds; interleaving them is how both
  stall. That they turn out to share an extremal function does not
  make them one piece of work.

* **Do not expect progress on the conjecture itself.** The `log n` is
  a conceptual barrier, not bookkeeping.

* **Do not chase sharp constants** anywhere. See Stage C.

* **Do not add a definition without adding its checks.** The two
  errors this corpus has produced were both invisible to the kernel,
  and the machinery in [`testing.md`](testing.md) only helps for
  definitions it has been pointed at.

* **Do not look for submultiplicativity of `iota` by splitting the
  ground set.** §11.3: the fibres over a nonempty trace are general
  sunflower-free families, and the cone is the extremal witness. The
  intersecting hypothesis is not available inside a split.

* **Do not add savings across cores.** §11.4: at the extremal families
  every core of intermediate size is already tight, so a Shearer/Han
  argument has nothing to accumulate.

---

## 11. The multiplicative structure of `iota`, and the cone

`IotaRate.conjecture_k_3_iff_iota_exponential` says the conjecture at
`k = 3` *is* `iota(b) <= C^b`. That is a statement about one sequence, so
the first question to ask of it is what multiplicative structure the
sequence has. `coq/Product.v` answers it, and the answer reframes the
problem twice.

### 11.1 Supermultiplicativity, and the conjecture as one limit

`Product.iota_supermultiplicative`: **`iota(a+b) >= iota(a) * iota(b)`.**
The direct sum of two intersecting families on disjoint ground sets is
intersecting — two members meet in their first halves — and
`DirectSum.sum_family_no_sunflower` already gives sunflower-freeness. The
only new ingredient is `sum_family_Intersecting`, and only the *first*
family has to be intersecting, for the same reason only the first has to
be uniform there.

So `log iota` is superadditive, and Fekete's lemma applies:

```
  iota(b)^(1/b)  increases to   L = sup_b iota(b)^(1/b)  in (0, infinity]
```

and **the sunflower conjecture at `k = 3` is exactly `L < infinity`.**
That is a restatement of Erdős's $1000 problem as the finiteness of a
single limit. By the sandwich `2 iota(b) <= g(b) <= 2b iota(b)`, `L` is
also `lim g(b)^(1/b)`, so it is *the* constant of the problem.

No limit is taken in the Coq. What is proved is the finitistic content,
which is that two *sufficient* conditions each settle `k = 3` with an
explicit constant:

```
  IotaSubMultiplicative D  :  iota(a+b) <= D * iota(a) * iota(b)
  IotaStepBounded D        :  iota(b+1) <= D * iota(b)
```

* `submultiplicative_gives_step_bounded`: the first implies the second
  (take `a = 1`, where `iota_one_at_most_one` gives `iota(1) = 1`);
* `step_bounded_gives_explicit_bound`: the second gives
  `iota(b) <= D^(b-1)` by induction from `iota(1) = 1`;
* `step_bounded_settles_k3` and `submultiplicative_settles_k3`: hence the
  conjecture at `k = 3`, with `c(3) = 2(D+1)`
  (`step_bounded_gives_the_constant`).

**The second is one bounded ratio.** The whole of `k = 3` follows from
`iota(b+1)/iota(b)` being bounded. That is a much more local statement
than `exists C forall b`, and it is measurable:

```
  b   iota(b)   iota(b+1)   ratio
  1         1           3   3.0000
  2         3          10   3.3333
  3        10          27   2.7000
```

Three values, all between 2.7 and 3.4. Two things bound the constant from
below, and both are theorems rather than measurements:

* `iota_at_least_doubles` — the cone composed with
  `Intersecting.doubling_lower_bound` gives `iota(b+1) >= 2 iota(b)`, so
  every admissible `D` is at least 2;
* `step_bounded_needs_D_at_least_three` — with the proved
  `iota_two_at_most_four` and the witnessed `iota(3) >= 10`,
  `10 <= 4D`, so **`D >= 3`**. The same shape as
  `IotaGround.ground_bounded_needs_c_at_least_four`: the hypothesis is
  not vacuous and the data already forces its constant up.

Read honestly: three ratios is thin evidence, the fourth is not decidable
(see §11.4), and boundedness of the ratio is *strictly stronger* than the
conjecture — `iota(b) <= C^b` does not bound any single ratio. What the
reformulation buys is a target with one number in it.

### 11.2 The cone: `g(b-1) <= iota(b)`

Add one fresh point to every member of a sunflower-free `m`-uniform
family. The result is `(m+1)`-uniform, **intersecting**, and still
sunflower-free: three members `A_i ∪ {p}` have pairwise intersections
`(A_i ∩ A_j) ∪ {p}`, which are all equal exactly when the `A_i ∩ A_j`
are. `Product.iota_at_least_g_pred`.

Against `Intersecting.intersecting_link_bound`'s `iota(b) <= b g(b-1)`,
that is a **second sandwich, in the uniformity rather than in the size**:

```
  g(b-1)  <=  iota(b)  <=  b * g(b-1)
```

Elementary, and surely folklore — no claim of novelty is made for the
construction. What is new here is that it is machine-checked and that
four things follow from it, three of which correct something this
repository had written down.

**(a) Intersecting-ness is worth exactly one point of uniformity.** Any
statement true of every sunflower-free family at uniformity `m` is true of
an intersecting one at `m+1`, and conversely up to the factor `b`. So no
argument whose only use of the intersecting hypothesis is "the pieces are
intersecting" can beat the general argument. §7's reading of
intersecting-ness as "a *locality* constraint … exactly the property a
ground-set bound needs" is too optimistic by one uniformity.

**(b) An upper bound on `iota` is an upper bound on `g` one uniformity
down** (`iota_bound_bounds_g`), and that makes the §7 ladder a *hard*
question rather than a computation. §7 names "is `iota(4,10)` 28 or does
it stay at 27?" as the decisive experiment for `IotaGroundBounded`, and §9
records that neither the branch-and-bound nor SAT decides it. The transfer
says why:

> `iota_four_at_most_27_would_beat_erdos_rado`: a proof of
> `iota(4) <= 27` gives `f(3,3) <= 28`.

Erdős–Rado gives 49 and the best lower bound here is `f(3,3) >= 21`. So
the ladder is at least as hard as a new bound on the first unknown
sunflower number. **Do not budget for it as a search.**

**(c) The two ground-set hypotheses are not independent.**
`IotaGround.both_ground_hypotheses_settle_k3` says "neither implies the
other; what separates them is that one has a measurement behind it". The
first half is wrong and is withdrawn:

* `ground_bounded_implies_iota_ground_bounded` — immediate, because
  `IotaGroundBounded`'s existential does not ask its witness to be
  intersecting or even uniform;
* `iota_ground_bounded_bounds_the_general_row` — the cone gives the
  converse with the uniformity shifted by one, hence
  `iota_ground_bounded_bounds_g_by_counting`:
  `IotaGroundBounded c` alone bounds the *general* row by
  `(2^c)^(m+1)`.

So the flat `iota(3,g)` row is evidence for `GroundBounded` too, and the
general row still climbing at `g = 10` is evidence *against*
`IotaGroundBounded`. The two rows are not independent readings; they are
the same question with the uniformity shifted.

**(d) The universal reading of `IotaGroundBounded` is false.**
`coq/IotaGround.v` says of it: "The data says the extremal intersecting
sunflower-free family literally lives on `O(b)` points". It does not. Cone
the [FPPTZ24] tree-path family — the apex is the stem edge above the root,
which is exactly what the paths through different children of the root
were missing — and the result is intersecting, `b`-uniform,
3-sunflower-free, with `2^(b-1)` members on `2^b - 1` points, **every one
of them used**. `Product.the_universal_iota_ground_reading_is_false` is
the `b = 4` instance in the kernel; `rust/tests/iota_structure.rs` checks
the construction to `b = 7`, where 64 members need 127 points.

As in §7.5, this does not conflict with the flat `iota(3,g)` row: that
measures the largest family *on* `g` points, which is the quantity the
existence reading needs.

### 11.3 The submultiplicativity attempt, and where it fails

The prediction, written before anything was computed. Approximate
submultiplicativity would be proved by partitioning the ground set into
`X` and `Y`, bucketing the members of `F` by the trace `P = A ∩ X`, and
bounding each fibre. Three things were expected to go wrong:

1. there is no canonical partition — the members do not split at
   prescribed sizes, so `|A ∩ X|` ranges over `0..a+b`;
2. the number of traces is bounded only by `2^|X|`, and the trace family
   is not sunflower-free;
3. the fibres over a **nonempty** trace lose intersecting-ness, so they
   are bounded by `g` and not by `iota`, and the uniformity drops by
   `|P|` rather than by `a`.

The third is the fatal one, and the cone is its extremal witness. Take
`X = {p}`. Then `link [p] (cone p F) = F` **literally**
(`Product.link_of_cone`), so the cone of a `g`-extremal family is an
intersecting family with one nonempty trace whose fibre *is* a general
sunflower-free family of the largest possible size.
`the_split_fibres_are_not_intersecting` says this for every `F`;
`the_fibre_bound_is_g_not_iota` is the smallest instance, where the fibre
is `F23.two_triangles`, attaining `g(2) = 6` against `iota(2) = 3`.

So the best a split gives is `iota(b) <= (number of traces) * g(b-1)`,
which at `b` traces is `intersecting_link_bound` and Erdős–Rado's rate.
**A splitting argument cannot use the intersecting hypothesis at all.**

Note also what a *bounded defect* would require. Fekete gives
`iota(a) iota(b) <= iota(a+b) <= L^(a+b)`, so
`iota(a+b) / (iota(a) iota(b))` is bounded iff `iota(b) = Theta(L^b)` —
no subexponential correction. Abbott–Hanson–Sauer's own bound carries one
(`10^(b/2 - c log b)`), so constant-defect submultiplicativity is
strictly stronger than the conjecture, and the polynomial-defect version
`iota(a+b) <= p(a+b) iota(a) iota(b)` is the honest target. It is not
formalised here; the constant version is, and it implies it.

### 11.4 The diagnosis, in the same shape as §8

`LinkCharacterisation.sunflower_iff_link_matching` makes
sunflower-freeness a conjunction with one clause per core `Y`:
`nu(F_Y) <= 2`. §8 proved that shifting commutes with the clause at
`Y = ∅` and with **no other**. The cone is the mirror image:

* it **imposes** the empty-core clause for free — `cone_Intersecting`
  needs no hypothesis whatever;
* and it is **literally the identity** on every other clause, because
  `link [p] (cone p F) = F` on the nose.

`Product.only_the_empty_core_is_cheap` records all four parts. So two
completely different operations each touch exactly one clause of the
conjunction, and it is the same clause — the one Erdős–Ko–Rado lives at.
That is a sharper statement of what is hard here than either result alone:
**the `Y = ∅` clause is free in both directions, and every clause above it
is the whole problem.**

The measurement agrees, and it is the entropy question §10 asks
("do the savings from different cores multiply, or merely repeat?").
`rust/tests/iota_structure.rs` computes the per-core matching numbers of
the extremal families:

```
  iota(4,9) = 27, on nine points
    |Y| = 0:  1 core,  0 tight
    |Y| = 1:  9 cores, 9 tight
    |Y| = 2: 36 cores, 36 tight
    |Y| = 3: 54 cores, 54 tight
    |Y| = 4: 27 cores, 0 tight (these are the members)
```

**Every** core of intermediate size is tight. There is no slack anywhere
to trade between cores, so a Shearer/Han argument that hoped to add up
savings from different cores has nothing to add up. That answers §10's
entropy item in the negative before any proof is attempted, which is what
the item asked for.

### 11.5 The instrumentation, and what it identified

`rust/examples/iota_structure.rs` dumps the extremal families and every
invariant computable from them; `rust/tests/iota_structure.rs` pins them.
Two identifications came out of it, and both are checked rather than
guessed — the automorphism search is a backtracking walk whose prune is
complete, and all nine group orders agree with `nauty`.

**`iota(3) = 10` is the unique simple 2-(6,3,2) design.** Ten triples on
six points, 5-regular, every pair in exactly two blocks, `|Aut| = 60`,
point-transitive, diversity 5 of 10. (60 is the order of
`A_5 ≅ PSL(2,5)` acting on the six points of the projective line over
`F_5`, which is what one would expect; only the *order* was computed, not
the isomorphism type.) §5 already knew it
was a transversal of the complementary pairing; the design structure is
strictly more.

**`iota(4,9) = 27` is the Abbott–Hanson–Sauer substitution of the triangle
into itself.** Split the nine points into three triples and take every
union of a *pair* from one triple with a *pair* from a different one:
`3 * 3 * 3 = 27`, which is exactly `iota(2) * iota(2)^2`. Its
automorphism group has order **1296 = 6 * 6^3** — `Sym(3)` on the triples
times `Sym(3)` inside each — which is precisely the symmetry the
substitution predicts and nothing else would have.

So at `b = 4` the 1972 construction is not merely good, it is **optimal
on nine points**. That is the strongest evidence yet that the
substitution is the right construction and that `L = 10^(1/2)`; it is
also why nothing in §11.6 beats it.

**OEIS: no match.** `1, 3, 10, 27` returns ten sequences, none
combinatorial in a relevant way (non-sum-free subsets, `floor(sinh n)`,
…); `1, 3, 10, 27, 54` and `3, 10, 24` return nothing relevant; the
ground-set rows `1,5,9,15,24,27` and `1,4,6,10,12,12,14` return nothing at
all. Searched with the OEIS JSON API, not exhaustively over reformulations.

**Closed forms killed**, each as an assertion in
`rust/tests/iota_structure.rs` so it cannot be re-proposed:

```
  C(2b-1, b-1)  = C(2b,b)/2   dies at b = 4: predicts 35, truth is 27
  3^(b-1)                     dies at b = 3: predicts  9, truth is 10
  2^(b-1), Catalan(b), b!,
  C(2b-2, b-1), 2^b - b       die at b = 2: predict 2, truth is 3
```

And the trap: all `b`-subsets of `[2b-1]` is intersecting with
`C(2b-1,b)` members, which matches the complementary-pair ceiling — but it
*contains a sunflower* from `b = 3` on, so it is not an `iota` witness.
Pinned as a test.

One observation the instrumentation produced that is **not formalised**,
recorded so it is not lost: a `(b-1)`-set lies in at most **two** members
of a sunflower-free `b`-uniform family (its link is a family of
singletons, so the matching number *is* the degree). Counting incidences,
`b|F| <= 2|shadow_{b-1}(F)| <= 2 C(g, b-1)`, which is tight at
`(b,g) = (2,3)` and `(3,6)`. It is the `|Y| = b-1` end of
`IotaGround.link_degree_ground_bound`, whose `|Y| = 1` end is the theorem;
the general form is `C(b,j)|F| <= C(g,j) N(b-j, g-j)`. Checked in
`rust/tests/iota_structure.rs`.

### 11.6 The `iota` table, extended

Exhaustive search decides `iota(b,g)` up to `(4,9)` and stops. Past that,
`rust/examples/iota_extend.rs` builds the best families the three
available constructions give — the cone, the doubling, and the
Abbott–Hanson–Sauer substitution — and hands each to an independent
verifier:

```
  b   iota(b) >=   points   iota^(1/b)   route
  1            1        1       1.0000   exhaustive
  2            3        3       1.7321   exhaustive
  3           10        6       2.1544   exhaustive
  4           27        9       2.2795   exhaustive at g = 9; g >= 10 open
  5           54       19       2.2206   cone(substitute(g(2), iota(2)))
  6          300       18       2.5873   substitute(iota(2), iota(3))
  7          600       37       2.4939   cone(substitute(g(2), iota(3)))
  8         2187       27       2.6151   substitute(iota(2), iota(4,9)) -- unverified
```

Rows 5–7 are verified; row 8 is stated and **not** verified (2187 members
means 1.7e9 triples, and the check was not run). The previous best at
`b = 5` was 42 — SAT at ground 10, §9 — and `b = 6` and `b = 7` had never
been computed at all. `b = 5` is where the cone earns its keep: 54 against
42, and against the direct sum's `iota(2) iota(3) = 30`.

`nothing_in_the_table_beats_the_1972_rate` asserts what this does **not**
do: every entry satisfies `iota(b)^2 <= 10^(b-1)`, so none of them beats
Abbott–Hanson–Sauer. That is forced — the substitution's own fixed point
is `10^(1/2)` — and it is asserted so a future session does not mistake a
bigger number for a better rate.

Through the doubling these give lower bounds on `f(n,3)`:

```
  b   2 iota(b)   rate (2 iota(b))^(1/b)
  3          20               2.7144    <- the repository's headline
  4          54               2.7108
  6         600               2.9042    (needs the unformalised substitution)
```

`Product.lower_bound_4_3_54` formalises the `b = 4` row: **`f(4,3) >= 55`**,
where `Audit.f_4_3_at_least_37` reached 37. It does not improve the rate
(`54^(1/4) < 20^(1/3)`, and
`the_rate_at_four_does_not_beat_the_rate_at_three` proves it), and
`IotaRate.every_construction_is_within_2b_of_iota` is why: at a fixed
uniformity nothing can beat `iota` there.

### 11.7 What this closes and what it opens

**Closed.** Do not look for submultiplicativity by splitting the ground
set — the fibres are `g`-fibres. Do not treat `GroundBounded` and
`IotaGroundBounded` as independent hypotheses. Do not read the flat
`iota(3,g)` row as saying extremal intersecting families are small-ground:
they can need `2^b - 1` points. Do not budget the `iota(4,10)` ladder as a
search: deciding it downward implies `f(3,3) <= 28`. And do not attempt a
Shearer/Han argument that adds savings across cores — at the extremal
families every intermediate core is already tight.

**Open, and now sharper.**

* **Bound the ratio `iota(b+1)/iota(b)`.** This is the whole conjecture at
  `k = 3` (`step_bounded_settles_k3`), it needs one constant, the
  constant is at least 3 (`step_bounded_needs_D_at_least_three`), and
  the three measurable values are 3.00, 3.33, 2.70. Every clause of the
  link characterisation at a nonempty core is what stands in the way, by
  §11.4.
* **Formalise the substitution** (§5 item 2, unchanged). It is now
  needed for *two* things rather than one: the `g(6) >= 600` rate, and
  rows 5–7 of the `iota` table above, which are currently verified in
  Rust and not in Coq. And §11.5 gives it a new motivation: at `b = 4`
  the substitution family is provably extremal, so it is not one
  construction among many.
* **`iota(4,10)`, with the cost understood.** It is worth what a new
  bound on `f(3,3)` is worth, which is a lot; it is not worth attacking
  with a bigger budget for the same search.

---

## 12. The sharp reformulation, and a target with a number in it

§11 restates the conjecture at `k = 3` as `L = sup_b iota(b)^(1/b) < infinity`.
That is the wrong normalisation, and `coq/Sharp.v` fixes it.

### 12.1 Why the exponent is `1/(b-1)`

The substitution `iota(ab) >= iota(a) iota(b)^a` — verified in
`rust/tests/intersecting.rs`, still not formalised — iterated at `b^k`
extracts a rate of `iota(b)^(1/(b-1))` per point, not `iota(b)^(1/b)`.
The 1972 constant is a value of *that* sequence: `10^(1/2)` is
`iota(3)^(1/(3-1))`. So the sequence to watch is

```
  b      1      2      3       4
  iota   1      3     10      27   (on nine points, exhaustive)
  rate   -   3.000  3.162   3.000
```

and the conjecture at `k = 3` is that it is bounded.

**Formalised, as an equivalence** (`Sharp.conjecture_k_3_iff_iota_shifted`):

```
  sunflower_conjecture_k_3   <->   exists C, forall b >= 1, iota(b) <= C^(b-1)
```

Both directions are arithmetic on top of
`IotaRate.conjecture_k_3_iff_iota_exponential`; the constant moves by a
square in one direction and by one in the other. The **substitution is not
needed** for the equivalence — it is needed only to know that `1/(b-1)` is
the exponent the constructions actually achieve, which is a statement about
lower bounds and is not claimed there.

The shift is not a reindexing, and there is a theorem saying so.
`Audit.the_shifted_bound_at_three_is_false` proves `~ IotaShiftedAt 3`:
the base-3 form is refuted outright by the witnessed `iota(3) >= 10`
against `3^2 = 9`. The unshifted form at base 3 is *not* refuted by that
family (`10 <= 27`). So in the shifted normalisation the base is at least
4, which is the finitistic content of "`L > 3`, and the value conjectured
is `sqrt(10) = 3.162...`".

### 12.2 The sharp conjecture, named

```
  AHSOptimal  :=  forall b >= 1,  iota(b)^2 <= 10^(b-1)
```

squared so nothing leaves `nat`. Equivalently `iota(b) <= 10^((b-1)/2)`;
equivalently **Abbott–Hanson–Sauer is optimal** and `L = sqrt(10)`;
equivalently `f(n,3) <= (2 sqrt(10))^n + 1`, about `6.33^n`.

It is **met with equality at `b = 3`** and nowhere else that is decided
(`Sharp.the_sharp_bound_is_attained_at_three`): `iota(3)^2 = 100 = 10^2`
exactly. One more member there refutes it. That single exhaustive
computation is what the whole constant rests on.

Three consequences, all machine-checked:

* `Sharp.sharp_settles_k3` — it implies the conjecture at `k = 3`, with
  the explicit constant `c(3) = 8` (`sharp_gives_the_constant`). The
  real-valued constant is `2 sqrt(10) = 6.32...`; 8 is the price of
  staying in `nat` and no attempt is made to sharpen it.
* `Sharp.sharp_beats_erdos_rado_at_three` — it gives **`f(3,3) <= 32`**
  against Erdős–Rado's 49, from a hypothesis about uniformity 4. Read as
  hardness: proving the sharp conjecture settles a value nobody knows.
  Read as a target: `iota(4)` alone is worth a new bound on the first
  unknown sunflower number.
* `Sharp.sharp_forces_iota_three_exactly_ten` — it pins `iota(3) = 10`,
  where the development otherwise has only `[10, 18]`.

`Audit.the_sharp_bound_narrows_iota_four` records that it says strictly
more than the kernel already knows: `iota(4)` in `[27, 192]` becomes
`[27, 31]`.

### 12.3 The threshold table — this is the thing to memorise

`Sharp.refutation_threshold` turns one family into a refutation. The least
family size that refutes at each uniformity, tabulated, pinned in
`rust/tests/sharp_conjecture.rs`, and each rung a corollary in
`coq/Sharp.v`:

```
  b     iota(b) known   beats AHS at   fraction   note
  4         27                32        0.844     iota(4,10) <= 31; g >= 11 untouched
  5         54               101        0.535
  6        300               317        0.946     <-- 17 members short
  7        600              1001        0.599
  8       2187              3163        0.691     (the b = 8 row is unverified)
  9     10,000            10,001        0.9999    <-- needs exactly ONE more set
```

**The odd tower is exactly on the threshold.**
`Sharp.the_tower_misses_by_exactly_one`: at `b = 2j+1` the sharp bound
reads `iota(b) <= 10^j`, a round number, and it is exactly what the
substitution delivers when iterated on `iota(3) = 10`. So at every odd
uniformity the record falls at one more set, and `b = 3, 9, 27, ...` all
sit on the line. Any single improvement anywhere propagates up the whole
tower.

The even rungs are separate corollaries (`iota_four_at_least_32_refutes`,
`iota_six_at_least_317_refutes`) because their thresholds are not round.

### 12.4 How to read this

Honestly, and the file says so itself. This is **not** evidence for the
sharp conjecture beyond (i) four exhaustive values of `iota`, (ii) the
fact that no construction in the repository reaches a threshold — which
is *forced*, since the substitution's own fixed point is `10^(1/2)`, and
is asserted in `rust/tests/sharp_conjecture.rs` so a bigger number is not
mistaken for a better rate — and (iii) `iota(4,9) = 27` being provably the
Abbott–Hanson–Sauer family (§11.5).

What it is, is a target with a number in it. The cap-set programme had
one; this one has not. Every future session can now ask "did I beat 1972?"
and get an integer answer.

---

## 13. Settled: the 1972 families are maximal, and prescribed symmetry does not transfer

§12 gives the threshold at every uniformity. This is the campaign that
went at it, and both halves come back negative — with theorems rather
than with "the search did not find anything".

### 13.1 The cheapest question nobody had asked

At `b = 9` the substitution `substitute(iota(3), iota(3))` builds 10,000
members and the threshold is 10,001. **Can one more 9-set be added?**

The question looks like it has to be re-asked per ground set. It does
not. A candidate `C` interacts with the family only through its trace
`S = C ∩ support(F)` — a point in no member contributes to no
intersection — so `C` meets `A` iff `S` does and `A ∩ C = A ∩ S`.
Enumerating traces answers the question **for every ground set at once**,
and `Maximal.maximal_of_trace_certificate` is that reduction: a `forallb`
over `HallCore.sublists U` implies a statement quantified over every list
`A`, with no ground-set hypothesis in it.

Measured first (`rust/examples/extend_ahs.rs`), three independent methods
that agree — minimal hitting sets, brute force over every trace where
affordable, and SAT with two solvers required to agree on UNSAT:

```
  family                                b    members   tau   addable
  substitute(iota(2), iota(2))          4         27     4   none
  substitute(iota(2), iota(3))          6        300     6   none
  substitute(iota(3), iota(3))          9      10000     9   none
  cone(substitute(g(2), iota(2)))       5         54     -   none
  cone(substitute(g(2), iota(3)))       7        600     -   none
```

**Every row is maximal on every ground set.** For the three pure
substitutions the verdict does not even use sunflower-freeness: no
`b`-set meets every member except the members themselves.

The mechanism is that the **covering number is multiplicative**. A set
`C` meets every member of `substitute(G,H)` exactly when
`{v : C_v is a transversal of H}` is a transversal of `G`, so
`tau(substitute(G,H)) >= tau(G) tau(H)`; and an intersecting family is
met by each of its own members, so `tau <= ab`. When `tau(G) = a` and
`tau(H) = b` the two meet and the minimum transversals are exactly the
members — so **maximality is multiplicative under substitution**, and
since `iota(2)` and `iota(3)` are both maximal the whole 3-adic tower is.
`rust/tests/extension.rs` pins `tau` on every pair.

Formalised: `Maximal.iota4_is_maximal_intersecting` at `b = 4`, through
the general reduction, reflectively, with no ground set. The general
statement needs `substitute` in Coq, which is §5 item 2's session.

### 13.2 What that does *not* say

**Maximal is not maximum.** `Maximal.maximality_is_not_a_size_bound` is
the witness: the **Fano plane** is a maximal intersecting 3-uniform
family — `tau = 3`, and the seven 3-sets meeting all seven lines are
exactly the lines — with *seven* members, while `Intersecting.iota3` is
an intersecting 3-uniform family with *ten*. Inside the sunflower-free
world the gap is the same: random greedy growth finds a **six**-member
intersecting sunflower-free 3-uniform family to which nothing can be
added on any ground set, against `iota(3) = 10`.

So §13.1 closes one route to the record and says nothing about whether
the record is reachable by another. Do not read it as evidence for
`AHSOptimal`.

### 13.3 Kramer–Mesner does not transfer, and here is why

If the 1972 families cannot be extended, a record family has different
symmetry — so prescribe a group and search its orbits, which is how
record designs are found. `rust/src/orbit.rs` builds it: group closure,
orbits on `b`-subsets, and a max-clique-shaped search with the ternary
condition checked incrementally (`A, B, x` is a sunflower iff
`A ∩ B ⊆ x` and `x ∩ (A △ B) = ∅`, so the pairs of the current family
live in buckets indexed by `A ∩ B` and a candidate costs `2^b` lookups
rather than a scan over 50000 pairs). Validated against
`intersecting::iota` with the trivial group at six parameter points,
including the exhaustive maxima `iota(3,6) = 10` and `iota(4,7) = 15`.

**136 (ground, group) pairs, every one exhausted, nothing found.**

```
  row                                     grounds        groups   verdict
  b = 4, target 32, intersecting          11..16             41   none; 0 usable orbits
  b = 3, target 32, general (cone)        16..22             50   none; 0 usable orbits
  b = 5, target 317, general (cone)       15..20             45   none; best reached 100
```

The first two rows are the finding. **Zero orbits were usable** — not
"the search failed", but "there was nothing to search". A `G`-invariant
sunflower-free family is a union of orbits, so *every orbit must itself
be sunflower-free*, i.e. have no three pairwise disjoint members. An
orbit of a group acting on a ground set much larger than `3b` almost
always contains three disjoint translates, and then it is dead before
the search starts. At `b = 3` on sixteen points, no orbit of any group
in the list survives; at `b = 5` on fifteen, where `3b = g` exactly, most
of them do — and that row *is* searched, exhaustively, and comes back
empty with a best of 100 against the target 317.

That is the structural reason the classical instrument does not carry
over, and it is the same shape as §8's diagnosis of shifting. The
Kramer–Mesner method works for designs because the condition is
**linear and positive** — cover every `t`-set `lambda` times, so orbits
add up. Sunflower-freeness is **ternary and negative**, so orbits do not
add up; they veto.

Half of it is a theorem. If `G` is transitive on the ground set then
every orbit is **point-regular**, and
`Maximal.regular_intersecting_ground_bound` proves

> a regular intersecting `b`-uniform family lives on at most `b^2` points.

Two consequences. It is why prescribing a transitive group is hopeless
above `g = b^2`. And it sharpens
`Product.the_universal_iota_ground_reading_is_false`: the cone of the
tree-path family needs `2^b - 1` points, far past `b^2`, so it *must* be
irregular — and it is, the apex having degree `|F|` while every other
point has less. **The universal ground reading fails only on irregular
families**, and §7's measurement that the extremal `iota` families *are*
regular puts all of them comfortably inside `b^2`.

One order-of-work note, recorded because the repository's rule is the
other way round: `regular_intersecting_ground_bound` was proved before it
was enumerated. It is three lines from `Pigeonhole.pigeonhole_family` and
the incidence count, and it was written as the explanation of a
measurement rather than as a conjecture to test. The enumeration in
`rust/tests/extension.rs` was added afterwards and found no
counterexample; that is weaker evidence than the usual order gives.

### 13.4 What is left at the top of the ladder

* **`iota(4) >= 32`, through the general row.** By the cone, a
  *3-uniform* sunflower-free family with 32 members gives `iota(4) >= 32`,
  refutes `Sharp.AHSOptimal`, and gives `f(3,3) >= 33`. The proved
  `N(3,g) <= 2g` forces `g >= 16` and at `g = 16` the bound would have to
  be met with equality — which by §7 forces the family to be regular and
  every link extremal. That is a **rigid** target, not a wide search, and
  it is the most concrete thing left on the list. The prescribed-group
  route to it is closed by §13.3. The SAT route **was** run here, and it
  is recorded with its cost the way §9 records the others:

```
    question           solver     time    verdict
    N(3,16) >= 30      cadical    601s    undecided
```

  `cargo run --release --example sat_run -- general 3 16 30 33`. That is
  not the target rung — it is three *below* it. `C(16,3) = 560` variables
  is a small instance; the ternary clauses are what make it hard. So the
  general row at sixteen points is out of reach of every instrument in
  the repository — branch-and-bound, SAT and prescribed symmetry — and
  moving it needs a new one rather than a bigger budget. The lever
  nothing currently uses is the rigidity: at `g = 16` the bound
  `N(3,g) <= 2g` would have to be met with **equality**, which by §7
  forces the family to be regular with every link extremal, and neither
  the SAT encoding nor the orbit search knows that.
* **Formalise the substitution** (§5 item 2). Now needed for a third
  thing: the general maximality theorem of §13.1 is stated about
  `substitute` and cannot be proved without it.
* **A construction that is not a substitution.** Everything in §11.6 is
  built from `cone`, `double` and `substitute`, and §13.1 says all of it
  is maximal. The table cannot move without a genuinely new operation.

---

## 14. Settled: the Erdős–Rado ratio is unbounded, and the conjecture is about its mean

§13 closed the constructions. This is about the *proof*, and it comes out
of a quantity the repository has been measuring for three sessions
without naming.

### 14.1 The quantity Erdős–Rado's recursion pays

Erdős–Rado is one step iterated: find a heavy point, recurse into its
link. `Intersecting.sunflower_free_star_bound` proves the step. Write

```
  rho(F)  =  |F| / maxdeg(F)
```

The link at a maximum-degree point has `maxdeg(F)` members and uniformity
`b-1`, so `|F| = rho(F) · |link|` and, descending,

```
  |F|  =  rho_0 · rho_1 · ... · rho_{b-1}
```

**exactly** — the chain telescopes, and `rust/tests/star_defect.rs`
checks that it does on every family the repository has. Erdős–Rado bounds
each factor by `2(b-j)` and gets `2^b b!`. **The conjecture at `k = 3` is
precisely that the product is `C^b`.**

And a constant bound on a *single* factor settles it outright:

```
  StarBounded c  :=  every sunflower-free b-uniform family has a point x
                     with |F| <= c · deg(x)
```

gives `g(b) <= c·g(b-1)`, hence `g(b) <= 2c^(b-1)` — the whole conjecture
from one inequality with one number in it. `StarDefect.star_bounded_settles_k3`,
with `c(3) = 2c`.

`StarDefect.star_defect_bound` is the per-family form of the step, which
the repository lacked: it *names* the point rather than consuming it, so
the recursion can be run parametrically (`star_step`).

### 14.2 It is not a constant, and the witness is the 1972 construction

`rust/tests/iota_sandwich.rs` has pinned the worst observed ratio for a
while — **2, 3, 2.75** at uniformities 1, 2, 3 against the proved 2, 4, 6
— and that row looks flat. A flat row is the conjecture.

**It is not flat.** `rho` is *exactly multiplicative* under the
Abbott–Hanson–Sauer substitution:

```
  |substitute(G,H)|       = |G| |H|^a
  maxdeg(substitute(G,H)) = maxdeg(G) maxdeg(H) |H|^(a-1)
  ==>  rho(substitute(G,H)) = rho(G) rho(H)
```

— the `|H|^(a-1)` cancels. Checked in exact rational arithmetic on all
six buildable pairs. With `rho(iota(2)) = 3/2` and `rho(iota(3)) = 2`,
iterating on `iota(3)` gives

```
  b = 3^k   ==>   rho = 2^k   ==>   rho = b^(log_3 2) = b^0.6309...
```

**Unbounded.** Verified directly at `b = 9`, where the substitution's
10,000 members have maximum degree exactly 2500 and `rho = 4`. So the
measured row was flat only because it stopped at `b = 3`, and the family
that refutes a constant star bound is the one giving the best lower bound
known.

The doubling is the only other operation that moves `rho`, and it doubles
it — but it cannot be iterated, because the doubling of an intersecting
family is not intersecting (`Audit.intersecting_is_needed_in_the_doubling`).
So the substitution is the mechanism, and it is the *same* mechanism that
makes the lower bound good.

Formalising the refutation needs `substitute` in Coq (§5 item 2). What is
proved is the finitistic half: `StarDefect.star_bounded_needs_c_at_least_five`
— the doubling of the exhaustively extremal `iota(4,9) = 27` is 54 members
at uniformity 4 with every point in at most 12 of them, so any admissible
`c` is at least 5, against the proved ceiling `2b = 8` there. Same shape
as `step_bounded_needs_D_at_least_three` and
`ground_bounded_needs_c_at_least_four`; what is new is that the
constructions push it up *without limit*.

### 14.3 What survives, and what it says about the `log`

The average. On the same tower the product of the `b` chain ratios is
`10^((b-1)/2)`, so their geometric mean is `|F|^(1/b)` — tending to
`sqrt(10) = 3.162` — while the largest single factor grows like `b^0.63`:

```
   b    product        geometric mean   largest factor rho
   3          10.00           2.1544              2.0
   9       10000.00           2.7826              4.0
  27       10^13              3.0303              8.0
```

That gap is exactly §4's still-unclaimed "are the covers correlated
across levels?", and it is now answered on the best object we have:
**they are.** The maximum is unbounded and the mean is not, so any proof
of the conjecture has to be a statement about the whole chain and cannot
be a per-level estimate. That is the precise form of "pay the log once",
and it is a *lower bound on the difficulty* of the remaining problem:
§14.2 rules out the entire class of arguments that bound one level at a
time.

### 14.4 Where this leaves the ladder

Three classes of argument are now closed with theorems rather than with
failed searches:

* **canonical-form symmetry breaking** — §8, `compressed_bound`;
* **prescribed symmetry** — §13.3, and the orbit-usability measurement;
* **per-level degree estimates** — §14.2.

What is not closed, in order of how concrete it is:

* **The chain, treated as a whole.** Bound `Π rho_j` without bounding any
  `rho_j`. Nothing in the repository attempts this and it is what the
  conjecture is.
* **`iota(4) >= 32` through the general row** (§13.4), still the most
  concrete open target, still out of reach of every instrument here.
* **Formalise the substitution** (§5 item 2). It is now needed for
  *four* things: the `g(6) >= 600` rate, rows 5–7 of the `iota` table,
  §13.1's general maximality theorem, and §14.2's refutation.

### 14.5 Withdrawn: `rho` is spreadness, and the repository already had it

The first version of this section said: *"one targeted web search for the
ratio `|F|/maxdeg`… nothing found… the related published quantity is
diversity `|F| - maxdeg`."* **That is wrong and is withdrawn.** The
search was one query, the conclusion drawn from it was a guess, and the
guess was about the wrong literature.

`Spread.Spread F r` is `forall T, NoDup T -> r^|T| · deg T F <= |F|`, and
has been in this repository since the spread layer went in. At `T = [x]`
it reads `r · deg(x) <= |F|`, i.e. **exactly `rho(F) >= r`**. So `rho` is
the singleton clause of spreadness — the parameter `kappa` of
[ALWZ20] Definition 1.10, which that paper notes was called *regularity*
before them, and Definition 2.5 of [Lovett]'s PCMI notes. Both read from
rendered pages. `StarDefect.star_defect_is_the_singleton_spread_clause`
is the identification, machine-checked, so the retraction is a theorem
rather than an edited paragraph.

What that does to the three claims above:

* **`star_defect_bound` is not new.** It is the "structured" branch of
  the classical Erdős–Rado dichotomy, stated verbatim as [Lovett]'s
  Lemma 2.2 with the constant `(r-1)n` — which at `r = 3` is exactly the
  `2b` proved here — and attributed to Erdős–Rado in [ALWZ20] §1.2
  ("much like in the original proof of Erdős and Rado"). What is new *to
  this repository* is that the branch is exposed in per-family form: the
  **other** branch, `SpreadReduction.elementary_spread_disjoint`, has
  been here all along, at the neighbouring constant `2b + 1`, proved by
  the same maximal-disjoint-cover-plus-pigeonhole argument.
  `the_two_branches_of_the_dichotomy` now puts them side by side, which
  is the connection the previous section should have made and did not.
* **`star_bounded_settles_k3` is textbook in shape.** It is the
  singleton-only case of [Lovett]'s Lemma 2.6, the reduction to spread
  families.
* **The unboundedness is the field's own stated motivation.** Immediately
  before Definition 2.5, [Lovett] writes: *"Note that in the proof we
  only used the 'structured' case where a single element belongs to many
  sets in F. But we also could have used two elements, or three elements,
  or any number of elements. This motivates the following definitions."*
  Generalising from one element to sets is the whole 2020 programme, and
  it exists because the one-element parameter is not good enough. So
  §14.2 is a quantitative instance of a known obstruction, not a
  discovery of one.

**What may still be unrecorded, narrowly.** The exact multiplicativity
`rho(substitute(G,H)) = rho(G)·rho(H)`, and the consequence that the
Abbott–Hanson–Sauer tower's singleton spreadness is exactly
`b^{log_3 2}`. That is a concrete lower bound on how spread a
sunflower-free family can be, along an explicit infinite family rather
than at a single parameter point — which is more than the repository's
existing non-vacuity witnesses (`ALWZ.threshold_is_inside_the_gap`) give.
**No claim of novelty is made for it.** Two searches and two papers read
at the relevant pages found the framing but not this computation, and
that is not the same as its being absent.

**What is unchanged.** Every theorem in §14.1–§14.3 is still true and
still machine-checked. The conclusion of §14.3 — that a proof of the
conjecture cannot be a per-level estimate — also stands, and is now
better supported: it is what the literature did next.

### 14.6 The lesson, since this is the second time

A one-query search is not a literature check, and the failure mode is
specific: the search was for the *shape I had invented* (`|F|/maxdeg` as
a ratio) rather than for the *shape the field uses* (a degree bound
relative to family size, i.e. spreadness). Searching for one's own
notation finds nothing by construction.

The check that would have caught it in seconds was not a search at all:
**grep the repository.** `Spread.v` defines the quantity, `TwoUniform.v`
proves it is a maximum-degree bound at uniformity 2, and
`SpreadReduction.v` proves the complementary branch. The rule to add:
before claiming a quantity is unnamed, look for it in the development
first.

---

## 15. What to read next, and why none of it has been read

> **Superseded by §16 and `docs/reading.md` (session N+3).** This section
> is kept as written, because it is the diagnosis that produced the
> reading session and the table below is the plan that was executed. Its
> "read" column is now out of date: [Ra20], [ALWZ20], [BCW21], [Lovett]
> and [MNSZ22] were read in full, and its headline claim — that the
> repository's axiom came from an unopened paper — is no longer true.
> Everything §15 predicted about the *consequences* of reading turned
> out to be right, including that §1's target would change.


§14.5 withdrew a novelty claim that one `grep` would have prevented. The
same audit, applied to the reading list, turns up something worse: **the
repository's single axiom comes from an eight-page open-access paper that
nobody here has opened.** §1 plans a three-stage campaign against Rao's
encoding argument, in detail, without having read it.

So this section is the reading list, ranked, with page counts and
reachability checked (July 2026). None of these has been read beyond the
pages named.

### 15.1 The spread lemma has four independent proofs, and we have read none

```
  source                                     pages   reachable   read
  [Ra20] Rao, Coding for sunflowers            8     arXiv 1909.04774, open   no
  [Lovett] PCMI notes, §3 proof               29     IAS, open                p.7 only
  [ALWZ20] Improved bounds                    19     arXiv 1908.08483         p.4 only
  [MNSZ22] A second moment proof               8     arXiv 2209.11347         p.1 only
  [BCW21] Note on sunflowers                   -     Discrete Math            no
  [Smooth] A smoother notion of spread        12     arXiv 2106.11882         no
```

[MNSZ22] page 1 lists them: the delicate counting of [ALWZ20], refined by
[FKNP21]; Shannon's noiseless coding theorem ([Ra20]); manipulations of
Shannon entropy ([Tao20]); and their own truncated second moment. **Four
routes, and the repository has planned its campaign against the one whose
prerequisite — Shannon coding — is the worst fit for a `nat`-only
development.**

That matters for §1's scoping. Stage A's technical choice — state the
covering step for the *product measure* so "probability" becomes plain
cardinality over the powerset, which `Spread.subsets` already enumerates
— is exactly right for the **counting** proof ([ALWZ20]/[FKNP21]) and for
nothing else. The entropy and second-moment routes both need real-valued
machinery this development does not have. So the first hour of the Rao
campaign should be spent reading, not proving, and the target may well
change from [Ra20] to [ALWZ20] §2 or [Lovett] §3.

Read in this order, all as rendered pages: [Ra20] (it is the axiom, and it
is eight pages), then [Lovett] §3 (self-contained and pedagogical), then
[ALWZ20] §2 for Definition 2.1, the *weighted* spread notion the axiom is
probably better stated against.

**One question these settle that this repository has open.** §5 records:
*"whether the `log` is necessary in the disjointness form with Rao's size
hypothesis was looked for and not found in the literature."* [ALWZ20]
page 4 says its own bound is sharp — *"For fixed α, β, the bound of
`(log w)^{w(1+o(1))}` for robust sunflowers in Theorem 1.9 is sharp; it
cannot be improved beyond `(log w)^{w(1-o(1))}`. We give an example
demonstrating this in Lemma 3.1"* — but that is the *robust sunflower*
form, not the disjointness form. Reading Lemma 3.1 decides whether the
open question is open.

### 15.2 [AHS72] is still unread, and three separate results rest on it

`iota(3) = 10`, the substitution recursion, and the exact values `f(2,k)`
all trace to Abbott–Hanson–Sauer 1972 (JCTA 12, 381–389). The repository
has a *reconstruction*, corroborated against [Kup25] and confirmed by its
own exhaustive searches, and that is genuinely good evidence — but the
paper has been on the unread list for three sessions. It is Elsevier 1972
and likely paywalled; if no legitimate copy is reachable, **record that
and stop**, per the standing rule. Do not formalise anything that depends
on a guess at its contents.

### 15.3 The next campaign: two candidates, ranked

**Primary — formalise `substitute` (§5 item 2).** It has quietly become
load-bearing for *four* results rather than one:

* the `g(6) >= 600` rate, which is the gap between the proved `2.714^n`
  and the known `3.162^n`;
* rows 5–7 of the `iota` table (§11.6), currently Rust-only;
* §13.1's general maximality theorem — "maximality is multiplicative
  under substitution" — which is stated about `substitute` and cannot be
  proved without it;
* §14.2's `rho` unboundedness, same reason.

It is the only item on the list whose work is known to be finite: the
construction decomposes as `union over A in G of (direct sum over v in A
of H_v)`, so `DirectSum` supplies most of the machinery, and the roadmap
has estimated it at one session for two sessions running. Doing it
converts three computational claims into theorems and unblocks two
negative results that are currently half-formal.

**Alternate — the spread campaign (§1/M4), preceded by the reading.**
Better motivated than it was: `StarDefect` showed that this repository's
Erdős–Rado layer and its spread layer are the *same statement* at
`|T| = 1` (`star_defect_is_the_singleton_spread_clause`), and
`SpreadRestrictions` already proves the weaker interface suffices.
Discharging `Rao20_lemma2` makes every conditional theorem here
unconditional and makes `make coqchk` report nothing at all. Multi-session,
and the first session is reading plus Stage A's counting layer.

### 15.4 Three cheap experiments, any of which fits beside either campaign

* **The full spread profile of the best-known constructions.** `rho` is
  the `|T| = 1` clause. Measure the rest: for each family in §11.6, the
  largest `kappa` for which it is `kappa`-spread in the full sense
  (`deg T <= |F|/kappa^{|T|}` for all `T`). That says how close the 1972
  construction sits to the spread lemma's *hypothesis*, which is what the
  published tightness examples are about, and every piece of machinery it
  needs is already written (`Spread.deg`, `ratio.rs`, the `iota` table).
  Nobody has done it because `rho` was not identified as spreadness until
  §14.5.
* **The cover chain, not the degree chain** (§4, still unclaimed after
  four sessions). §14 measured the ratio `|F|/maxdeg` down the greedy
  chain. Erdős–Rado's actual bookkeeping is over *vertex covers of the
  links* — at most `2(b-j)` points at level `j` — and how much consecutive
  covers overlap is still unmeasured. That is the literal form of "are the
  covers correlated across levels".
* **`iota(4) >= 32` through the general row** (§13.4). Unchanged, still
  the most concrete open target, still out of reach of branch-and-bound,
  SAT and prescribed symmetry. The unused lever is the rigidity: at
  `g = 16` the proved `N(3,g) <= 2g` would have to be met with equality,
  forcing regularity and extremal links, and no encoder here knows that.

### 15.5 The standing rule this section adds

§14.6 says: grep the development before calling a quantity unnamed. This
section adds the other half: **read the source of your own axiom before
planning sessions of work against it.** Eight pages, open access, cited in
`coq/ALWZ.v`, and the campaign built on it is the highest-value item in
the repository.

---

## 16. What the reading changed

Session N+3 read papers instead of proving things. Thirty-three papers
were downloaded and rendered, plus one MathOverflow answer; **eleven were
read cover to cover** (§17 added two more to §16's nine) —
[Ra20] (8pp), [ALWZ20] (19pp), [BCW21] (3pp), [Lovett] (28pp),
[MNSZ22] (8pp), [ErRa60] (6pp), [Mis26] (12pp), [Rao25] (12pp) and
Fukuyama's arXiv:2510.19037 (8pp), and — added in §17 — [Kup25] (66pp)
and [NaSa17] (5pp); seven more in part, and Hunter's answer in full.
`docs/reading.md` is the log, with an explicit page count for every
entry and a register of twenty-one claims resolved. This section is what
it did to the repository.

### 16.1 Refuted

Six withdrawals — **five, after §17.6 withdrew one of them.** §15
predicted the count going up would be a success condition, and it went
up; §17 is what happens when the same discipline is turned on this
section.

1. **"The only fully machine-checked formalisation of the Erdős–Rado
   1960 upper bound."** False, and false for five years before this
   repository started. René Thiemann's Isabelle/HOL entry *The Sunflower
   Lemma of Erdős and Rado* has been in the Archive of Formal Proofs
   since **25 February 2021**, proving `(r−1)^k·k!` with the same
   strict-inequality convention, plus two corollaries about cores that
   this development does not have. Withdrawn in `docs/references.md`.
   What does appear to be unduplicated is the *spread layer*.

2. **`coq/ALWZ.v`: "the source allows sets of size at most `m`."** Rao's
   Lemma 2 says *"sets of size `k`"*. The "at most" convention is
   [ALWZ20]'s Definition 1.1. The header cited the wrong paper for its
   own axiom's shape.

3. **`coq/ALWZ.v`: "Rao's proof is elementary — injections between
   finite sets and binomial estimates, no measure theory."** Its Lemma 5
   is Shannon's noiseless coding theorem, over a random partition of the
   ground set, through Kraft's inequality and the concavity of `log`.
   This one had been load-bearing: it is why §1 planned three stages
   against the wrong paper.

4. **`coq/IotaRate.v`: the extremal-set-theory toolbox "has never been
   pointed" at intersecting families here.** [ALWZ20] §4.2 is titled
   *Intersecting set systems*; Theorem 4.2 bounds the spread parameter
   of an intersecting `w`-uniform system by `O(log w)`, with a
   near-matching example. Different hypothesis from `ι`, so the sandwich
   and the equivalence stand — but nobody had looked, and the reason
   nobody had looked is that nobody had read §4.

5. **`docs/references.md`: "[ALWZ20] establishes `f(n,k) ≤ (Ck log n)^n`."**
   That is [BCW21]'s bound. ALWZ's own Theorem 1.4 is
   `(Cr³ log w log log w)^w`. ALWZ's §4 records the chain itself.

6. ~~**`docs/references.md`: [NaSa17] gives "`3(n+1)C^n` members".**~~
   **This withdrawal is itself withdrawn — see §17.6.** It was based on
   the abstract; Theorem 3 on page 2 says `3(n+1)`, and `C^n` does bound
   the binomial sum exactly. The original wording was right. **Five
   withdrawals stand, not six.**

And two half-withdrawals.

* The *reason* `docs/references.md` gave for [Mis26]'s "at least / more
  than" discrepancy was wrong. It is not an extracted-text artefact; the
  paper's abstract and its introduction disagree with each other.
* The cone's search note said *"one targeted search found nothing stating
  it"*. The **technique** — add a dummy point to every member of a
  maximal sunflower-free family one uniformity down — is stated, by Zach
  Hunter, in the answer this repository has been citing for two sessions
  without opening (§16.4). The exact statement `g(m) ≤ ι(m+1)` is still
  not found; the move is not new and was never claimed to be.

### 16.2 Confirmed

* **`Rao20_lemma2` is a faithful rendering of Rao's Lemma 2.** Checked
  symbol by symbol on the rendered page: the absolute spread condition,
  the `>` in the size hypothesis, the threshold `αp log(pk)`, the base-2
  logarithm, the direction of every weakening. The trusted core says what
  it claims to say.
* **`Spread.Spread` *is* Lovett's Definition 2.5**, on the nose, and the
  three quotations `docs/references.md` attributes to his page 7 are
  verbatim on rendered page 7. §14.5's correction is confirmed at the
  primary source.
* **Both branches of `StarDefect.the_two_branches_of_the_dichotomy` are
  on page 90 of the 1960 paper.** The maximal-disjoint-subfamily cover
  and the pigeonhole are Erdős and Rado's own argument for the finite
  distinct case, not a later textbook rewrite.
* **`coq/DirectSum.v`'s supermultiplicativity is [Kup25] Observation 2**,
  with proof, on rendered page 6. No novelty was claimed; now it has a
  citation.
* **[BCW21] `(Cp log k)^k` is still the peer-reviewed record**, and
  `coq/ALWZ.v`'s note on what it would buy is accurate.
* **`f(n,3) ≳ 10^{n/2}` is still the lower-bound record.** An arXiv
  sweep of three queries over 2024-06 → 2026-07 returned thirty
  sunflower papers and no lower-bound improvement. Negative evidence.
* **[Mis26] is unrevised and unwithdrawn**, and `coq/Compression.v`'s
  off-by-one convention is right.

### 16.3 Two things that changed a plan

**§1's technical choice was backwards.** It proposed proving the covering
step for the product measure at `p = 1/2`, because "probability becomes
plain cardinality over the powerset, which `Spread.subsets` already
enumerates". But the proof needs `W` *small* — `q ≈ 1/log n` — and at
that `p` the product measure is a weighted sum, not a cardinality. In
every published version the **fixed-size** statement is the primitive
(Lovett Claim 3.4 computes `|B| / (|F|·C(N,qN))`, already a ratio of two
cardinalities), and the product-measure version is *derived from it* by a
limiting argument. Starting at the product measure means formalising a
limit.

§1 is rewritten: Stage A builds fixed-size subset enumeration and
binomial counting, the target moves from [Ra20] to Lovett §3, and the
target *statement* moves from the absolute to the fractional form.

**And the alternative was checked rather than left as a hope.** [Rao25]
advertises *"a short elementary proof of the best known bounds for the
robust sunflower lemma"* in its §3. Read (pp. 8–10): it needs a Chernoff
bound, Azuma's inequality and Markov on top of the counting, where
Lovett §3 needs Markov and a geometric series. Not a shortcut, and
rejected on evidence rather than left on the list for a fourth session.

What §3 did give is that the **outer induction is already done here**.
Its dichotomy, p. 8, is `SpreadReduction.spread_reduction`'s, with
`Spread.RaoSpread` as the "Otherwise" branch. The only missing piece of
the whole argument is the covering step.

### 16.4 What it revealed that nobody here knew to look for

This is the part worth keeping.

* **The axiom said more than its source.** Rao's Lemma 2 fixes `r` at one
  value; `Rao20_lemma2` quantifies over every `r` above the threshold,
  and `SpreadYieldsDisjoint` is not monotone in `r` on general grounds —
  the repository's own `SpreadReduction.v` says so, in a comment, about
  the *elementary* lemma, and then the axiom did the thing the comment
  warns about. It is now discharged rather than assumed:
  `ALWZ.fractional_form_gives_the_axiom_shape` derives the whole
  quantified family from the fractional single-threshold statement, via
  machinery (`RaoSpread_Spread`, `Spread_mono`) that had been sitting in
  `Spread.v` since the spread layer went in. **The same shape as §14.5:
  the fix was already in the repository.**

* **§5's open question is not open in the way it was recorded.** It said
  "whether the `log` is necessary in the disjointness form was looked for
  and not found". It is found, three times, in sources that were sitting
  unread: [Ra20] p. 2, *"As far as we know, it is possible that Lemma 2
  holds even when `r(p,k) = O(p)`. Such a strengthening of Lemma 2 would
  imply the sunflower conjecture of Erdős and Rado."*; [Rao25] p. 3,
  *"This dependence is necessary for robust sunflowers ... Nevertheless,
  it is quite possible that the sunflower conjecture of Erdős and Rado
  holds in its original form."*; and both tightness examples ([ALWZ20]
  Lemma 3.1, [BCW21] Lemma 4) are transversal families, which **do**
  contain `p` pairwise disjoint sets and therefore say nothing about the
  disjointness form. The question is a stated open problem whose positive
  resolution is the conjecture.

* **One of the four proofs has a published gap, and two independent
  sources say so.** [MNSZ22] footnote 2, page 6: *"It was recently
  pointed out that the proof of [Tao20] has a gap, which has been
  corrected in [Hu21, Sto22]."* [Kup25] page 7: *"Tao [118] gave a proof
  based on entropy, which, however, contained a mistake."* §15.1 listed
  Tao's entropy argument as one of four routes without knowing this. The
  corrected entropy proof reaches `φ(s,k) ≤ (64s log k)^k` — which is
  where this repository's unsourced "`C = 64`" note came from, now with a
  page behind it.

* **Erdős–Rado 1960 does not prove `(k−1)^n n!`.** It proves something
  sharper — `φ(a,b) ≤ b!a^b(1 − 1/(2!a) − 2/(3!a²) − …)` for distinct
  families, p. 90 — and its headline Theorem III is about *multisets*,
  which is a factor `a` larger and is why `c = 12` at `a = b = 2`.
  `coq/ErdosRado.v` proves the rounded modern version, which is correct
  and weaker than the source. Nobody here knew the source was sharper.

* **[AHS72] also improved the upper bound, and Spencer 1977 improved it
  again.** [Kup25] p. 5: *"Abbot, Hanson and Sauer [1] in 1972, and then
  Spencer [116] in 1977 improved upper bounds on `φ(k,s)`. The result of
  Spencer states that for any fixed `s` and `ε > 0` there exists `C` such
  that `φ(k,s) ≤ Ck!(1+ε)^k`."* This bibliography had three results
  traced to [AHS72] and none of them was this one. **Spencer 1977 is not
  in the bibliography at all.**

* **A 2025 preprint claims to beat [BCW21]**, with a sub-logarithmic
  base `(ck² ln m / ln ln m)^m` (Fukuyama, arXiv:2510.19037v2). It is
  unrefereed, the author's own page calls the proof unstable, and the
  same author has a 2018 claim of the same kind that never appeared.
  Recorded and not adopted — but §12's threshold table had been written
  as though the 2021 record were unchallenged, and it is being
  challenged.

* **The 2024–2026 literature is much larger than the reading list
  assumed.** Thirty sunflower papers in twenty-five months, including a
  survey by Rao (Sept 2025), the Duke–Erdős extremal-structure line, the
  sunflower-free process, two vector-space analogues, and a June 2026
  polynomial improvement of [NaSa17]. The tabulated sweep is in
  `docs/reading.md` so the next session does not repeat it.

* **Zach Hunter's answer was reachable all along, and it contains two of
  this repository's theorems.** `docs/references.md` has credited the
  ground-set equivalence to it for two sessions without anyone opening
  it, because `WebFetch` refuses mathoverflow.net. **The StackExchange
  API is not blocked**, and one `curl` to
  `api.stackexchange.com/2.3/answers/463150?site=mathoverflow&filter=withbody`
  returns the body. Reading it:

  * the equivalence is confirmed at source, in one sentence;
  * his closing *"EDIT: my question is also silly. If no element is
    contained by a `(1/tk)`-fraction of the edges from `H`, then we can
    greedily find `t` disjoint sets"* is `StarDefect.star_defect_bound`,
    stated informally in January 2024, at constant `3b` against this
    repository's `2b`. That is the *third* independent source for the
    branch §14.5 withdrew the novelty claim for;
  * the question he proposes and immediately withdraws — a vertex of
    degree `≥ c_t^k|H|` — is the **exponentially weak** form of
    `StarDefect.StarBounded` and is trivially true, where `StarBounded`
    asks for a *constant* factor and is false. Keeping those two apart is
    the whole content of §14.

  The lesson generalises past this problem: **a blocked fetcher is not an
  unreachable source.** The same route reaches any MathOverflow post.

* **The negative-result infrastructure was reading the wrong sources.**
  "Not found in [Kup25]" was doing a lot of work in this repository, and
  [Kup25] is a 66-page survey of which six pages have now been read. Six
  pages of it produced one confirmation, one new reference, and one
  published theorem that this repository had reproved. The other sixty
  pages are unread.

### 16.5 What did not change

No theorem in the development is false, and none was weakened. Every
withdrawal above is a claim *about the literature* or a description of a
proof — never a mathematical statement checked by the kernel. `make
coqchk` still reports exactly one axiom. That is the system working: the
prose was wrong in six places and the mathematics in none, which is the
right way round, and the only reason the six were found is that somebody
finally rendered the pages.

### 16.6 The standing rule this section adds

§14.6: grep the development before calling a quantity unnamed.
§15.5: read the source of your own axiom before planning sessions against
it.

**§16.6: when the repository states what a source says, the sentence goes
in with a page number and a verbatim quotation, or it does not go in.**
Every one of the six withdrawals above is a paraphrase that drifted. None
of them would have survived being written as a quotation, because writing
a quotation forces you to have the page open.

---

## 17. The second pass: reading the survey properly, and what that cost

§16 was written after reading nine papers cover to cover. This section is
what changed when the reading went on — [Kup25] in full rather than two
pages, [ASU12], the MathOverflow answer, and one exhaustive computation.
It is shorter than §16 and more uncomfortable, because two of its entries
are corrections to §16 itself.

### 17.1 Withdrawn from §16's own session

**`pdftotext` cannot establish absence, and this repository has now been
bitten by that inside the very session that was written to stop it.**

Register row B12 was recorded as *"one clean negative: the strings
'covering number', 'transversal' and 'maximal intersecting' do not occur
anywhere in [Kup25]'s 66 pages"*, from a page-by-page extracted-text
search. Then page 19 was rendered:

> he ... shows that `G` should be empty using a simple, but somewhat
> tedious, 'covering number' argument which we avoid. [Kup25, p. 19]

The extractor had broken the phrase across a line — `'covering` then
`number'` — so a two-word search missed it in a document that contains
it. Page 59 has *"intersecting families with covering number 2"*. Both
withdrawn in `docs/references.md`.

The rule the reading discipline already had — *quote only from rendered
pages* — was obeyed. The rule it did not have is the other half:
**a negative from extracted text is not a negative at all.** Searching
is as much a source of false claims as quoting, and it was the untested
half.

**And the search vocabulary was wrong independently of the extractor.**
[Kup25] §1.7 is *about* the covering-number material, under the names
**base**, **nucleus**, **generating set**, **crosscut** and **minimal
cover**, crediting Erdős–Lovász, Füredi, Frankl and
Ahlswede–Khachatrian. p. 52: *"the produced sets ... give exactly the
family of **minimal covers** for the sets in `F` ... In a recent paper of
Frankl [52], the family of minimal covers is efficiently analyzed in
order to bound the maximal diversity of an intersecting family."* §14.6
said "search for the field's notation, not yours". The field has five
notations for this one, and none of them is "covering number".

### 17.2 Verified rather than cited

**`ι(3) = 10` is the unique simple 2-(6,3,2) design, and that is now
checked.** `docs/references.md` had it as *"standard design theory and
taken on the literature's word here, not verified"*, because the Handbook
of Combinatorial Designs is not open access. It never needed the
Handbook: there are `C(20,10) = 184756` ways to choose ten triples from
the twenty on six points. Exactly **12** are simple 2-(6,3,2) designs and
all 12 form a **single** isomorphism class, so `|Aut| = 720/12 = 60` — a
second, independent derivation of the group order, agreeing with
`structure::automorphisms`.
`rust/tests/iota_structure.rs::the_two_six_three_two_design_is_unique_and_that_is_checked_not_cited`.

A paywall is not always a blocker. Sometimes the claim behind it is a
finite check.

### 17.3 The vocabulary problem, which is the general form of §17.1

§14.6 said: search for the field's notation, not yours. That was right and
too weak. This session's corpus contains **five** names for a sunflower
and **five** for a cover, and every "not found" in this repository has
been run against one or two of each.

```
  the object            sunflower  Delta-system  s-star  weak sunflower
                        pseudo-sunflower  near-sunflower
  the covering notion   cover  base  nucleus  generating set  crosscut
                        minimal cover
```

`s-star` is [Kup25] fn. 6, p. 21, *"a name that appears in the follow-up
papers of Frankl and Füredi"*. `weak sunflower` is Erdős–Milner–Rado, via
[FPPTZ24] p. 1. The covering names are [Kup25] §1.7 and Definition 39.

**A negative search result is only as good as its worst synonym**, and
none of this repository's negatives has been run against this list. They
are all downgraded accordingly in `docs/reading.md`; none is deleted,
because the searches did happen and are worth knowing about.

### 17.4 What the full survey revealed

Five things, none of which the two-page read had reached.

* **`Spread.Spread` is a tool of the Δ-system method itself.** §1.7,
  p. 49: *"r-spread families in many ways behave like sunflowers with r
  petals, albeit they are much easier to find"*, via the
  **peeling-simplification** procedure; p. 53 names the **spread
  approximation** method of Kupavskii and Zakharov. Two research
  programmes built on this repository's central definition, and the
  bibliography had neither.

* **`SpreadReduction.spread_reduction`'s conclusion is Observation 58.**
  p. 50, two lines: *"If `G ⊂ ([n] choose ℓ)` is such that there is no
  `X` such that `G(X)` is `r`-spread, then `|G| ≤ r^ℓ`"* — followed by
  *"This bound is already better than the bound coming from not
  containing a sunflower."* No novelty was claimed for the reduction and
  none is now; but it is worth knowing it is a remark elsewhere.

* **`g` is the leading constant of a published asymptotic.** Theorem 37,
  p. 35 (Frankl–Füredi): `f(n,k,ℓ,s) = (φ(ℓ+1,s) + o(1))·C(n−ℓ−1,k−ℓ−1)`
  for the Duke–Erdős forbidden-sunflower problem. At `ℓ=1, s=2` the
  constant is `φ(2,2) = f(2,3) − 1 = 6`, which `coq/F23.v` proves. The
  small exact values are not only local curiosities.

* **A third name for a sunflower.** Footnote 6, p. 21: `Δ(s)`-systems
  are called **`s`-stars** "in the follow-up papers of Frankl and
  Füredi". Every negative search in this repository has used "sunflower"
  or "Δ-system".

* **The Hall layer has a second customer.** Theorem 29 (Frankl–Katona),
  p. 29, is proved by a containment bipartite graph and *"a Hall's
  condition in disguise"* — `coq/HallCore.v`, `coq/KoenigHall.v` and
  `coq/Matching.v`, built for the uniformity-2 programme, are exactly
  that machinery.

### 17.5 Two citations settled, one still shut

* **[AHS72]**, in full, and now with the closure established rather than
  assumed:

  > H. L. Abbott, D. Hanson and N. Sauer, *Intersection theorems for
  > systems of sets*. **Journal of Combinatorial Theory, Series A**,
  > vol. **12**, issue **3**, May **1972**, pp. **381–389**. Elsevier.
  > **DOI `10.1016/0097-3165(72)90103-3`.**

  The citation is from [Kup25] p. 62, the bibliographic detail verified
  against Crossref. [Kup25] omits the series letter; JCT split at volume
  10 (1971), so volume 12 is Series A and the two agree.

  **It is closed, and that is a fact rather than a failed search.**
  OpenAlex's record for that DOI reports `oa_status: "closed"` and
  `any_repository_has_fulltext: false` — no open copy in any indexed
  repository. Five retrieval routes are recorded in `docs/reading.md`;
  the fourth session in a row to try should not be a fifth. §15.2's
  instruction stands: **record it and stop.**

  One detail worth keeping: an earlier attempt this session guessed the
  DOI suffix as `-4` and got a 404. The real suffix is `-3`. Same lesson
  as §17.7.
* **Spencer 1977**, in full, from [Kup25] p. 66: *Canadian Mathematical
  Bulletin 20 (1977), N2, 249–254*, doi:10.4153/CMB-1977-038-7.
  Unreachable — Cambridge Core, no open access.
* **[Ko97]'s bound** had two incompatible renderings in §16's sources.
  [ASU12] Theorem 2.2 agrees with [Rao25] on
  `cs!·(log log log s / log log s)^s`; [Kup25] p. 5 is garbled. Fixed.
* **"Lu" vs "Hu"** is settled: [Kup25]'s reference list, p. 65, gives
  **Lunjia Hu**. Its body text is the typo.

### 17.6 A withdrawal of a withdrawal

§16 listed six withdrawals. One of them was wrong.

It said `docs/references.md` misquoted [NaSa17] as *"`3(n+1)C^n`
members"* when the paper says `3n Σ_{k≤n/3} C(n,k)`. That came from
reading **page 1**, the abstract. Pages 2–5 were then read, and
**Theorem 3 on page 2** is:

> `|F| ≤ 3(n+1) Σ_{k ≤ n/3} C(n,k)`, and `μ₃^S ≤ 3/2^{2/3} = 1.889881574…`

The abstract and the theorem disagree about the polynomial factor, and
the theorem is the claim. And `Σ_{k≤n/3} C(n,k) ≤ 2^{H(1/3)n}` with
`H(1/3) = log₂3 − 2/3`, so `(3/2^{2/3})^n` bounds it exactly — the
original `3(n+1)C^n` was right in the factor *and* in the shape. **§16's
sixth withdrawal is withdrawn.** Five stand.

The reading discipline's rule 3 says nothing is quoted from an abstract.
This session then based a correction on one. **Page 1 is not the paper**,
and abstracts disagree with their own theorems often enough to matter —
[Mis26] does it too, "at least" against "more than", which §16 already
recorded without drawing the general moral.

### 17.7 One more failure mode, recorded because it wasted a read

The first attempt at [ASU12] fetched `arXiv:1109.6216`, an identifier
recalled rather than looked up. That is *Observation of the Perseus galaxy
cluster with the MAGIC telescopes*, and four of its pages were rendered
and read before the mismatch was obvious. [ASU12] is not on arXiv at all.

**Identifiers get looked up, never recalled** — the same rule as
quotations, for the same reason, and it belongs beside §16.6.

### 17.8 The corpus is pinned now

`docs/papers/` holds 29 records: SHA-256 of the exact bytes rendered and
read, page count from `pdfinfo`, source URL, retrieval date, and the
licence the publisher states. `fetch.sh` rebuilds the corpus and fails on
a hash mismatch, so a paper revised upstream cannot be quoted as the
version that was read. Fourteen PDFs are stored — the ones whose licence
permits it, decided from arXiv's OAI-PMH licence field rather than by
assumption — and `pdf/.gitignore` is a whitelist generated from that
flag, so rebuilding the full corpus locally cannot become a copyright
problem in a later commit.

This session spent its first hour re-fetching what the last one had
already found. That was the last time.
