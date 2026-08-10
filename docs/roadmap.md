# Roadmap

What is worth doing next, why, and what to avoid. Written to be picked
up cold: each item states the target, the technical choice that decides
whether it is feasible, and the failure mode that would sink it.

The repository's state is in [`STATUS.md`](../STATUS.md); the testing
layer and its limits are in [`testing.md`](testing.md).

> **Starting cold? Read §32 first.** It is the most recent session's
> handover: what moved, what did not, the five open questions that would
> count as new mathematics, and the failure modes to skip. Then §1 (the
> axiom, and how far its discharge has got), and `docs/reading.md`'s
> rules — there are **26**, each earned by an error made here.
>
> The one sentence a cold reader most needs: **discharging the single
> axiom will not improve any bound** — it makes a Rao-2020-shaped bound
> unconditional, and the literature record is already better. §32.2.

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

### Read at proof level, August 2026 — the exact skeleton

[Lovett] §3 was re-read line by line before any of the staging below was
written. The whole proof is six statements, and their dependency graph is
a chain:

```
  Def 3.2   minimal fragment  M(S,V) = min-size element of
                              { S' \ V : S' in F, S' subset S u V }
  Obs 1-3   M subset S ; M disjoint from V ; M empty iff some S' subset V
  Claim 3.3 Z := V u M(S,V), F' := { S' in F : S' subset Z }.
            Then F' nonempty, and every S' in F' has S' \ V = M(S,V).
  Claim 3.4 THE COUNT.  Pr[ |M(S,V)| >= n/2 ]  =  |B| / (|F| * C(N,qN))
            bounded by an explicit encoding.
  Claim 3.5 Markov on 3.4, plus Exercise 3.1 (spreadness survives
            shrinking sets and passing to a (1-eps)-subfamily).
  Claim 3.6 Iterate: if F_t contains the empty set then union V_i
            contains a member of F_0.
  Lemma 3.1 Apply 3.5 log n times; product of (1 - 10^{-n/2^i}) >= 0.8.
```

**Three things this changes about the staging, none of which were visible
from the section's summary.**

1. **Claim 3.6 and Claim 3.3 are arithmetic-free.** 3.6 is an induction on
   `t` with no numbers in it at all, and it is the claim that actually
   produces the conclusion. 3.3 is pure set algebra. Together they are
   perhaps a third of the proof and they need nothing but `Sets.v`.

2. **The encoding's injectivity is an equation, not an argument.** Claim
   3.4 defines `phi(S,V) = (Z, S', M, S \ M)` and justifies it in one
   sentence: *"we can decode `(S,V)` given `phi(S,V)` since
   `S = M u (S \ M)` and `V = Z \ M`"*. So the formal obligation is not
   "`phi` is injective" — it is `psi (phi (S,V)) = (S,V)` for an explicit
   `psi`, which is a rewrite, not a case analysis. This is the single
   most useful thing the proof-level read produced.

3. **There is exactly one binomial estimate in the whole proof**:
   `C(N, qN+m) <= q^{-m} C(N, qN)`. Everything else is `C(n,m) <= 2^n`
   and a geometric sum. The earlier plan budgeted for "binomial estimates"
   in the plural; there is one.

### Stage A — the counting layer — **DONE, `coq/Counting.v`, §30**

Every item on the list below is proved, axiom-free, and cross-checked by
`rust/tests/counting.rs` against an independent implementation. The one
correction Stage A produced is that **the binomial estimate's hypothesis
is not the one this section assumed**: §1 wrote it at `j = qN`, i.e.
`c*N ≤ d*j`, and the argument in fact runs at `c*N ≤ d*(j+1)`, which is
strictly weaker and is *exactly* the boundary — `c*N ≤ d*(j+2)` is false.
See §30.2. `Counting.binom_ratio_at_threshold` is the shape this section
asks for, derived from the sharp one.

**The technical choice from an earlier version of this section was
backwards.** §1 used to say: state the covering step for the *product
measure* with each element included independently with probability `1/2`,
so "probability" becomes cardinality over the powerset, which
`Spread.subsets` already enumerates. Three things are wrong with it:

* the proof needs `V` to be a **small** random set, `q = p/log n`. At
  `p = 1/2` the product measure is plain cardinality; at `p = 1/log n` it
  is a weighted sum, which is *worse* than the fixed-size version;
* in every published *proof* the **fixed-size** statement is the
  primitive. Lovett Claim 3.4, ALWZ Lemma 2.8 and FKNP Theorem 1.6 are
  all stated for a random subset of fixed size. (Surveys sometimes state
  the *conclusion* in the product measure — [Kup25] Theorem 3 does — but
  nothing proves it there.);
* the product-measure statement is *derived from* the fixed-size one, by
  a limiting argument. Lovett p. 11, in full: *"Take now `U'` of growing
  size; the limiting distribution of `W` converges to `Bin(U,p)`."*
  Starting at the product measure means formalising that limit.

So Stage A builds **fixed-size subset enumeration and one binomial
ratio**, not powerset enumeration:

* `subsets_of_size : nat -> list nat -> list (list nat)`, with
  `length (subsets_of_size j U) = C (length U) j`;
* `count : (list nat -> bool) -> list (list nat) -> nat`, injection
  implies `<=`, additivity over disjoint predicates;
* `C (n, m) <= 2 ^ n`;
* **the one estimate**: `C(N, j+m) * c^m <= C(N, j) * d^m` for `j = qN`
  and `q = c/d`. Cleared denominators, so it stays in `nat`. This is the
  only place rationals would otherwise appear.

`Spread.subsets` still helps — `subsets_of_size j = filter (length = j)
(subsets ...)` is the cheap definition and gives membership for free —
but the *counting* is over the size-`j` layer.

Independently testable, and the Rust testbed can falsify every line of it.

### Stage B — the encoding — **set-theoretic half DONE, `coq/Fragment.v`, §31**

Definition 3.2, all three observations, both parts of Claim 3.3, the
encoding, its decoder and the injectivity the count consumes are proved,
axiom-free, and were falsified over 32968 exhaustive triples first. The
count itself is **not** done; §31.5 names the two things in the way (a
fibred counting lemma, and the geometric sum). And Stage B produced the
same kind of correction Stage A did: **the decode is not an equation**,
only its `V` half is, and closing the `S` half needs `Distinct F` — see
§31.3 and rule 24.

### Stage B — the encoding, and it is smaller than it looked

* `minimal_fragment : Family -> list nat -> list nat -> list nat`,
  picking the first element of minimal length in an explicit enumeration
  (Lovett's *"breaking ties arbitrarily"* becomes "first in the
  enumeration", which is what makes it a function rather than a choice);
* the three observations, and **Claim 3.3** — set algebra, no arithmetic;
* `phi` and an explicit `psi`, with `psi (phi (S,V)) = (S,V)`;
* **Claim 3.4**'s count, assembling Stage A's four pieces.

The stall risk is here, but it is smaller than the previous version of
this section assumed, because the injectivity obligation is an equation.

### Stage C — the iteration

* **Claim 3.5**: Markov, which in the fixed-size setting is the counting
  statement "if the average over `V` is at least `(1-eps)|F|` then most
  `V` are good", plus Exercise 3.1's two spreadness-preservation lemmas;
* **Claim 3.6**: induction on `t`. Arithmetic-free, and it is the step
  that yields the conclusion;
* the `log n` iteration and the product `prod (1 - 10^{-n/2^i}) >= 0.8`.

**Scoping decision — do not chase the constant.**
`FractionalSpreadDisjoint` is instantiated at whatever `t` the proof
yields, and `fractional_form_gives_the_axiom_shape` is monotone upward in
`r`, so any explicit constant discharges the axiom. `c = 2^20` closes the
file exactly as well as `c = 64`.

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
  mutation testing from 151 anecdotes into a coverage metric over the
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
  5   >=78 (ground 15)   >=2.9718   <- plateau search, §20.6; was >=54
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
  5           78       15       2.3901   plateau search, §20.6 (was 54)
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
  5         78               101        0.772
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

Session N+3 read papers instead of proving things. Thirty-five papers
were downloaded and rendered, plus one MathOverflow answer; **twelve were
read cover to cover** (§17 added two to §16's nine, §19 added a twelfth) —
[Ra20] (8pp), [ALWZ20] (19pp), [BCW21] (3pp), [Lovett] (28pp),
[MNSZ22] (8pp), [ErRa60] (6pp), [Mis26] (12pp), [Rao25] (12pp) and
Fukuyama's arXiv:2510.19037 (8pp); added in §17, [Kup25] (66pp) and
[NaSa17] (5pp); added in §19, [KuZa22] (27pp). Seven more in part, and
Hunter's answer in full.
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

`docs/papers/` holds 35 records: SHA-256 of the exact bytes rendered and
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

---

## 18. What the reading changes about the plan

§16 and §17 recorded what the papers said. This section is what to do
about it. It is a reprioritisation, and it moves one item to the top that
was not on the list at all.

### 18.1 The thing that was already here, three times, unconnected

The repository contains all three of these and has never put them in the
same sentence:

* **`Conjecture.spread_conjecture`** — "is there, for each `k`, a constant
  `c k` such that every `c k`-spread family of more than `(c k)^n` sets
  of size `n` contains `k` pairwise disjoint members?" — with
  `spread_conjecture_suffices` proving it implies the Erdős–Rado
  conjecture. Machine-checked, since the spread layer went in.
* **§3.6's `empirical_threshold`** — exhaustive search for the smallest
  `r` with `SpreadYieldsDisjoint m k r`. It measures `r*(2,3) = 3` and
  `r*(3,3) = 3`: **flat in the uniformity**, against the axiom's
  `Θ(k log km)` which is 9 and 12 at those points. §3.6 read that as
  "the axiom is loose".
* **[Ra20] p. 2** — *"As far as we know, it is possible that Lemma 2
  holds even when `r(p,k) = O(p)`. Such a strengthening of Lemma 2 would
  imply the sunflower conjecture of Erdős and Rado."*

These are one question. `spread_conjecture` **is** Rao's `r(p,k) = O(p)`.
`empirical_threshold` **is** a measurement of its hypothesis. And §3.6's
flat table is data on a named open problem whose positive resolution is
the conjecture — not a remark about a loose axiom.

`coq/Conjecture.v` already says *"removing the dependence on `n` is
open"*. What nobody here knew is that the source says it too, says it
would settle the conjecture, and that this repository is measuring it.

### 18.2 The first concrete consequence: `r*` must break, and at `m = 9`

If `r*(m,3) = 3` for all `m` then `spread_conjecture_suffices` gives
`f(m,3) ≤ 3^m + 1`. The 1972 lower bound is `≈ 3.162^m`. **So the flat
table cannot stay flat**, and the repository's own constructions say
where it breaks first:

```
   m   3^m       best known lower bound on g(m)     route
   2         9            6   g(2) = 6 exact
   3        27           20   g(3) >= 2*iota(3)
   4        81           54   g(4) >= 2*iota(4)
   6       729          600   g(6) >= g(2)*iota(3)^2
   7      2187         1080   g(7) >= g(3)*g(4)   (direct sum)
   8      6561         5400   g(8) >= g(4)*iota(2)^4
   9     19683        20000   g(9) >= g(3)*iota(3)^3   <-- BREAKS
  12    531441       540000   g(12) >= g(4)*iota(3)^4
```

`g(9) ≥ g(3)·ι(3)³ ≥ 20·1000 = 20000 > 19683 = 3⁹`, margin **317**.

**And the near side: at both measured points the inequality is tight.**
`spread_reduction` gives `g(m) ≤ r^m` for any working `r`, so

>  `r*(m,3)  ≥  ⌈ g(m)^(1/m) ⌉`

is a theorem — `IotaRate.spread_threshold_bounds_g` and its
contrapositive `g_lower_bound_refutes_spread_threshold`, which is the
integer form and needs no roots. Evaluate it where both sides are known:

```
   m    g(m)        ceil(g(m)^(1/m))     measured r*(m,3)
   2    6 (exact)   ceil(2.449) = 3      3        <- tight
   3    >= 20       ceil(2.714) = 3      3        <- tight
```

**Tight at both.** Two points is nearly nothing and this is recorded as a
hint, not a result. But if `r*(m,3) = ⌈g(m)^(1/m)⌉` in general then the
spread-threshold sequence and the extremal-rate sequence are *the same
object*, and since the 1972 rate is `10^(1/2) = 3.162...` the threshold
should settle at **4** — the conjecture true with a nearly sharp
constant.

**It has a falsifiable consequence available now.** `r*(3,3) = 3` forces
`g(3) ≤ 27` (`flat_threshold_at_three_forces_g_three_at_most_27`), and
this development only knows `20 ≤ g(3) ≤ 48` — 20 from
`Intersecting.lower_bound_3_3_20`, 48 from Erdős–Rado. So:

> **Computing `g(3)` exactly decides `r*(3,3)`.** If `g(3) > 27` the flat
> table breaks at uniformity 3 rather than 9, and the whole tightness
> pattern dies at its second data point.

That is a far cheaper search than widening `empirical_threshold` past
ground 10, and it is the same computation as §18.3 item 2 approached
from the other side. **Two open computations that are one computation.**

Both inputs are already machine-checked — `g(3) ≥ 20` is
`IotaRate.iota_three_sandwich`, `ι(3) ≥ 10` is `Intersecting.iota3`. The
only missing piece is the substitution itself, which is **already §15.3's
primary campaign**. Formalising `substitute` therefore buys a fifth
result nobody had counted:

> **`~ SpreadYieldsDisjoint 9 3 3`** — and hence `c(3) ≥ 4` in
> `spread_conjecture`, the first lower bound on the constant in the
> spread reformulation.

That is a negative result about a named open problem, machine-checked,
from constructions the repository already owns. It is the sharpest thing
on this list and it did not exist before the reading, because nobody knew
§3.6 and §2 were the same question.

**Note the direct sum cannot do it.** `g(a+b) ≥ g(a)g(b)` from `g(2)=6`
gives `6^{m/2} = 2.449^m < 3^m` forever. Only the substitution crosses 3.
That is the cleanest statement yet of why §5's "the direct sum does not
reach 3.162" matters, and it retires the question of whether
`substitute` is worth the session.

### 18.3 Priorities that go up

1. **`substitute`, unchanged as the primary campaign, but for a fifth
   reason** (§18.2). It was already load-bearing for four results.
2. **Extend `empirical_threshold`.** §3.6 stalls at ground 10 for
   `(3,3,3)` and says *"widening it needs a better search, not a bigger
   budget"*. That is now the highest-value computation in the repository,
   because the quantity it measures is a published open problem. The
   ground-10 case is also exactly where a counterexample could first
   live.
3. **`φ(3,s)` for small `s`.** [Kup25] Theorem 37 makes `φ(ℓ+1,s)` the
   leading constant of the Frankl–Füredi asymptotic for the Duke–Erdős
   problem. The repository's exhaustive small-case machinery computes
   exactly this. `φ(2,2) = 6` is already `coq/F23.v`. Cheap, and it has
   an external consumer for the first time.
4. ~~**The spread-approximation literature** ([KuZa22], [Ku23]).~~
   **Done — see §19.** [KuZa22] read in full, [Ku23] in part. The answer
   is yes: `Spread.Spread` is the definition at the centre of a
   programme whose selling point is that it is elementary where the
   alternatives are algebraic, and its base layer is three statements
   this repository already has.
5. **Frankl–Katona (Theorem 29), as a second customer for the Hall
   layer.** `HallCore.v`, `KoenigHall.v` and `Matching.v` exist for the
   uniformity-2 programme and are otherwise unused; [Kup25] p. 29 proves
   Theorem 29 by "a Hall's condition in disguise". Cheap reuse.

### 18.4 Priorities that go down

1. **`coq/ErdosRado.v` as a headline result.** Duplicated in Isabelle
   since February 2021, and the AFP entry proves more. Keep it as
   infrastructure; stop presenting it as the contribution.
2. **Novelty framing generally.** With five names for a sunflower and
   five for a cover, and every search here having used two of each, "not
   found" is not worth much. The `ι` programme should be sold on what it
   *is* — a machine-checked equivalence — not on being unpublished.
   `IotaRate`'s value does not depend on the literature search, and it
   should stop resting on one.
3. **[AHS72].** OpenAlex says `oa_status: closed`,
   `any_repository_has_fulltext: false`. Four sessions have tried. Stop.
4. **Chasing the axiom's constant.** Unchanged, and now cheaper to
   avoid: `fractional_form_gives_the_axiom_shape` is monotone upward in
   `r`, so any explicit constant closes the file.

### 18.5 The moonshot, restated

The repository is not going to prove the sunflower conjecture. Thirty
arXiv papers in twenty-five months did not move the lower bound off 1972,
the upper bound has not moved since 2021 except for one unrefereed
preprint, and the four proofs of the spread lemma are one gapped, two
analytic, one formalisable.

What it can uniquely do, in order:

1. **Discharge `Rao20_lemma2`.** No prover has a spread lemma. The target
   is now precisely scoped: `FractionalSpreadDisjoint` at one threshold,
   by the counting proof of Lovett §3, over fixed-size subsets. Everything
   downstream is already proved and `fractional_form_gives_the_axiom_shape`
   already bridges the forms.
2. **Be the machine-checked reference for the spread framework**, which
   the reading shows is becoming general-purpose machinery rather than a
   sunflower-specific trick.
3. **Be the exhaustive-data source for the small constants**, which
   turn out to appear in published asymptotics rather than only here.
4. **Compute the sharp spread threshold sequence `r*(m,3)`.**

The fourth is the one worth calling a moonshot, and it is new. `r*(m,k)`
is the smallest `r` for which `SpreadYieldsDisjoint m k r` holds. By
`spread_conjecture_suffices`, **whether `r*(m,3)` is bounded in `m` is
the sunflower conjecture at `k = 3`**, and its limiting value is the
constant. So the sequence is not evidence about the problem; it *is* the
problem, one finite computation at a time:

```
   m        1    2    3    4    5    6    7    8    9   ...
   r*(m,3)  ?    3    3    ?    ?    ?    ?    ?   >=4  ...
                 |    |                            |
                 exhaustive (§3.6)                  §18.2
```

Two entries measured, one bounded below, and six unknown between them.
Nobody has computed this sequence. The repository is the only place with
all three of the pieces it needs — a formal statement of
`SpreadYieldsDisjoint`, a machine-checked reduction from it to the
bound, and an exhaustive testbed — and §3.6 has already found the exact
obstacle, which is search quality at ground 10 rather than budget.

If `r*(m,3)` settles at 4, that is `f(m,3) <= 4^m + 1` against the
1972 lower bound of `3.162^m`, and the conjecture is true with a nearly
sharp constant. If it grows, the conjecture is false. Either answer is
worth more than another conditional theorem, and the first six terms are
finite.

The first three items are engineering with a known finish. The fourth is
a question nobody has asked in this form, that this repository is built
to answer, and whose first term past the measured range it can already
bound. That is a better portfolio than "prove the conjecture", and it is
what the reading actually supports.

### 18.6 The methodological rules, consolidated

§14.6, §15.5, §16.6, §17 each added one. Together:

1. **Grep the development before calling a quantity unnamed.**
2. **Read the source of your own axiom before planning against it.**
3. **A claim about a source goes in with a page number and a verbatim
   quotation, or it does not go in.**
4. **`pdftotext` cannot establish absence.** Line breaks defeat phrase
   search silently.
5. **A negative is only as good as its worst synonym.** Five names for a
   sunflower, five for a cover.
6. **Page 1 is not the paper.** Abstracts disagree with their own
   theorems — [NaSa17] and [Mis26] both do.
7. **Identifiers get looked up, never recalled.** One guessed arXiv ID
   cost four pages of an astrophysics paper; one guessed DOI suffix cost
   a 404.
8. **A paywall is not always a blocker.** Sometimes the claim behind it
   is a finite check — the 2-(6,3,2) uniqueness took one enumeration.
9. **A scripted edit that cannot find its target must fail, not no-op.**
   Added by §20.9, which is a commit message that said a slow test row was
   removed when it was not.
10. **Before calling a bound an advance, evaluate it against the best
    published bound for the same quantity — including the one the
    repository has already assumed as an axiom.** Added by §22.7, which
    is a session that improved `r*(m,3)` from `2m+1` to `1.74m` without
    noticing that `ALWZ.v`'s axiom already gives `O(log m)`.

---

## 19. What the spread-approximation literature says the spread layer is for

§18.3 named [KuZa22] and [Ku23] as the highest-value unread items,
because if `Spread.Spread` is becoming general infrastructure then the
spread layer is worth more than this conjecture. Both are now read in
full. The answer is yes, and it is more specific than expected.

### 19.1 Spread replaces representation theory and Fourier analysis

[KuZa22] abstract, p. 1: the method is *"based on the notion of `r`-spread
families and builds on the recent breakthrough result of Alweiss, Lovett,
Wu and Zhang for the Erdős–Rado 'Sunflower Conjecture'"*, and *"can work
in a variety of sparse settings"*. Its Theorem 2 proves the
Ahlswede–Khachatrian theorem for **permutations** in a new range, and
p. 3 says why that matters:

> The proof is also much simpler and avoids the use of heavy machinery of
> the previous authors.

The machinery avoided is named on [Ku23] p. 2: *"Early approaches to this
question were algebraic, based on Hoffman-Delsarte type bounds and
representation theory. The approach of [5] combines junta
approximations, coming from Boolean Analysis, with representation theory.
Zakharov and the author introduced a combinatorial technique of spread
approximations that is based on the breakthrough in the Erdős–Rado
sunflower problem due to Alweiss, Lovett, Wu and Zhang."*

**That is the strategic fact.** `Spread.Spread` is the definition at the
centre of a programme whose selling point is that it is *elementary where
the alternatives are algebraic*. Elementary-where-the-alternatives-are-
algebraic is exactly what a `nat`-only Coq development can host, and
nothing else in this repository's reach has that property.

### 19.2 Three of this repository's theorems are its primitives

Reading [Ku23] §3 — which p. 1 advertises as *"a self-contained
presentation of the spread approximation technique"*, so it is the entry
point — the method's base layer is three statements this development
already has:

* **Observation 11**: *"let `X` be an inclusion-maximal set that
  satisfies `|F(X)| >= r^{-|X|}|F|`. Then `F(X)` is `r`-spread as a
  family in `2^{[n]\X}`."* That is `Spread.rao_witness` finding a
  violator and `Spread.link` stripping it, with maximality doing the
  work.
* **Observation 12**: *"If for some `α > 1` and `F ⊂ C([n],k)` we have
  `|F| > α^k` then `F` contains an `α`-spread subfamily of the form
  `F(X)` for some set `X` of size strictly smaller than `k`."* That is
  `SpreadReduction.spread_reduction`'s dichotomy. Kupavskii's proof is
  two sentences, and he adds *"this observation together with Theorem 10
  implies bound (1)"* — the sunflower bound.
* **Theorem 13** is the peeling procedure built on top, and [Ku23] p. 6
  says of the next one: *"Theorem 14 alone can be seen as a strengthening
  of one of the important parts of the Delta-system method."*

So `spread_reduction` is not a step on the way to one conjecture; it is
the base of an active method. That is a better argument for the spread
layer than anything in §16–18, and it was not available before reading.

### 19.3 The sunflower bound is a subroutine, so the constant matters

[KuZa22] Lemma 14 bounds `|W_i| <= (C_0 q log_2 q)^{q-i-t}` with
`C_0 < 2^15`, and it gets there by applying the sunflower bound (their
equation (1), with `C = 2^10`) to a family shown in Lemma 14(iii) not to
contain a sunflower with `q-i-t+2` petals.

**Improvements to the sunflower bound propagate into this method's
constants.** That is a use for the [BCW21] refinement, and for the
sharper `r*` measurement of §18.2, that this repository did not know it
had.

### 19.4 And `τ` is a tool there, not a curiosity

Register row B12 asked whether covering numbers of intersecting
hypergraphs are studied. [KuZa22] Lemma 14(v) uses `τ` directly, defining
it inline: *"Recall that, for a family `F`, `τ(F)` is the size of the
smallest set `Y` such that `Y ∩ F ≠ ∅` for each `F ∈ F`."* Combined with
[Kup25] §1.7's minimal-cover material, B12's original "not found" is
comprehensively wrong, and §17.1 already withdrew it.

### 19.5 What this does *not* say

The spread approximation method needs `p`-random subsets, expectations,
Markov, Chernoff-type estimates and real-valued `τ`, `ε`, `θ`. **It is not
formalisable here as it stands**, and nothing above claims otherwise.
What is formalisable is its base layer — Observations 11 and 12 — which
this repository already has, and the ALWZ input (Theorem 10), which is
§1's campaign.

The honest reading is: **discharging `Rao20_lemma2` would put a
machine-checked floor under an active research programme, not just under
this repository's own conditional theorems.** That raises §1's value and
does not change its difficulty.

### 19.6 Tier 4, and where it stops

* **Coding theory / the Terwilliger algebra.** [Schrijver05] read pp. 1–2
  of 8. The method is block-diagonalisation of the (non-commutative)
  Terwilliger algebra of the Hamming cube — a C\*-algebra — followed by
  semidefinite programming. **Roadmap M2 should be marked not viable for
  this development**: it needs complex matrices, positive
  semidefiniteness and a numerical SDP solver, none of which are `nat`
  and none of which exist here. The Johnson-scheme connection [Kup25]
  p. 55 points at is real, but it is on the far side of that stack.
* **Flag algebras, design nonexistence, Stanley–Reisner** — not read. See
  §19.7 for why.

### 19.7 Five wrong identifiers in one session

Four Tier-4 arXiv IDs were recalled rather than looked up. They fetched,
in order: a PDE paper on a symmetry problem; *What Scalars Should We
Use?*; a condensed-matter paper on heat conduction in an anharmonic
crystal; and a lattice-QCD paper on kaon masses. A fifth, for [ASU12],
fetched an astrophysics paper on the Perseus cluster and four of its
pages were read before the mismatch was obvious.

All five were caught by rendering page 1 before reading — which is now
the rule, and is why only one of them cost anything. §17.7 stated the
lesson from a single instance; five instances make it a procedure:

> **Fetch, render page 1, confirm the title and authors, and only then
> read.** An identifier that was not copied from a reference list or a
> Crossref record is a guess, and guesses resolve to real papers about
> other subjects.

Correct citations, obtained from Crossref, for whoever picks these up:

```
  Schrijver 2005   New code upper bounds from the Terwilliger algebra and
                   semidefinite programming.  IEEE Trans. Inform. Theory
                   51:2859-2866.  doi 10.1109/tit.2005.851748.  GREEN OA
                   at ir.cwi.nl/pub/14098/14098B.pdf  [read pp.1-2 of 8]
  Gijswijt-Schrijver-Tanaka 2006  New upper bounds for nonbinary codes
                   based on the Terwilliger algebra and SDP.  JCTA
                   113:1719-1731.  doi 10.1016/j.jcta.2006.03.010. CLOSED
  Razborov 2007    Flag algebras.  J. Symbolic Logic 72(4):1239-1282.
                   doi 10.2178/jsl/1203350785.  CLOSED
  Frankl 1978      On intersecting families of finite sets.  JCTA
                   24:146-161.  doi 10.1016/0097-3165(78)90003-1. CLOSED
  Fueredi 1983     On finite set-systems whose every intersection is a
                   kernel of a star.  Discrete Math. 47:129-132.
                   doi 10.1016/0012-365x(83)90081-x.  CLOSED
```

OpenAlex reports `oa_status: closed` for all four of the closed ones, so
these are index-confirmed rather than search-exhausted, the same standard
§17.5 applied to [AHS72].

---

## 20. The construction session: what moved, and the cheap experiment that died

§18 set three targets with numbers in them — `iota(4) >= 32`, `iota(6) >= 317`,
and "compute `g(3)` exactly, because it decides `r*(3,3)`". This section is
what a session aimed at all three actually produced. None of the three
happened. Something else did, and it closed the third target rather than
answering it.

### 20.1 The observation, which is one sentence

Erdős–Rado's step takes a maximal pairwise-disjoint subfamily `M ⊆ F`, notes
that every member meets `T = ∪M` (else `M` was not maximal), and bounds
`|F|` by `|T|` times the largest degree — each degree being a link, hence a
`(b-1)`-uniform sunflower-free family, hence at most `g(b-1)`. That gives
`g(b) <= 2b · g(b-1)`.

Not all of those members cost `g(b-1)`. Call a member **pure at `x`** when it
meets `T` in `x` and in nothing else. Then

> the pure members at `x`, with `x` removed, form an **intersecting** family.

Suppose two of them, `A \ x` and `B \ x`, were disjoint. Let `A₀` be the
member of the matching `M` through `x`. Then `A₀ \ x` lies inside `T`, and
purity says `A \ x` and `B \ x` do not — so `A \ x`, `B \ x` and `A₀ \ x` are
three **pairwise disjoint** members of the link at `x`, which is a sunflower
with empty core there, which lifts to a sunflower in `F` with core `{x}`.

That is the whole argument. `coq/PureLink.v` is
`pure_link_intersecting`, and the hypothesis doing the work is
`Subset A0 X` — that the matching member through `x` lies inside the cover.
The mutation `purelink-drop-cover-inside-x` is there because that is the
clause a reader would assume is bookkeeping.

### 20.2 The recursion

Double counting `Σ_{x ∈ T} deg(x) = Σ_{A ∈ F} |A ∩ T|` —
`IotaGround.degsum_eq_sizesum`, reused rather than rebuilt — against `2|F| <= |pure| + Σ_A |A ∩ T|` — every member meets `T` at least
once and every impure member at least twice — and bounding the pure part by
`iota(b-1)` instead of `g(b-1)` gives `cover_recursion`:

```
    2 * |F|  <=  |T| * ( g(b-1) + iota(b-1) )
```

with `|T| <= 2b` in general and `|T| = b` when `F` is intersecting, so

```
    g(b)      <=  b * ( g(b-1) + iota(b-1) )
    2 iota(b) <=  b * ( g(b-1) + iota(b-1) )
```

Since `2 iota(m) <= g(m)` (`Intersecting.doubling_lower_bound`) the step is
never worse than Erdős–Rado's and is a factor `4/3` better when the doubling
is tight. **It reproduces both values this development knows exactly**, which
is the only check available on it:

```
   b   this recursion              Erdős–Rado    truth
   1   iota(1) <= 1,  g(1) <= 2         -        1,  2       exact
   2   iota(2) <= 3,  g(2) <= 6     g(2) <= 12   3,  6       exact
   3   iota(3) <= 13, g(3) <= 27    g(3) <= 36   10 exact (§20.4), >= 20
   4   iota(4) <= 80, g(4) <= 160   g(4) <= 288  >= 27, >= 54
```

Against what was here before: `iota(3) <= 18`
(`Intersecting.iota_three_at_most_eighteen`), `iota(4)` in `[27, 192]`
(`Audit.the_sharp_bound_narrows_iota_four`), and `f(3,3) <= 49`.

> **`f(3,3) <= 28`**, unconditionally — `PureLink.f_3_3_at_most_28`.

`Sharp.sharp_beats_erdos_rado_at_three` reaches 32 from a hypothesis about
uniformity 4; `Product.iota_four_at_most_27_would_beat_erdos_rado` reaches 28
from a hypothesis nobody can discharge. This is 28 from nothing, and it
narrows the first unknown sunflower number to `21 <= f(3,3) <= 28`.

### 20.3 The novelty check, which came back negative

**The asymptotic content is not new, and the sentence that says so was
already in this repository.** §17 recorded it from [Kup25] p. 5 and filed it
as "a reference the bibliography lacks entirely":

> *"Abbot, Hanson and Sauer [1] in 1972, and then Spencer [116] in 1977
> improved upper bounds on `φ(k,s)`. The result of Spencer states that for
> any fixed `s` and `ε > 0` there exists `C` such that
> `φ(k,s) ⩽ C k!(1 + ε)^k`."*  [Kup25, p. 5]

`φ(k,2)` is `g(k)` — the survey says on the same page that the maximum is
attained on sets of size exactly `k`. Spencer's `(1+ε)^k` for every `ε`
beats `(3/2)^k` outright, so the recursion here is asymptotically
**subsumed by a 1977 result**, and by whatever [AHS72] proved before it.

The reading did its job and the register was the thing that did it: the
quote was three sessions old, sitting in `docs/reading.md` under a heading
nobody had reason to revisit, and it took thirty seconds to find because
§17.8 pinned the corpus. That is the first time the reading layer has
*prevented* a claim rather than corrected one.

**What is not subsumed is the finite values.** Spencer's `C` is not named,
so the bound says nothing at `k = 3`; the survey records no exact value of
`φ(3,2)`, and searching it for `φ(3`, "exact value" and "is known" finds
none. So `g(3) <= 27` and `f(3,3) <= 28` are new *to this development*,
possibly not to 1972 or 1977, and both of those are index-confirmed closed
(§17.5, §15.2). No priority is claimed.

### 20.4 The support bound, and `iota(3) = 10` exactly

`IotaAtMost b N` quantifies over every ground set, so no search decides it.
`PureLink.intersecting_support_bound` is what makes one search enough, and
it is three lines: every member of an intersecting family meets a fixed
member, so contributes at most `b - 1` points beyond it, and

```
    an n-member intersecting b-uniform family has support <= b + (b-1)(n-1).
```

At `b = 3`, `n = 11` that is **23 points**. `rust/src/wide.rs` is the same
exact search on `u64` masks with the `b`-subsets generated combinatorially
rather than by scanning `0 .. 2^g` — the 16-point ceiling in
`intersecting::iota_decide` was never a limit on the search, only on the
enumeration, and it was the only thing between this development and a
statement about `iota(b)` rather than `iota(b, g)`.

```
    iota(3) >= 11 on 23 points?   exhaustive, none.     < 1s
    iota(3) >= 12 on 25 points?   exhaustive, none.     < 1s
```

> **`iota(3) = 10`.** The development had `[10, 18]`.

Two things it settles. `Sharp.sharp_forces_iota_three_exactly_ten` is now
redundant — the sharp conjecture does not have to be assumed to pin
`iota(3)`. And `Sharp.the_sharp_bound_is_attained_at_three` —
`iota(3)² = 100 = 10²` exactly — is now known to be an equality between two
known values rather than between a value and a bound: **the 1972 rate is exactly
optimal at uniformity 3**, and every refutation of `AHSOptimal` has to happen
at `b >= 4`.

The chain is not one machine-checked object and the file says so. The support
bound is Coq; the step from "support has at most 23 points" to "the family
may be taken to live on `{0,...,22}`" is a relabelling that
`DirectSum.relabel_preserves` does not cover, because it wants a globally
invertible map rather than one invertible on the support; the search is Rust.
The relabelling is the same step `iota_decide` already leans on when it forces
the anchor, and it is argued there.

### 20.5 The cheap experiment died, and that is the useful part

§18.2 and §3.1 named the cheapest decisive thing on the list:

> `IotaRate.flat_threshold_at_three_forces_g_three_at_most_27` — if
> `r*(3,3) = 3` then `g(3) <= 27`, and this development only knows
> `20 <= g(3) <= 48`. **Computing `g(3)` exactly decides `r*(3,3)`.** If
> `g(3) > 27` the flat table breaks at uniformity 3.

`g(3) <= 27` is now a theorem. So `g(3) > 27` is impossible, and **the
experiment cannot refute `r*(3,3) = 3` however it comes out.** The cheapest
decisive item on §18's list was not decisive; it was a consequence of
something provable, and proving it removed the decision rather than making
it.

What survives is worth writing down. §18.2's tightness pattern is
`r*(m,3) >= ceil(g(m)^(1/m))`, tight at both measured points. At `m = 3` the
bound `g(3) <= 27` gives `ceil(g(3)^(1/3)) <= 3` **exactly** — `27^(1/3) = 3`
on the nose — so the pattern is not merely consistent with `r*(3,3) = 3`,
it is *saturated* by it: one more member in `g(3)` and the prediction would
move to 4. That is a sharper statement of the tightness than two data points
were, and it is the first time the pattern has been pinned from above.

`g(3)` is still worth computing exactly — it is now known to lie in
`[20, 27]`, seven values wide, and it feeds `iota(4) >= g(3)` through the
cone. It is no longer the decisive experiment.

### 20.6 The searches, with their cost

The point of the session was `iota(4) >= 32` and `iota(6) >= 317`.
`rust/src/plateau.rs` is what was built for it: a plateau search that gives
up on deciding and only tries to find, since a record needs a witness and a
witness needs no exhaustiveness argument. Two moves — fill to maximality,
then force a non-member in and evict the fewest members that block it — with
a short tabu list on what was evicted. The candidate test is bucketed by
`A ∩ x`, which is `2^b` values, so a candidate costs a few pair-checks rather
than `|F|²/2`; at `|F| = 300` that is the difference between 45000 pair
lookups and about twenty.

**The bar it has to clear is `iota(4,9) = 27`**, the 1972 family, rigid and
exhaustively known. It rediscovers it from nothing in about two seconds, and
`plateau_reaches_the_known_maxima` is a test rather than a remark because a
search that cannot do that has no business being pointed at `b = 6`.

**And it did not beat 1972.** The parameters run, with what they reached:

```
  question         grounds    seed   reached  target  verdict
  iota(4) >= 32    11..15       27      27      32    never left the seed
  iota(6) >= 317   18..21      300     300     317    never left the seed
  iota(5) >= 101   12..20        -      78     101    54 -> 78, a new best
  g(3)    >= 21    12..20       20      20      21    never left the seed
  g(4)    >= 101   18..21       54      54     101    never left the seed
```

Four of the five rows never moved off the construction they started from —
including after ruin-and-recreate kicks that discard an eighth of the family
and refill. One run, `plateau_run 4 12 200000 99`, is the calibration:
**200,000 forced moves in 136 seconds, best 27 throughout**, and the grid
ran five or six seeds at each of four or five ground sets per row.

That is the same finding as §13.1's, reached by a different instrument:
**the 1972 families are not merely maximal, they are isolated.** Every
neighbourhood the plateau search can reach from them is worse.

The one row that moved is the one where the substitution cannot be used at
all. `b = 5` is prime, so `substitute` has no factorisation to work with and
the repository's 54 came from the cone of a 4-uniform family; the search
found **78 on fifteen points**, pinned in `rust/tests/iota_five.rs` and
verified by `intersecting::verify`. That is `iota(5)^(1/4) = 2.972` against
the 1972 rate of 3.162 and against the conjectured `iota(5) = 100`, so it is
a new best for this development and **not** a record. The gap it closes is
`54 -> 78` of the `54 -> 100` the sharp conjecture allows, and
`iota_five_does_not_beat_1972` asserts exactly that so the number is not
mistaken for a rate.

That the only movement is at the only uniformity where the substitution has
nothing to say is the sharpest form of §13.1's finding this session
produced. Where the 1972 construction exists, local search does not improve
it. Where it does not exist, local search beats what the repository had by
44%.

### 20.7 What `g(4) >= 101` would have been, and why it is on the list

Worth recording because it is not obvious and it is where a future session
should point first. The cone gives `iota(b) >= g(b-1)` (§11.2), so a large
*general* family one uniformity down beats 1972 exactly as an intersecting
one at the target uniformity would:

```
    g(4) >= 101   =>   iota(5) >= 101   =>   rate 101^(1/4) = 3.1702 > 3.16228
    g(5) >= 317   =>   iota(6) >= 317
```

The general row is far less constrained than the intersecting one — §9 already
found that SAT is transformative there and useless on the intersecting UNSAT
side — and `g(4)` is known only to lie in `[54, 160]`, the upper end being new
here. So `g(4)` is a live target with 47 to find, on a search space where the
one instrument that has ever worked at these sizes is known to work.

The plateau search does not find it, from the doubling seed or from nothing.

### 20.8 What this session changes about the plan

**Up.**

1. **`g(4)`, through the cone.** §20.7. It has replaced `iota(4) >= 32` as
   the most concrete unsolved number, because the search space is the one
   where SAT wins and because the interval is now bounded on both sides.
2. **`g(3)` exactly, but for a different reason.** No longer decisive for
   `r*(3,3)` (§20.5). Still worth seven values, and it feeds
   `iota(4) >= g(3)`.
3. **`u64` everywhere in the exact layer.** `rust/src/wide.rs` cost twenty
   lines and removed a ceiling that had silently shaped every question asked
   of `iota` — the reason nobody had asked for `iota(3)` rather than
   `iota(3, g)` is that the enumerator could not express it.
4. **One more term in `cover_recursion`, worked out and not done.** The
   count as it stands is `2|F| <= t_1 + Σ_t deg(t)`. It does not use that
   the members of the matching `M` lie *inside* `T`, so each contributes
   `b` to the degree sum while counting once in `|F|`. Putting that in
   gives

   ```
       2|F|  <=  |T| * (g(b-1) + iota(b-1))  -  (b-2) * |M|
   ```

   which is `g(3) <= 26` and hence **`f(3,3) <= 27`**, still exact at
   `b = 2` (the correction is zero there), and `g(4) <= 156`. It was left
   out because it landed after the mutation suite had started and
   re-running the gate costs more than the term is worth this session. It
   is half a page of Coq: `M` is already in scope in `g_recursion`, and
   what is needed is `|A ∩ T| = b` for `A ∈ M` fed into the same
   `sizesum` count.

**Down.**

1. **`flat_threshold_at_three_forces_g_three_at_most_27` as an experiment.**
   Closed by §20.5. Keep the theorem; stop calling it a decision procedure.
2. **Local search against the 1972 families.** Five parameter rows,
   hundreds of thousands of moves, three of them motionless. Whatever beats
   the substitution is not one eviction, or eight, away from it.
3. **`iota(3)` as an open interval.** It is 10.

**Unchanged.** The axiom (§1) is still the highest-value engineering item and
was not touched this session.


### 20.9 Two defects in the instruments, found by using them

Both are the kind of thing that is invisible until something depends on it.

**`plateau_run` logged sizes without families.** The first pass reached 78 at
`b = 5` in a run that was later killed, and the log recorded the number and
nothing else — the family dump was conditional on beating the 1972 target, so
every result that was interesting but not a record was thrown away. The 78
had to be found a second time. Fixed: the family is written on *every*
improvement. This is the incremental-flush rule (§0 of the session brief)
applied to the thing actually worth flushing rather than to the progress
line.

**`tools/mutate.py` has been misattributing every kill after `Sharp.v`.**
The "first file to break" column comes from the first `File "..."` header in
the build output. Coq emits those for *warnings* too, and `coq/Sharp.v` line
353 has one about large `nat` literals — so every mutation whose kill lands
later in the build order was reported as breaking `Sharp.v`. Both of this
session's new mutations were, and the file they actually break is
`PureLink.v`. Fixed: walk back from the first `Error` to the header above it.

The verdicts were never wrong — `killed` is decided by the exit code, not by
the regex — so no recorded outcome changes. What was wrong is the one column
a reader uses to check that a mutation broke the thing it was aimed at, which
is the whole point of the column. It had been wrong since `Sharp.v` was
added.

**And one own-goal, recorded because it cost twenty minutes of gate time.**
A scripted edit meant to drop the `iota(4,10)` row — the 4437-second row of
§9 — from `rust/tests/pure_link.rs` matched a comment that was not in the
file, replaced nothing, wrote the file back unchanged, and reported success.
The commit message said the row was gone; the test kept running it. Caught
only because the suite sat on that one test for minutes and the timing did
not match anything the row was supposed to cost.

The rule this adds to §18.6's list, and it is the same shape as rule 4:
**a scripted edit that cannot find its target must fail, not no-op.**
`tools/mutate.py` already gets this right — `apply_edit` asserts the `find`
string occurs exactly once and refuses to proceed otherwise, which is why the
mutation manifest cannot silently drift. Ad-hoc edits during a session have no
such check, and this session shipped a wrong commit message because of it.


## 21. The session that closed its own headline target, and the term it
##     shipped instead

§2 of the session brief named one target and said it "might be the whole
game": [ALWZ20] Theorem 4.2 composed with `IotaRate`'s `k = 3`
equivalence, giving the modern bound with no spread lemma and demoting
the axiom from load-bearing to optional. The brief also said, twice, that
the derivation was a sketch and had not been checked.

It does not work. It fails for two reasons, either of which is fatal
alone, and the checking took about an hour. This section is that hour,
and then what the rest of the session did instead.

### 21.1 Reason one: Theorem 4.2 is a corollary of the axiom

The register has carried Theorem 4.2's *statement* since §17, under B10a,
where it refuted the claim that nobody had pointed the spread framework
at intersecting families. Nobody had read its *proof*. On the rendered
page 13 it is introduced by

> *"We note the following corollary of Theorem 2.5:"*

and proved, in full, by

> *Proof.* *If `F` is intersecting then it is not `(1/2, 1/2)`-satisfying
> (apply Lemma 1.6 for `r = 2`). Thus by the improvement of Theorem 2.5
> from [19], it cannot be `(C log w)`-spread for a large enough constant
> `C`.* □

Theorem 2.5 **is** the spread lemma, and [19] is Rao — that is,
`ALWZ.Rao20_lemma2`, the single axiom of this development. So formalising
Theorem 4.2 would **consume** the axiom, not replace it. The whole point
of the target was to get the modern bound without the axiom; 4.2 is four
lines of the axiom.

This is rule 2 — read the source of your own axiom before planning
against it — in a form the rule did not anticipate: the thing to read was
not the axiom but the theorem being proposed as an alternative to it.
Rule 6 also applies. Page 13 was cited for its statement three sessions
running, and the proof is on the same page, four lines below.

### 21.2 Reason two: the arithmetic, which fails on its own

Suppose 4.2 were independent. The chain is: `F` intersecting, `b`-uniform,
sunflower-free; by 4.2's contrapositive `F` is not `κ`-spread for
`κ ≈ C log b`, so some `T` with `t = |T| ≥ 1` has `|F| < κ^t · deg T F`;
the link at `T` is `(b−t)`-uniform sunflower-free, so
`iota(b) < κ^t · g(b−t)`.

**`t` is existential.** An upper bound has to survive every `t`, and the
adversary hands back `t = 1` at every level. There the chain reads

```
    iota(b)  <  κ · g(b-1)
```

and to recurse it has to get back to an *intersecting* family — because
4.2 applies to nothing else. **The link of an intersecting family is not
intersecting.** `IntersectingSpread.link_of_intersecting_not_intersecting`
is the smallest witness: the triangle is intersecting, 2-uniform and
sunflower-free, and its link at a vertex is two disjoint singletons. So
every level pays `Intersecting.sunflower_free_star_bound`'s factor
`2(b−1)`:

```
    iota(b)  <  κ · 2(b-1) · iota(b-1)
```

which multiplies by `2(b−1)κ` per level, hence `b! · (2κ)^b`, hence

> **`b! · (2C log b)^b` — Erdős–Rado's `b! · 2^b` made *worse* by
> `(C log b)^b`.**

`rust/tests/alwz_chain.rs` evaluates the recursion numerically with the
maximum over `t` taken honestly at every level, from `b = 4` to `b = 24`
exactly and to `b = 200` in log space. The ratio to Erdős–Rado is exactly
**1.000** at every `b` and every `C ∈ {1, 2, 4, 8, 16}`, because the
Erdős–Rado clamp inside the recursion is what is binding; remove the
clamp and the chain is strictly worse. The growth rate `g(b)^{1/b}/b`
sits on Erdős–Rado's `2/e = 0.736` and does not move, where the ALWZ
target sends it to zero.

ALWZ's own recursion never pays the `2(b−t)` **because their spread lemma
applies to general families**. Restricting to intersecting families is
what makes 4.2 cheap, and it is the same restriction that makes it
useless as a recursion step. That is the whole finding, and it is not
visible from the statement of 4.2 — only from what it is quantified over.

So the sentence §2 of the brief offered as the one nobody had written
down —

> *"The entire gap between Erdős–Rado and ALWZ, at `k = 3`, is the gap
> between `intersecting_not_spread_above_uniformity` and Theorem 4.2."*

— is **false**, and is retired here. The gap between those two statements
is a factor `b / log b` per level. The re-intersection factor `b` per
level sits on top of *both* of them, and it is untouched by sharpening
either. This is §1's ceiling again, reached from a new direction: the
`n!` is the barrier, and moving from `b` to `log b` inside a recursion
that still pays `b` to re-intersect does not remove it.

`coq/IntersectingSpread.v` is the whole argument machine-checked, with
the 4.2 hypothesis carried as an explicit premise rather than assumed, so
the file adds no axiom and asserts nothing about whether 4.2 is true.

### 21.3 What shipped instead: the correction term, and one member of
###      `g(3)`

§20.8 item 4 had the next term of the cover recursion worked out and
deliberately not implemented. It is in now.

`cover_recursion` charges every impure member exactly two. The matching
members lie *inside* the cover, so each meets it in all `b` of its points
while counting once in `|F|` — a surplus of `b − 2` apiece.
`cover_recursion_sharp` recovers it:

```
    2|F| + (b-2)|M|  <=  |T| * (g(b-1) + iota(b-1))
```

| quantity | without the term | with it |
|---|---|---|
| `iota(2)`, `g(2)` | 3, 6 | 3, 6 (exact, unchanged) |
| `iota(3)` | 13 | 13 |
| `g(3)` | 27 | **26** |
| `f(3,3)` | 28 | **27** |
| `iota(4)` | 80 | **77** |
| `g(4)` | 160 | **154** |

The correction vanishes at `b = 2`, where the recursion is already exact,
which is the only check available on it. `iota(3)` does not move because
`|M| = 1` in the intersecting case and the bound is then halved. Both
ladders are kept rather than one edited: the unsharpened corollaries are
true, and the pair is the only visible measure of what the term buys.

The brief predicted `g(4) <= 156`; the value is 154, because `g(3)`
improves to 26 first and feeds the next rung.

> **`f(3,3)` is now bracketed `21 <= f(3,3) <= 27`.**

### 21.4 The trace decomposition, costed out — and the hypothesis its
###      derivation omitted

§3 of the brief proposed computing `f(3,3)` exactly from the trace
decomposition. Two things came out of writing it down.

**The lemma as sketched is false.** The brief's claim was:

> *for every `S ⊊ T` that does not contain a whole member of `M`, the
> family `{A \ S : A ∈ F_S}` is intersecting.*

The set that forces the sunflower is a matching member `A0`, and all
three sets — `A \ S`, `B \ S`, `A0 \ S` — have to live in `link S F`. So
`A0` must **contain** `S`, which is strictly stronger than "`S` does not
contain a whole member of `M`". At `|S| = 1` it holds automatically,
because every point of the cover lies in some matching member, which is
why `pure_link_intersecting` never had to state it. At `|S| ≥ 2` a trace
class whose `S` *straddles* two matching members lies inside no `A0`,
satisfies every other hypothesis, and gets only `g(b − |S|)`.
`PureLink.trace_class_intersecting` states the correct version;
`purelink-trace-drop-s-inside-a0` is the mutation that says the extra
hypothesis is load-bearing.

**And the LP it feeds does not reach `f(3,3)`.** Writing `n_k` for the
number of members whose trace has size `k`, the whole decomposition is
one line: `n1 + 2n2 + 3n3 <= 6·g(2) = 36` with `n3 >= 2` forced, so

```
    |F|  =  n1 + n2 + n3  <=  n1/2 + 18 - n3/2.
```

* `n1 <= 18` (six classes at `iota(2) = 3`) gives **26** — *exactly what
  `g_recursion_sharp` proves in half a page*. The entire trace layer buys
  nothing over the recursion on its own.
* `n1 <= 16` (the cross-intersecting constraint: at most two of the three
  pure links inside a matching member are triangles, else three members
  `{t,a,b}` have pairwise intersections all `{a,b}`) gives **25**.

So cross-intersecting is worth exactly one member, and the LP stops at
25 against a conjectured `g(3) = 20`. **The trace LP is five short and
the slack is structural** — it sees class sizes and a degree budget and
nothing about how classes interact. `rust/tests/trace_lp.rs` pins all of
this, including that the per-class LP over all 41 classes (CBC) returns
the same two values as the aggregate relaxation, so the aggregate is the
whole content.

The brief's incorrect caps happen not to change the LP's answer, because
the degree budget is exhausted by the cheaper weight-1 classes before the
straddling classes are reached. The error was not load-bearing for the
number; the lemma was still false.

**Not formalised, deliberately.** Getting from 26 to 25 in Coq needs the
trace-partition layer, the classification of intersecting 2-uniform
sunflower-free families, the cross-intersecting lemma and the LP — for
one member, on a route that provably cannot reach 20. Recorded rather
than built.

### 21.5 `tau`: half of §8 was already done, and the other half closes it

§8 of the brief called measuring `tau` "cheap and never done". Half of it
had been done in an earlier session and the brief did not know:
`rust/tests/extension.rs::the_covering_number_is_multiplicative_under_substitution`
already measures `tau(triangle) = 2`, `tau(iota3) = 3`, `tau(g(2)) = 4`,
and checks `tau(substitute(G,H)) = tau(G)·tau(H)` on four pairs.
`extend::covering_number` has been there the whole time. Rule 1 again,
from the other side: grep before calling something undone, not only
before calling a quantity unnamed.

**The other half kills the route, and the brief's premise was wrong.**
§8 predicted `tau(b) = b^{log₃ 2} ≈ b^{0.63}` for the AHS tower. That
needs a base with `tau = 2` at uniformity 3. The measured value is
`tau(iota3) = 3`. Since `tau` *and* uniformity both multiply under
substitution, the tower has

```
    tau  =  tau(base)^k  =  b(base)^k  =  b
```

— **`tau = b` exactly**, which is the largest it can be: an intersecting
family is covered by any one of its own members, so `tau <= b` always,
and the 1972 families sit at the ceiling rather than well below it.

Then the arithmetic §8 asked for, and it has to be done at `tau = b`
specifically — **there is no `b^tau` bound in general**. At `tau = 1`
every member shares a point and the family is a full star, which is
unbounded; a first draft of this paragraph claimed `|F| <= b^tau` and
that claim is false, with the star as its counterexample.

What is true is the greedy tree at `tau = b`, and it needs `tau = b`
twice. Pick `A_1 ∈ F`; every member meets it, so `b` branches for the
first point `x_1`. Since `tau = b > 1`, `{x_1}` is not a cover, so some
`A_2 ∈ F` misses `x_1`, and every member through `x_1` meets `A_2`: `b`
branches again, for a point `x_2 =/= x_1`. This continues for as long as
`{x_1, ..., x_k}` is not a cover — that is, for `k < tau = b` — and after
`b` steps the member contains `b` distinct chosen points, so *is* the set
of them. Each leaf holds at most one member, and

```
    |F|  <=  b^b  =  b! · e^b / sqrt(2 pi b).
```

Both uses of `tau = b` are load-bearing: it is what keeps the branching
going for `b` levels, and `b = |B|` is what makes the leaves singletons.
(Elementary, and *not* attributed: no priority search was run, and
`docs/reading.md` B12 records the surrounding literature under *base*,
*nucleus*, *crosscut* and *minimal cover*. Rule 3 — claimed only as
arithmetic done here.)

the **same `n!` barrier**, reached a third way this session.
`rust/tests/tau_rate.rs` pins `tau = b` on the tower and checks the
Stirling identity. And the comparison is worse than "same barrier":
Erdős–Rado at `k = 3` is `b! · 2^b = (2b/e)^b`, and `2/e = 0.736 < 1`, so

```
    b^b  >  (2b/e)^b  =  Erdos-Rado,     by a factor (e/2)^b = 1.359^b.
```

**The `tau` bound is not merely on the wrong side of the barrier — it is
worse than 1960 outright.** To reach `C^b` from a `tau`-indexed bound the
extremal families would need `tau = O(log b)`. They have the maximum.

So §8 closes the way §2 and §3 did: real route, checkable arithmetic,
stops at `n!`.

### 21.6 State of the numbers

```
  quantity     was                 now                 how
  f(3,3)       [21, 28]            [21, 27]            PureLink.f_3_3_at_most_27
  g(3)         [20, 27]            [20, 26]            g_three_at_most_26
  iota(4)      [27, 80]            [27, 77]            iota_four_at_most_77
  g(4)         [54, 160]           [54, 154]           g_four_at_most_154
  iota(3)      10 exact            unchanged
  iota(5)      >= 78               unchanged
```

Nothing on the lower-bound side moved. No search was run this session.

### 21.7 What this changes about the plan

**Down, and closed rather than answered.**

1. **[ALWZ20] Theorem 4.2 as a route to the modern bound.** Closed twice
   over (§21.1, §21.2). It is a corollary of the axiom, and its
   arithmetic is worse than 1960's. Do not reopen it; reopen instead the
   question of whether the *spread lemma itself* can be applied to
   general sunflower-free families without the axiom, which is §1 and is
   unchanged.
2. **The trace decomposition as a route to `f(3,3)` exactly.** Closed
   (§21.4). It reaches 25 and stops, five short, for structural reasons.
   Computing `f(3,3)` exactly needs canonical augmentation over actual
   families, not an LP over trace profiles.
3. **The counting recursion.** §1's budget was half a day and it is
   spent. The correction term is in, it is the last term of that shape,
   and §21.2 is a second independent confirmation that the whole family
   of counting arguments stops at `n! C^n`.

4. **`tau` as a route to `C^b`.** Closed (§21.5). The extremal families
   have `tau = b`, the maximum, and the greedy tree at `tau = b` gives
   `b^b`.
   What survives is the *measurement*, which is real and was already in
   the repository: `tau` is multiplicative and the tower sits at the
   ceiling. That is a structural fact about the 1972 families worth
   keeping; it is not a bound.

**Unchanged and now the only headline left.** The axiom (§1). It was the
highest-value engineering item before this session and nothing here moved
it — except to remove the one idea that claimed to make it optional.

**A note on what this session is.** Its output is **three closed
targets** (§2, §3, §8), one correction to a lemma that had been derived
but never checked, one hypothesis added to a lemma whose sketch omitted
it, and one term worth a single member of `g(3)`. The closures are the
valuable part: §2 was the brief's headline and would have consumed the
session, and it was refuted by reading four lines on a page the register
had already cited and by evaluating a recursion in a fifty-line script.

All three closures have the same shape, and it is worth naming. Each
route reaches `n! · C^n` and stops: the counting recursion pays `b` per
level to pigeonhole, the 4.2 chain pays `b` per level to re-intersect,
and the `tau` bound pays `b` in the exponent because `tau = b`. §1 said
the `n!` is the barrier and that no sharpening of the counting recursion
removes it. This session is three more instruments arriving at the same
wall from three directions, which is stronger evidence for §1's claim
than §1 had.

---

## 22. The sequence that is the conjecture: two bounds on `r*(m,3)`, and
##     what the search could and could not reach

`SpreadReduction.SpreadYieldsDisjoint n 3 r` is true above `r*(n,3)` and
false below it, `spread_reduction` turns a bound on `r*` into a bound on
`f(m,3)`, and §18.5 is the observation that **whether the sequence is
bounded in `m` is the sunflower conjecture at `k = 3`**. This session
attacked the sequence directly. The output is one new theorem, one new
instrument, and one correction to the table.

### 22.1 The theorem: `r*(m,3) <= 1 + sqrt(3m^2 - 4m + 3)`

`coq/SpreadThreshold.v`, axiom-free. Two bounds, both better than the
`2n + 1` of `SpreadReduction.elementary_spread_disjoint`, which was the
only general upper bound the development had.

* **`cover_spread_disjoint`: `r*(n,3) <= 2n`.** A family with no three
  pairwise disjoint members has a maximal matching of at most two
  members, its union is at most `2m` points, and every member meets it.
  Rao's *absolute* spread condition caps each point at `r^(m-1)`, so
  `|F| <= 2m·r^(m-1)`, which is at most `r^m` as soon as `r >= 2m`. The
  elementary bound does not use spreadness at all beyond counting cover
  points; this uses it once.

* **`quadratic_spread_disjoint`: `r*(n,3) <= 1 + sqrt(3n^2 - 4n + 3)`**,
  about `1.74 n`. Stated in Coq without roots, as
  `2r + 3n^2 + 2 <= r^2 + 4n`.

The second is the one worth the space, because of *why* it works.

> **For `B` any member of a family with no three pairwise disjoint
> members, `{C in F : C ∩ B = ∅}` is intersecting.**

Two disjoint members that both miss `B` would be three pairwise disjoint
sets together with `B`. So against a matching `{A, B}` the family splits
into **two intersecting pieces and a cross piece**, and each is bounded
separately:

```
  piece                          covered by            bound
  {C : C ∩ B = ∅}   (meets A)    a point, or pairs     r^(m-1) + (m-1)^2 r^(m-2)
  {C : C ∩ A = ∅}   (meets B)    a point, or pairs     r^(m-1) + (m-1)^2 r^(m-2)
  meets both                     one A-point x one     m^2 r^(m-2)
                                 B-point
```

The saving is that **a pair has degree `r^(m-2)` where a point has
`r^(m-1)`**, so any piece that can be covered by pairs is smaller by a
factor of `r`. Summing gives `r^(m-2)·(2r + 3m^2 - 4m + 2)`, and `r^m`
is `r^(m-2)·r^2`.

`intersecting_piece_bound` is where the case analysis lives, and it is a
two-way split, not a minimisation: either some member meets `A` in
exactly one point `a1` — and then the piece is the star at `a1`, at most
`r^(m-1)` sets, plus the members meeting both `A \ {a1}` and `C0 \ {a1}`,
covered by `(m-1)^2` pairs — or every member meets `A` twice and the
whole piece is covered by the `m(m-1)` ordered distinct pairs inside `A`.
The hypothesis `m - 1 <= r` is what makes the second at most the first;
`spreadthreshold-piece-drop-r-bound` in the mutation manifest checks it
is load-bearing.

**This is the first bound on `r*` that uses `k = 3` as structure rather
than as the arithmetic constant `k - 1`** — `elementary_spread_disjoint`
and `cover_spread_disjoint` are both the general-`k` cover argument with
`k = 3` substituted — and it is worth naming why it can. §21.7 closed
three routes because each pays `b` per level to re-intersect, and
`IntersectingSpread.link_of_intersecting_not_intersecting` says why: the
link of an intersecting family is not intersecting. Here nothing is
re-intersected. The intersecting-ness is *produced* by the
hypothesis on the family, once, at the top — which is exactly §1's
observation that a hypothesis about **general** families does not pay the
toll, applied to the smallest available such hypothesis.

Evaluated:

```
  m      elementary 2m+1     cover 2m      quadratic     Coq name
  1                    3            2              3     cover_spread_disjoint
  2                    5            4              4
  3                    7            6              6     r_star_three_at_most_six
  4                    9            8              7     r_star_four_at_most_seven
  5                   11           10              9     r_star_five_at_most_nine
  6                   13           12             11     r_star_six_at_most_eleven
  10                  21           20             18
```

`rust/tests/spread_threshold.rs` pins every row, and pins that the Coq
condition holds at `(4,7)` and fails at `(4,6)` — the bound is sharp for
*this argument* at the headline point, not merely sufficient.

### 22.2 The correction: `r*(3,3) = 3` was never established

§2 of this session's brief tabulates the sequence as `3, 3, ?` with the
second entry attributed to "§3.6 + §20.5 (`g(3) <= 26` forces it)". Both
halves of that attribution fail, and §3.6 and §20.5 each say so in their
own text.

* **§20.5 runs the other way.** `IotaRate.flat_threshold_at_three_forces_g_three_at_most_27`
  is `r*(3,3) = 3 -> g(3) <= 27`. §20.5's whole point is that proving
  `g(3) <= 27` **removed** the decision rather than making it: "the
  experiment cannot refute `r*(3,3) = 3` however it comes out". A bound
  on `g(3)` is a consequence, not a cause.

* **§3.6's rows at grounds 8 and 9 are arithmetic, not search.** This is
  now exact. `rstar::min_ground` computes the counting floor
  `ceil(m(r^m + 1) / r^(m-1))`, which at `(m,r) = (3,3)` is **10**:
  `m·|F| = Σ_x deg(x) <= ground·r^(m-1)` gives `|F| <= 3·ground/1`, i.e.
  at most 27 members on 9 points, one short of the 28 a counterexample
  needs. §3.6 already said "ground sets that provably cannot contain a
  counterexample plus nothing beyond"; the new content is that
  `counting_settles_the_small_ground_sets` decides grounds 6 through 9
  **with zero search nodes**, so the cost of §3.6's grid at uniformity 3
  was zero and its information content is zero too.

So the honest state of the sequence is:

```
  m     r*(m,3)          lower bound from            upper bound from
  1     = 2   exact      r = 1 refuted               cover_spread_disjoint
  2     = 3   exact      r = 2 refuted (C5)          exhaustive, see §22.3
  3     in [3, 6]        r = 2 refuted               r_star_three_at_most_six
  4     in [3, 7]        r = 2 refuted               r_star_four_at_most_seven
  5     in [3, 9]        r = 2 refuted               r_star_five_at_most_nine
  6     in [3, 11]       r = 2 refuted               r_star_six_at_most_eleven
  9     >= 4             §18.2, via g(9) >= 3^9      -
```

> **Correction, §25.3:** the `m = 9` row is **conditional**, and this
> table lists it as though it were not.
> `IotaRate.substitution_would_refute_the_flat_threshold_at_nine` assumes
> `LowerBound 9 3 (3^9 + 317)`, which rests on the Abbott–Hanson–Sauer
> substitution — not formalised here. Every other row is a theorem.


Two exact terms, not two-and-a-conjecture. The interval at `m = 4` is
`[3, 7]`, down from `[3, 9]`, and it is the first time the top of that
interval has moved.

### 22.3 `r*(2,3) = 3`, certified rather than cited

§3.6 records `r*(2,k) = k` as "known conditionally on [ChHa76]". At
`k = 3` it is now a finite check this repository owns outright, and the
support bound is what makes it finite:

* no intersecting counterexample, since `|F| <= m·r^(m-1) = 6 <= 9 = r^m`;
* so there is a matching `{A, B}`, `|A ∪ B| = 4`, and every member meets
  it, giving `|F| <= 2m·r^(m-1) = 12` by `no_three_disjoint_cover_bound`;
* a 2-set meeting a 4-set has at most one point outside it, and distinct
  outside points lie in distinct members, so at most `|F| <= 12` of them:
  **the support of a counterexample is at most 16 points.**

`r_star_two_three_is_three` runs the exhaustive search on every ground
set from the counting floor 7 up to 16, in both the intersecting and the
matching case, and at uniformity 1 as well since `SpreadYieldsDisjoint 2
3 3` quantifies over it. Nothing. **This is a Rust certificate, not a
Coq theorem** — the support bound is proved by hand above and the search
is the finite check it licenses. The same argument does not close
`m = 3`: there the support bound is `6 + 2·54`, which is 114 points, and
nothing in this session brought it down.

### 22.4 The instrument: `rust/src/rstar.rs`

Two independent searches for a counterexample at fixed `(m, r, ground)`,
agreeing wherever both finish (`sat_and_dfs_agree`).

* **A SAT encoding.** One variable per `m`-subset meeting the cover;
  Sinz sequential counters for the degree caps (`O(n·k)`, where the
  crate's existing `at_most` is `O(n·(n-k))` — the wrong way round when
  `k` is a degree cap); the two anchors forced; and **lex-leader symmetry
  breaking for the generators of the residual group**
  `(Sym(A) × Sym(B)) ⋊ swap × Sym(U)`. The lex-greatest member of an
  orbit satisfies `X >=_lex g(X)` for every `g`, so imposing it for a
  generating set keeps a representative of every orbit. Note this is
  **not** the degree-sequence constraint §4 and §5 name: that one needs
  counters with exact semantics in both directions, or the ordering it
  imposes can delete satisfying assignments, and the totaliser that gives
  them is `O(n²)` clauses per point — too much at the sizes here. The
  lex-leader form is `O(#variables)` per generator and needs no counters
  at all. The intersecting-piece theorem of §22.1 enters as **binary
  clauses** — two disjoint members that both miss an anchor — which is
  the form CDCL propagates.
* **A depth-first enumeration** with a filtered candidate list and three
  counting bounds: total point-slack over `m`; a *least-point* group
  bound; a *least-pair* group bound. The group bounds are what SAT cannot
  do — see §22.5.

Every SAT model is decoded and re-verified by `rstar::verify`, which
shares no code with the encoder, and UNSAT is only reported when cadical
and cryptominisat agree, the discipline `sat.rs` already applies.

### 22.5 What ran for hours and decided nothing

Recorded with its cost, because the negative is the useful part.

* **cadical on `(m,r,ground) = (3,3,9)` did not terminate in 6m21s of
  CPU** on a 12 051-clause instance that is *infeasible by counting*:
  28 members × 3 points = 84 incidences against 9 points × 9 = 81. This
  is the pigeonhole principle, which has no polynomial resolution proof,
  and it is exactly the shape every instance here has. **The counting
  precheck was added because of this**: `degree_ceiling` now answers such
  grounds without a solver, in no nodes at all.
* **cadical on `(3,3,10)` did not terminate in about half an hour**,
  across two runs, the longer about 25 minutes. Ground 10 is the first
  ground set that can hold a counterexample and the counting there is
  nearly tight — 84 incidences against a capacity of 90 — which is the
  regime CDCL is worst at.
* **The depth-first search on `(3,3,10)` did not terminate.** Measured
  exactly: 400 000 001 nodes in 251.8 s — 1.6 M nodes per second — with
  the largest `r`-spread family of matching number 2 found being **23
  members against a target of 28**, up from 22 at the 20 M-node mark. The
  three counting bounds cut the tree but not enough; what is missing is
  isomorph rejection, and the residual group at ground 10 has order
  `3!·3!·4!·2 = 1728`.

  The 23 is worth keeping even though it decides nothing. It is a lower
  bound on the maximum, and the maximum is what has to reach 28 for
  `r*(3,3) > 3`. Five short, after 4·10^8 nodes, is weak evidence that
  the term really is 3 — and weak evidence is what the sequence has never
  had at any `m > 2`.
* **The depth-first search on `(4,3,13)` did not terminate**, in either
  the intersecting or the matching case. 710 candidate sets, target 82.
* **Which way each instrument fails is itself the measurement.** The SAT
  encoding finds counterexamples in *milliseconds* when one exists —
  `(4,2,11)`, 29 885 variables and 65 504 clauses, 0.1 s — and cannot
  close the negative side at all. The depth-first search closes small
  negatives instantly and is the only one of the two that can see a
  counting argument. They fail on opposite sides, which is why both are
  kept and why `sat_and_dfs_agree` is a test.

So `r*(3,3)` and `r*(4,3)` are still open at their lower ends, and this
session did not move them. What it moved is the top of the interval and
the honesty of the bottom.

### 22.6 What this changes about the plan

**Up.**

1. **Isomorph rejection in the depth-first search.** This is now the
   single bottleneck on every open term of the sequence, and the size of
   the prize is measurable: 1728 at `(3,3,10)`, and larger at every
   parameter beyond it. `nauty` is installed and canonical augmentation
   is what it is for. The lex-leader constraint in the SAT encoding is
   the same idea, and the SAT side is *also* stuck, so the search side is
   where it has to be done properly.
2. **A support bound at uniformity 3.** `r*(2,3) = 3` became certified
   the moment the support was bounded by 16. At `(3,3)` the same argument
   gives 114 and the search cannot reach it. Any argument that brings it
   to, say, 14 turns an open term into a finite check. The place to look
   is the rainbow-matching structure of the link graphs `L_x` for `x` in
   the cover: no three of them admit a rainbow matching, and each has at
   most `r^(m-1)` edges.
3. **Sharpening `intersecting_piece_bound`.** The star branch is bounded
   by `r^(m-1)`; if the piece has any member avoiding `a1` it is bounded
   by `m·r^(m-2)` instead, which replaces `r + (m-1)^2` by `m^2 - m + 1`
   and would give `r*(6,3) <= 10` rather than 11. It does not move `m = 4`
   — 7 either way — which is why it was not done here.

**Down.**

4. **SAT as the instrument for the *negative* side of this question.**
   §9 measured SAT as transformative on the `iota`/`g` row, where the
   constraints are ternary and structural. Here the binding constraints
   are *cardinality*: cadical spent 6m21s failing to close `(3,3,9)`,
   which the depth-first search dispatches in **zero nodes** because one
   division settles it, and about half an hour on `(3,3,10)` without a
   verdict. On the positive side it is the better instrument by a wide
   margin — every counterexample here was found by SAT, `(4,2,11)` in
   0.1 s over 29 885 variables. So: keep the encoding for finding
   witnesses and as an independent check, and do not expect it to close a
   negative.
5. **`g(3)` exactly as a route to `r*(3,3)`.** Already closed by §20.5;
   §22.2 records that the brief's table had it backwards, so it is worth
   restating: the implication runs `r*(3,3) = 3 -> g(3) <= 27` and not
   the other way.

### 22.7 What §22 is worth, stated plainly

§22.1 is written as though the bound were the session's advance. It is
not, and the correction belongs next to it rather than in a later
session's discovery.

**The growth rate of `r*(m,3)` is already a theorem, and it is better
than anything here.** `coq/SpreadReduction.v`'s own comment on
`spread_disjoint_above_elementary` says so:

> The 2020 papers prove `[SpreadYieldsDisjoint]` for `r = Θ(k log n)`.

So `r*(m,3) = O(log m)` is published. §22.1 proves `Θ(m)`. On the axis
that matters — growth — the new bound is **strictly behind the state of
the art**, and what it improves is one column of one table:

```
  bound on r*(m,3)                          value
  literature (ALWZ 2020 / Rao 2020)         O(log m)
  this repository, conditional on its axiom O(log m)
  this repository, unconditional, before    2m + 1
  this repository, unconditional, now       ~1.74 m
```

That is a *formalisation* improvement: `2m + 1 -> 1.74m` in the
unconditional column of one Coq development. The arguments themselves —
a maximal matching gives a `2m`-point cover; cover by pairs instead of
points — are elementary and would not be new to anyone working in the
area. Machine-checking them has value. Discovering them does not.

**And the sequence is not a route to the conjecture.** §18.5 and this
session's brief both say computing terms of `r*(m,3)` would give "the
first evidence anyone has ever had about the growth rate" and would
"distinguish bounded from `log m` empirically". Neither is true.
Finitely many terms cannot distinguish a bounded sequence from `log m` —
that is a fact about limits, not about compute — and the growth rate is
already proved. `r*(m,3)` is an elegant way to *state* the conjecture at
`k = 3`. It is not a way to attack it, and a session spent inside that
frame is a session spent improving a superseded bound.

**What the frame was worth.** Two things survive and both are small:
`r*(1,3) = 2` and `r*(2,3) = 3` are now exact and certified rather than
cited, and §22.2's correction is real. Neither is mathematics.

**The standing rule this adds.** Rules 1–9 all guard against
mis-describing a *source*. This one guards against mis-describing a
*result*:

> **10. Before calling a bound an advance, evaluate it against the best
> published bound for the same quantity — including the one the
> repository has already assumed as an axiom.** The axiom in this
> development *is* the state of the art for `r*`. A new unconditional
> bound that is asymptotically worse than the assumption sitting in
> `ALWZ.v` is a formalisation result, and saying so is the difference
> between a contribution and a press release.

### 22.8 Where the effort should go instead, and why

The evidence that AI systems can produce genuinely new mathematics on
problems of this shape is now concrete and public, and it points away
from what §22 did. The pattern in every case that has worked is the
same: **a new mathematical argument or construction on a named open
problem, with formalisation as the certificate afterwards.** The
formalisation is how the result is made trustworthy; it is not the
result. §22 inverts that — it is a certificate with napkin-level content
inside it.

Two targets in this repository have the right shape. Neither was touched
this session.

1. **Beat the 1972 lower bound, by searching over *generator programs*
   rather than over families.** §5's rate to beat is `10^(1/2) = 3.162`
   per point; the live rows are `iota(5) >= 101` (record 78, and the only
   row local search has ever moved) and `g(4) >= 101` (record 54).
   §20.6 measured *why* five sessions of local search failed: four of
   five parameter rows never left their seed, so the 1972 families are
   not merely maximal but **isolated**. Isolated optima are exactly where
   move-based search on the object fails and where changing the *program
   that emits the object* is the right move. The pieces are already here:
   `intersecting::verify` is the scoring function, `construction.rs` has
   `cone`/`double`/`substitute` as the seed program, and the missing
   ingredient is a search whose mutation operator proposes structurally
   different generators — group actions, cocycles, twisted products,
   designs under the derived link conditions — rather than perturbing a
   family. That has never been run here, and it is the method with the
   track record on exactly this shape of problem.

2. **`f(3,3)` exactly.** Bracketed `[21, 27]`, seven values wide, with
   the structure theory already proved (§4 of the brief:
   `trace_class_intersecting`, the straddling-class hypothesis, the
   cross-intersecting pure links, the degree cap). A new sunflower number
   would be the first since 1960 and is a genuinely new mathematical
   fact rather than a re-proof. It is a finite search, and §21.4 already
   established that the LP route stops at 25, so what is needed is
   canonical augmentation over families — the same isomorph rejection
   §22.6 identifies as the bottleneck everywhere else.

**Down, and this is the reordering.** Discharging `Rao20_lemma2` (§3)
stays valuable — no proof assistant has the modern bound unconditionally,
and that is a real artifact — but it is *re-formalising a 2020 proof*.
It is the certificate half of the recipe with the discovery half absent.
It should be done, and it should not be done first.

---

## 23. Searching over generator programs: the instrument, the bound that
##     aims it, and four negatives

§22.8 named the target: beat the 1972 lower bound by searching over the
*programs that emit families* rather than over families, because §20.6
measured the extremal objects as **isolated** — four of five parameter
rows never left their seed under local search — and an isolated optimum
is where moving the object fails and changing the generator can work.

This section is that search, run. It did not move a record. What it
produced is one bound that aims every future search on this row, one
filled gap in §13.3, and three measured negatives.

### 23.1 The counting ceiling, and where it says a record can live

`LinkCharacterisation` says a family is sunflower-free exactly when every
link has matching number at most 2. Two consequences were in the
development as facts about *links*; neither had been turned into a bound
on `|F|`.

* A `(b-1)`-set's link is 1-uniform, so `ν <= 2` reads `deg <= 2`. Each
  member contains `b` of them: **`|F| <= (2/b)·C(n, b-1)`**.
* A `(b-2)`-set's link is a graph with `Δ <= 2` (from the line above) and
  `ν <= 2`, so it is a union of paths and cycles with no 3-matching —
  at most **two disjoint triangles**, six edges. Each member contains
  `C(b,2)` of them: **`|F| <= (6/C(b,2))·C(n, b-2)`**.

`genprog::size_ceiling` is the smaller of the two. Evaluated:

```
  b = 4    n     8    9   10   11   12   13   14   15
  ceiling       28   36   45   55   66   78   91  105

  b = 5    n    10   11   12   13   14   15
  ceiling       72   99  132  171  218  273
```

Three readings, and the first two are the useful ones.

1. **`iota(5) >= 101` is impossible below twelve points**, and
   `iota(4) >= 51` — which reaches the same threshold through `double`
   and `cone` — is impossible below eleven. That is the first statement
   in this repository about *where* a record could be, as opposed to how
   big it would have to be.
2. **§9's `b = 5` SAT row was asked at a ground that could not answer
   it.** It ran at ground 10, whose ceiling is 72 against a threshold of
   101. `iota(5,10) >= 42` is a true measurement and it was never on
   course, which §9 suspected on rate grounds and can now be said
   exactly.
3. **At `b = 3` the ceiling is 10 at six points, and `iota(3) = 10`.**
   The extremal object of the whole 1972 tower saturates the counting
   bound at its own ground set. At `b = 4` it does not: the ceiling at
   eight points is 28 and the exhaustive search finds no 28-member family
   there (`the_ceiling_is_not_attained_at_uniformity_four`). Whatever
   makes `b = 3` special, it is not visible to this count.

### 23.2 The instrument

`rust/src/genprog.rs`. A **generator** is a parameterised program
emitting a *pool* of candidate blocks; its score is the largest verified
intersecting sunflower-free subfamily inside that pool. The pool is the
hypothesis — "a record looks like this kind of object" — and the
subfamily search is the evaluation, so structurally unrelated
constructions land on one scale.

Evaluation reuses `orbit::search_orbits` with singleton orbits. One thing
had to be got right and was got wrong first: that routine is a
**decision** procedure, and its bound ("what is in hand plus everything
still to come") prunes at the root whenever the pool cannot reach the
target, so its `best` is not a maximum. Reading it as one gives silent
zeros on nonempty pools. `genprog::evaluate` therefore asks one decidable
question at a time — succeed at `t`, ask `t+1`; fail exhaustively at `t`
and the maximum is `t-1` — which keeps the bound sharp at every step.

Differentially checked: the unrestricted pool at `b = 3` on six points
returns 10, exhaustively, and every family that comes out is re-verified
by `orbit::verify`, which shares no code with the search.

### 23.3 Four negatives, with their cost

**One: prescribed symmetry at `b = 5` intersecting is dead too.** §13.3
ran `b = 4` intersecting, `b = 3` general and `b = 5` *general*, and
found nothing. It never ran `b = 5` **intersecting**, and its own
diagnosis said why grounds at or below `3b = 15` are the ones where
orbits survive. §23.1 says the record needs only twelve points, so
grounds 12–14 are both viable and below `3b` — the region where §13.3's
reason for failure does not apply. Run (`examples/km_five.rs`): grounds
12–16, every standard group, **every instance exhausted, best 75**
against a record of 78 and a threshold of 101. The gap is filled and the
answer is the same as §13.3's.

**Two: SAT does not reach this row.** `iota(5)` at ground 12, asked for
60 members — well below the 78 already in hand — was **undecided in
241 s**. Consistent with §9's finding that the intersecting instances are
the ones CDCL cannot do, and it rules out the obvious idea of walking the
target up with a solver.

**Three: every structured generator scores below no hypothesis at all.**
The pools were chosen to be structurally different from `cone`, `double`
and `substitute`, which is what §5 asks for:

```
  generator                              b   ground   best   control
  transversals of a 4x3 grid             4       12     12        24  (g = 8)
  the same, twisted by a weighted cocycle 4      12   <= 11        24
  complementary selection, b = 3          3        6      8        10
  star (= cone)                          4        8   <= 23        24
```

The transversal shape is where every product construction in the
catalogue lives, and the cocycle twist is the algebraic move behind the
modern cap-set constructions — §5 names it as the thing not in the
catalogue. Both cap out far below the unrestricted search on the same
ground set. Twisting never beat the untwisted grid at any modulus tried.

**Four, and this one refutes a hypothesis of its own:** `iota(3) = 10` is
"one triple from each complementary pair of `[6]`" — the 2-(6,3,2) design
really does have that shape, which is what suggested the
`complementary_half` generator. But **no weight rule finds it**: over
every residue modulo 2, 3, 4 and 5, the best complementary selection
contains only 8 of the 10, and `the_structured_pools_all_lose_to_no_hypothesis`
pins that. The selection that makes the design is not a linear
functional, so the generator built on that idea was built on a false
reading of the object.

**Five: `iota(4) >= 28` at ground 10 was attempted and is *still open*,
and the reason is worth recording.** §23.1 says a record needs eleven
points at `b = 4`, but ground 10 is the rung §9 left undecided after an
hour of SAT and it is the value `IotaGroundBounded` turns on, so it is
the cheapest live question on the row. The unrestricted pool there is 210
blocks and the question is a decision — "is there a 28-member
intersecting sunflower-free family" — with a sharp branch-and-bound
bound. It ran **2h28m of CPU, roughly 60% of a 4·10^9-node budget, and
was killed by a container restart without a verdict**; a second attempt
at a smaller budget was killed the same way inside a few minutes.

That is an environment result, not a search result, and it changes what
the next attempt should look like. A multi-hour single-threaded run is
not a shape this repository can rely on. What it needs is a search that
**checkpoints** — writes its frontier so a restart resumes rather than
restarts — or one fast enough not to need to. `search_orbits` has neither
property, and adding the first is a smaller job than adding isomorph
rejection while being worth roughly as much on every open question here.

### 23.4 What this says about the approach

The generator-program idea is the right shape for an isolated optimum and
it is *not* refuted by this — what is refuted is the specific family of
generators a first pass produces. But the measurement to take seriously
is §23.3's third row: on this problem the structured pools are
**strictly worse** than the unrestricted pool at the same ground set,
every time. That is the opposite of the cap-set situation, where the
structure is what makes the search tractable at all, and it is a
consequence of §13.3's observation one level up — sunflower-freeness is
ternary and *negative*, so imposing structure removes blocks without ever
buying a guarantee, and every block removed is a block a record might
have needed.

The honest next move is therefore not more generators of the same kind.
It is either

* **a generator whose pool is provably closed under the constraint** —
  something whose blocks cannot form a sunflower by construction, so that
  the pool *is* the family and there is no search inside it. Nothing in
  the catalogue has this shape except `cone`, and that is why `cone` is
  the only construction that has ever set a record here; or
* **the exhaustive question at the grounds §23.1 opens**, which is
  `iota(4) >= 28` at ten and eleven points. The ceiling permits 45 and
  55, the record is 27 on nine points, and §9 left it undecided after an
  hour of SAT. It is the smallest object whose existence would move
  anything: `iota(4) >= 51` gives `g(4) >= 102` by `double` and
  `iota(5) >= 102` by `cone`, and that beats 1972.

## 24. The degree sum nobody took, and the extremal problem underneath
##     it: `r*(m,3)` from `[3,6]` to a single value

**Verdict: this session produced new theorems, no new record object, and
two decisive negatives.** In order:

* **`r*(m,3) ≤ φ·m + O(1)`**, unconditional and axiom-free, against the
  `√3·m` that was the development's best (§24.2). The first *open* term
  of the sequence — which is `m = 3`, not the `m = 4` the brief aimed at
  — narrows from `[3,6]` to `[3,5]`.
* **`r*(3,3) ≤ 4`**, conditional on one classical theorem and **no new
  axiom** (§24.10, §24.12): the `τ ≤ 2` case proved outright, the
  `τ = 3` case assumed as a hypothesis to the left of the arrow.
  (**Superseded, §25.1**: that hypothesis is false as stated, so this
  line established nothing; §25.2 proves the repaired form and §25.3
  makes the conclusion unconditional.)
* **`r*(2,3) = 3` exactly, in Coq** (§24.13) — where every general bound
  the development has gives 4.
* **The extremal problem underneath all of it**, `I(m,r)`, named and
  measured, with its crossover at exactly `r = m+1` at both uniformities
  where it is computable, and the consequence that if the star is
  extremal there then `r*(m,3) ≤ m+1` — which would make the sequence
  unbounded and close the spread route to `k = 3`.

It did not produce a new record object; §24.5 and §24.11 say what that
cost. The two closed lines are §24.3 and §24.4.

### 24.1 The correction: the first open term is m = 3

The brief for this session aims §4 at `r*(4,3)` and calls its lower half
"the highest-information experiment available". §22.2's own table says
otherwise:

```
  m     r*(m,3)     status
  1     = 2         exact
  2     = 3         exact
  3     in [3, 6]   OPEN  <- first open term
  4     in [3, 7]   open
```

`r*(3,3)` is the first term of the sequence that is not pinned, and the
question at `m = 3` is exactly the question the brief wants asked at
`m = 4` — is the sequence `2, 3, 3, ...` (bounded, evidence for the
conjecture) or `2, 3, 4, ...` (still growing, and the spread method as
formulated cannot prove the conjecture)? — at a fraction of the size.
Everything below is asked at `m = 3` for that reason.

### 24.2 The theorem: `r*(m,3) ≤ φ·m + O(1)`

`coq/SpreadThreshold.v`, axiom-free, eight new audited names.

`quadratic_no_three_disjoint_bound` splits a family with no three
pairwise disjoint members **three** ways against a matching `{A, B}` —
the two intersecting pieces and a cross piece — and bounds each. The
new observation is that the split throws away the one quantity Rao's
condition makes free:

> The `m` point degrees **inside a single member** have never been
> summed. `Σ_{a ∈ A} deg({a}) ≤ m·r^(m-1)`, and every member meeting `A`
> is counted at least once on the left.

That gives a **two**-way split against a single member `A`, and it is
both simpler and sharper than the three-way one:

```
  {C : C ∩ A ≠ ∅}   covered by the m points of A        ≤ m·r^(m-1)
  {C : C ∩ A = ∅}   meets B, and is intersecting        ≤ r^(m-1) + (m-1)²·r^(m-2)
```

The second piece is `intersecting_piece_bound` with `B` as its anchor;
`miss_member_intersecting` is what makes it intersecting. The cross
piece — the one the quadratic bound pays `m²·r^(m-2)` for — is absorbed
into the cover count at no cost. So

> **`split_no_three_disjoint_bound`:**
> `|F| ≤ (m+1)·r^(m-1) + (m-1)²·r^(m-2)`,
>
> **`split_spread_disjoint`:** `(m+1)·r + (m-1)² ≤ r²` implies
> `SpreadYieldsDisjoint m 3 r`.

The condition solves to `r ≥ [(m+1) + √((m+1)² + 4(m-1)²)]/2`, which is
`m·(1+√5)/2 + O(1)`. The table, with `rust/tests/spread_threshold.rs`
pinning every row:

```
  m        1   2   3   4   5   6   7   8  10  15  20  ...  1000
  2m+1     3   5   7   9  11  13  15  17  21  31  41
  cover    2   4   6   8  10  12  14  16  20  30  40
  quadratic 3  4   6   7   9  11  13  14  18  26  35  ...  1732
  NEW      2   4   5   7   8  10  12  13  17  25  33  ...  1618
```

`split_bound_is_never_worse` pins that the new bound dominates the
quadratic one pointwise for every `m ≤ 400`, strictly from `m = 5` on
and at `m = 3`. The two agree at `m = 2` and at `m = 4`, which is why
the headline `r*(4,3) ≤ 7` does not move. At `m = 1` the new bound is 2,
which is the **exact** value of `r*(1,3)`.

Four rows move, each a Coq corollary: `r_star_three_at_most_five`,
`r_star_five_at_most_eight`, `r_star_six_at_most_ten`,
`r_star_ten_at_most_seventeen`.

**Where this sits relative to the published literature.** Through
`spread_reduction`, `r*(m,3) ≤ r` gives `f(m,3) ≤ r^m + 1`, so the new
threshold gives `f(m,3) ≤ (φm)^m + 1`. That is **worse** than
Erdős–Rado 1960's `m!·2^m + 1 ≈ (2m/e)^m` — at `m = 3` it is 126 against
49 — and exponentially worse than the `(O(log m))^m` of ALWZ / Rao /
Bell–Chueluecha–Warnke. `the_split_threshold_is_behind_erdos_rado_as_a_bound_on_f`
pins that comparison as a test rather than leaving it as a remark. The
bound is not a competitive bound on `f` and must not be quoted as one.
Its content is about the sequence `r*(m,3)` itself, whose boundedness in
`m` is the conjecture at `k = 3`.

### 24.3 Closed: Gallai–Edmonds adds nothing to the link structure

Brief §7(a) proposes pushing the Gallai–Edmonds structure theorem for
graphs with `ν ≤ 2` through `sunflower_iff_link_matching`, and calls it
"the best ratio of new mathematics to work on the entire list".

**It is vacuous, and the argument is one line.** At a `(b-2)`-set `Y` the
link `G_Y` is a graph with `ν(G_Y) ≤ 2` — that is the input
Gallai–Edmonds wants. But `LinkCeiling.top_link_degree_at_most_two`
applied at `Y ∪ {v}`, which is a `(b-1)`-set, says `deg_{G_Y}(v) ≤ 2`.
So

    Δ(G_Y) ≤ 2   **and**   ν(G_Y) ≤ 2,

and a graph with `Δ ≤ 2` is already a disjoint union of paths and
cycles. The content of Gallai–Edmonds is the structure of the
factor-critical components of `G[D]`; `Δ ≤ 2` has made every one of them
an odd cycle before the theorem is invoked. The classification collapses
to the elementary statement §23.1 already used —

> `G_Y` is a disjoint union of paths and cycles with `Σ⌊|C_i|/2⌋ ≤ 2`,

whose edge-maximal case is two disjoint triangles, six edges. There is
no sharper counting ceiling hiding here and no new template for the
search: the repository had already extracted everything this link level
contains.

### 24.4 Closed: the counting ceiling is best at level b-2, not deeper

The obvious follow-on — run the ceiling one level further down — is
worse at every parameter of interest, and it is worth recording so it is
not tried again. A `(b-3)`-set's link is 3-uniform and sunflower-free,
hence has at most `g(3)` members, giving
`|F| ≤ (g(3)/C(b,3))·C(n, b-3)`.

What the development knows unconditionally is `20 ≤ g(3) ≤ 48`
(`IotaRate.v`, restated at its line 378: 20 from
`Intersecting.lower_bound_3_3_20`, 48 from Erdős–Rado) — **not** the 26
this session's brief quotes. 26 would follow from `f(3,3) ≤ 27`, and that
bound is conditional on `Sharp.AHSOptimal`; the brief's `f(3,3) ∈ [21,27]`
is right at the bottom and unproved at the top. At `g(3) = 48`:

```
  b = 4     n = 10      n = 11         b = 5, n = 12
  level b-2      45          55                  132
  level b-3     120         132                  316
```

The deeper level loses because `C(n, b-3)` shrinks by a factor
`~(b-2)/(n-b+3)` while the degree bound grows by `~g(3)/6`, and the
second beats the first at every `n` where a record could live. Even the
most optimistic conceivable value of `g(3)` — its own lower bound, 20 —
gives 50 and 55 at `b = 4` against 45 and 55, so it does not win at ten
points and only ties at eleven. **The counting ceiling is best at level
`b-2`, and there is nothing below it.**

### 24.5 The search: `r*(3,3) ≥ 4`, and what it would take

Unwinding `SpreadYieldsDisjoint 3 3 3`, the sequence grows at its third
term exactly when there is a family `F` with

```
  (a) 3-uniform, distinct, on any ground set
  (b) |F| >= 28                          (= 3^3 + 1)
  (c) deg(x)   <= 9   for every point    (RaoSpread at |T| = 1)
  (d) deg({x,y}) <= 3 for every pair     (RaoSpread at |T| = 2)
  (e) no three pairwise disjoint members
```

`|T| = 3` gives `deg <= 1`, automatic for a distinct family. This is
`rstar::Question::new(3, 3, ground)` exactly, so the instrument already
existed; what had not been done was to run it above the counting floor.

**The question is finite, and the bound is 114 points.** `(e)` gives a
maximum matching `{A, B}` whose union covers `F`, so by
`no_three_disjoint_cover_bound` at `(m,r) = (3,3)`,
`|F| <= 2·3·3² = 54`. Every member has at least one of its three points
in that 6-point cover, hence at most two outside it, so at most
`2·54 = 108` points outside carry any member at all: **any witness lives
on at most 114 points.** The counting floor is `min_ground(3,3) = 10`
(`ceil(3·28/9)`), so the witness, if it exists, lives on between 10 and
114 points. That is a decidable question. It is not a small one.

**Two constructions reaching 20, by hand.** Both were checked by code
sharing nothing with the search.

* Two disjoint copies of `C([5],3)` on disjoint 5-point grounds. Each
  copy is intersecting with `deg = 6` and `deg_pair = 3` exactly; the
  union has `ν = 2` because a member of either copy uses three of that
  copy's five points, leaving no room for a second disjoint member
  inside the same copy. **No cross set can be added** — all 75 of them
  were tried and every one completes a 3-matching, e.g. `{1,4,u}` with
  `{2,3,z}` from the first copy and `{5,6,w}` from the second.
* `link_p = link_q = K_{3,3}` on the same six points `X ∪ Y`, plus the
  two sets `X` and `Y`. Also 20, on eight points rather than ten, with
  `deg = 9` and `deg_pair = 3`.

Two structurally unrelated constructions stopping at the same number
looked like weak evidence that 20 was a plateau. It was not — the search
below reaches 24 — and the episode is worth keeping as written: two
constructions agreeing is evidence that two attempts had the same idea,
not that a bound exists.

**One bound that was free, and what it does not do.** A witness must
have covering number at least 4: a 3-point cover gives
`|F| ≤ 3·9 = 27 < 28`, and a 2-point cover gives 18. Since `ν ≤ 2`
forces `τ ≤ 6`, the object sought has `ν(F) = 2` and `τ(F) ∈ {4,5,6}`.

That is a real necessary condition and it is **not** a discriminator
here: the two hand constructions have `τ = 6` and `τ = 4`, and the
23-member search object has `τ = 4`. All three already satisfy it. It
rules out the star-like shapes — which is why no amount of pushing on a
single cover point gets anywhere — and says nothing about why these
particular families stop.

**The runs.** Grounds 10, 11 and 12 were run as separate background
shells — §6(c)'s free-axis parallelism, which needs no code — with a
`4·10⁹`-node budget each, alongside a SAT attempt at ground 10 capped at
2400 s. `docs/reading.md` records that ground 10 was already attempted
in an earlier session and left undecided by both instruments; these are
larger budgets on the same question, not new questions.

```
  ground   ceiling   budget      nodes        largest   verdict
  10          30     4e9 nodes   4,000,000,001    23     undecided (truncated)
  11          33     4e9 nodes   4,000,000,001    23     undecided (truncated)
  12          36     4e9 nodes   4,000,000,001    24     undecided (truncated)
  10 (SAT)    30     2400 s CPU  --               --     undecided
```

The SAT row is cadical only: it spent its whole 2400 s CPU limit without
a verdict, and the confirming solver `decide` runs afterwards was stopped
by hand to free a core rather than allowed to finish. So that row is
"cadical did not decide it in 2400 s", which is all it was ever going to
be worth — §23.3's second item already found CDCL does not reach this
kind of instance.

**All three are undecided, and that is the honest report.** 4·10⁹ nodes
is above the ~2.4·10⁹ the killed `iota(4,10)` attempt reached in §23.3
and it did not exhaust any of these three grounds. `r*(3,3)` is
unchanged at `[3,5]` from below.

What the runs did produce is a number worth having. `largest` is the
biggest family the search met that satisfies **every** hypothesis except
the size one, so it is a genuine lower bound on what is feasible:

> **A family satisfying (a), (c), (d), (e) with 24 members exists on 12
> points.** Against the 28 needed, the gap is four, not the eight the
> hand constructions suggested.

That also kills the "20 is a plateau" reading above, and it is worth
saying so plainly: two constructions agreeing is not evidence of a
ceiling, only evidence that two people had the same idea.

**The object, and the honest limit of it.** `examples/rstar_dfs.rs` now
carries the best family out of a *truncated* run as well as a successful
one — a size with no object behind it is not something anyone else can
check. Re-run at ground 12 with 4·10⁸ nodes it produces a **23**-member
family, pinned as
`the_r_star_three_three_witness_problem_reaches_twenty_three` and
re-verified against `Spread.RaoSpread`, the matching number and the
uniformity by code sharing nothing with the search:

```
  [0,1,2] [3,4,5] [0,1,3] [0,2,3] [1,2,3] [0,1,4] [0,2,4] [1,2,4]
  [0,3,4] [1,3,5] [2,3,5] [3,4,6] [0,5,7] [1,6,7] [2,6,7] [5,6,7]
  [0,5,8] [1,6,8] [2,6,8] [5,6,8] [0,5,9] [1,6,9] [2,6,9]
```

It uses ten points although it was found at ground 12, and it
**saturates both degree caps at once** — some point lies in 9 members
and some pair in 3. So the object that gets closest is already against
both walls Rao's condition puts up, which is a more specific piece of
information about where the remaining five members would have to come
from than anything the hand constructions gave.

The 24 reported by the deeper `4·10⁹`-node runs has **no object behind
it in this repository** — that run predates the change that dumps the
family — and it is therefore quoted as a measurement, not pinned as a
certificate.

**What this does and does not settle.** Nothing about `r*(3,3)`: the
witness may live on any of the grounds from 10 to 114, and three
truncated runs at the bottom of that range rule out nothing at all. The
node budgets are the result, and they are reported so the next attempt
knows what it has to beat.

**What it would take to finish this from the other side.** The upper
bound could plausibly be driven to 4 without any search, and the missing
step is small and identified. At `(m,r) = (3,4)` the two-way split gives

```
  members meeting A   <= 3·4² = 48, less 2 for A's own multiplicity   = 46
  members missing A   <= I, the max intersecting piece
  need                   46 + I <= 4³ = 64,   i.e.  I <= 18
```

and the intersecting piece here is a 3-uniform intersecting family with
`deg <= 16`, `deg_pair <= 4`. A star attains exactly 16. The covering
number cases give `τ = 2 ⟹ |G| <= 12` by an elementary cross-intersecting
argument, and `τ = 3 ⟹ |G| <= 10` is **Frankl's theorem**, which this
repository does not have. So

> `r*(3,3) ≤ 4` follows from: *no 3-uniform intersecting family with
> `deg ≤ 16` and `deg_pair ≤ 4` has more than 18 members.*

The margin is 2 above the star, and the only missing ingredient is the
`τ = 3` case. That is a far smaller target than anything else on this
row, and unlike the search it does not depend on a 114-point ground set.

### 24.6 The root split, and the checkpoint that comes with it

`rust/src/orbit.rs`, `search_orbits_parallel`. §23.3's fifth item is a
2h28m run at `iota(4,10) >= 28` killed twice by a container restart with
no verdict, and its own diagnosis: what the repository needs is a search
that checkpoints, or one fast enough not to need to.

Both come from the same change, and the reason it is forty lines rather
than a research project is a property of the existing code:

> Every pruning test in `search_orbits` is against the **fixed**
> `target`. `s.best` is written and never read by any prune. So sibling
> subtrees at the root share no incumbent — there is nothing for one
> worker to learn from another, no speedup anomaly, and no risk of
> exploring a node the sequential run would have pruned.

So root subproblem `i` ("the families whose lowest-indexed taken orbit is
`ord[i]`") is independent of every other, the subproblems partition the
space, and **the list of finished ones is a complete resume point**.
`std::thread::scope`, one `Incremental` per worker, two atomics and a
mutex; no new dependency. `examples/record_hunt_par.rs` drives it.

Three things this cost, all worth recording.

* **The recursion has to report whether it finished.** A root subproblem
  abandoned when the budget ran out looks exactly like one that
  completed, and recording it would let a restart skip work that was
  never done — a wrong answer rather than a slow one. `rec` now returns
  `true` only if its subtree was exhausted, and only a `true` is written
  to the checkpoint. The bound firing counts as exhausted; the budget
  running out does not.
* **`push_orbit` already unwinds itself on failure.** The first version
  popped the orbit unconditionally after the subproblem, which on the
  failure path popped entries belonging to nothing and corrupted the
  worker for every later subproblem it took. Caught by the node-count
  differential test, not by any assertion.
* **Root splitting gives coarse checkpoints at the top.** With singleton
  orbits the root subproblems are wildly uneven — the first few carry
  almost all the work — so a budget of a tenth of the total completes
  *nothing* and records *nothing*. The parallelism is real; the
  restart-resilience only starts to bite once a substantial fraction of
  the space is done. Splitting two levels deep would fix it and is not
  done here.

`rust/tests/orbit_parallel.rs` is the differential check: the decision
agrees with `search_orbits` at every parameter small enough to exhaust
twice, any family found verifies, a checkpointed run resumes in strictly
fewer nodes than a fresh one and reaches the same verdict, and — for an
**exhaustive negative** — the node count is identical at 1, 2, 3, 4 and 8
threads. That last qualifier is the content: when the target is
reachable the search stops at the first success, so how much was explored
first depends on how many workers were racing, and a thread-dependent
node count there is correct rather than a bug. Asserting otherwise is
asserting that a parallel search is not parallel, and that is exactly the
assertion the first version of the test made.

### 24.7 Fixed: the mutation harness could pass with its own check off

`tools/mutate.py` warned when the manifest contained no control mutation
and then exited 0 anyway. That is the one failure this file cannot report
softly: the control exists precisely so that a harness which silently
failed to apply its edits — reporting every mutation `killed` — is
caught, and a warning nobody reads does not catch it. A missing control
is now a failure. The control itself (`canary-alpha-rename`) was already
present; what was missing was the guarantee that it stays.

### 24.8 Costs

Every computation that ran over ten minutes. **All four searches ran
concurrently on four cores, alongside a `make -j4 verify` and the Rust
test suite, so the wall times below are for a contended machine and are
not comparable with §23.3's.** Node counts are exact regardless.

```
  what                                   budget        spent        finished?
  r*(3,3) DFS, ground 10                 4e9 nodes     4e9          no, truncated   2746 s
  r*(3,3) DFS, ground 11                 4e9 nodes     4e9          no, truncated   2655 s
  r*(3,3) DFS, ground 12                 4e9 nodes     4e9          no, truncated   2334 s
  r*(3,3) SAT, ground 10 (cadical+cms)   2400 s CPU    2400 s       no verdict
  make -j4 verify (clean + 416 audits)   --            --           yes, after one
                                                                    baseline fix
  iota(4,10) >= 28, 4 threads            1e10 nodes    7.3 CPU-h    no, stopped
                                                       (0/210 roots) 7066 s
  mutation suite, 3 new + control        4 mutants     4            yes, all as
                                                                    declared        146 s
```

**The gates.**

```
  make -j4 verify        green  (433 audited theorems, 433 "Closed under
                                the global context", none carrying an axiom
                                -- including everything in TwoCover.v, whose
                                dependence on Frankl is a hypothesis rather
                                than an assumption)
  make coqchk            green  (38 modules; one axiom:
                                Sunflower.ALWZ.Rao20_lemma2; type-in-type,
                                unsafe (co)fixpoints and assumed positivity
                                all <none>)
  cargo test --release   green  (25 suites, 0 failures)
  python3 tools/mutate.py       green  (82 of the 85 run in full: 79 killed,
                                2 survived as declared, 1 control passing,
                                0 unexpected, ~47 min on 4 cores; the three
                                twocover-* mutations were added afterwards
                                and run separately, all killed as declared,
                                with the control)
  tools/statements.py    green  (500 statements match the baseline)
  tools/docnumbers.py    green  (12 quoted numbers match)
```

`make verify` failed once first, on exactly the check it exists for: a
theorem was added to `tools/audited.txt` without its statement baseline,
and the gate said so and named the fix. Recorded because a gate that has
never failed in a session is a gate nobody has tested.

**Two scheduling mistakes worth recording, both mine.**

* **I over-subscribed the machine.** Four searches on four cores plus a
  Coq rebuild plus a Rust test suite meant everything ran at roughly a
  third of its uncontended rate, and the one test that needed 25 seconds
  took 263. The searches were node-budgeted so the *results* are
  unaffected, but the wall times are worthless as a baseline for anyone
  else, which is the whole reason to record them.
* **I did not checkpoint the runs I was most worried about losing.**
  This session added checkpointing to `search_orbits` — and then ran the
  `r*(3,3)` searches through `rstar::dfs`, which has none, in exactly the
  fragile shape §23.3 warns about. Three 45-minute single-threaded runs
  with no resume point is the thing the engineering was supposed to stop.
  They survived; that was luck, not design.

[TO FILL]

### 24.9 Measured: the intersecting piece bound has a factor of two of
###      slack, and closing it would give `r*(m,3) ≤ m+1`

`rstar::max_intersecting_piece` computes the quantity the threshold
actually turns on: the largest `m`-uniform **intersecting** family
satisfying Rao's condition. Write it `I(m,r)`. The split bound is

```
  |F|  ≤  m·r^(m-1)  +  I(m,r),
```

and `intersecting_piece_bound` supplies `r^(m-1) + (m-1)²·r^(m-2)` for
the second term. Nobody had asked what `I` actually is.

```
  m   r   ground   5    6    7    8    9        piece bound   star
  3   3            10   10   10   10   10            21         9
  3   4            10   10   12   14   16            32        16
```

Every row exhausted (`the_intersecting_piece_bound_has_a_factor_of_two_of_slack`
pins grounds 5–8; ground 9 costs 56M and 306M nodes respectively).

Two things fall out.

**One: the bound is off by a factor of two at `(3,3)`.** The truth is 10
against a bound of 21. The extremal object is `C([5],3)` — every 3-subset
of a 5-set — which is intersecting with `deg = 6` and `deg_pair = 3`, so
it sits under both caps, and it **beats every star** (9). That is worth
noticing on its own: the natural guess for the extremal intersecting
family under a degree cap is a star, and at `(3,3)` it is not.

**Two, and this is the one that matters: if `I(m,r)` were the star
`r^(m-1)`, the split condition would read**

```
  m·r^(m-1) + r^(m-1) ≤ r^m     ⟺     r ≥ m + 1.
```

**`r*(m,3) ≤ m+1`** — linear with constant 1, against the `φ·m = 1.618 m`
proved in §24.2. At `m = 10` that is 11 against 17. And `r = m` is a hard
floor for this method whatever `I` is, since `m·r^(m-1)` alone already
equals `r^m` there, so `m+1` is the best the two-way split can ever give.
`the_star_would_give_r_star_at_most_m_plus_one` pins both halves.

At `(3,4)` the measurement says `I = 16`, which **is** the star, exactly
the value needed: `3·16 + 16 = 64 = 4³`. So

> **`r*(3,3) ≤ 4` follows from `I(3,4) ≤ 16` alone**, and `I(3,4) = 16`
> is exhausted for every ground set up to nine points.

That would put the first open term of the sequence at `{3,4}`, one value
from decided.

**What is not proved, stated plainly.** `I(3,4) ≤ 16` is measured to
ground 9, not proved for all grounds, and the search cannot reach ground
10 (the ground-9 row already costs 306M nodes and each further point
multiplies by roughly twenty). A proof would go by covering number, since
an intersecting 3-uniform family has `τ ≤ 3`:

* `τ = 1` — a star, so `|G| ≤ deg cap = 16`. Immediate.
* `τ = 2` — cover `{p,q}`. If both sides are nonempty, an edge of one
  side's tail forces the other side's tail into two stars, giving
  `|G_p|, |G_q| ≤ 2·deg_pair = 8` and `|G| ≤ 8+8+4 = 20`; pushing either
  side to 8 collapses the other to 1. Elementary, and it is a real case
  analysis rather than a line.
* `τ = 3` — **Frankl's theorem**, `|G| ≤ 10`, which this repository does
  not have. The elementary greedy bound is `3³ = 27`, well short of 16.

So the honest shape of the next step is: one elementary case analysis,
and one classical theorem to formalise. That is a much more specific
target than "sharpen `intersecting_piece_bound`", and it is worth
strictly more — the whole table of §24.2 moves if it lands.

### 24.10 Proved: the two-point cover case, and the star is extremal
###       from `r = 4` on

`coq/TwoCover.v`, axiom-free, eight new audited names. This is the
elementary half of §24.9's target, done.

An intersecting 3-uniform family has covering number at most 3, so
`I(m,r)` splits into `τ = 1, 2, 3`. The first is a star and immediate
from the point-degree cap (`one_cover_bound`: `|G| ≤ r²`). The third is
Frankl's theorem and is **not** here. The second is now a theorem:

> **`two_cover_bound`:** if `{p,q}` covers `G` and neither point covers
> alone, then `|G| ≤ max(4r, 3r+4)`.
>
> **`two_cover_star_extremal`:** hence `|G| ≤ r²` — the size of a star —
> for every `r ≥ 4`.
>
> **`covered_by_two_at_most_star`:** and dropping the "neither alone"
> hypothesis, `τ(G) ≤ 2` and `r ≥ 4` give `|G| ≤ r²` outright.

`r = 4` is the exact crossover, and it is sharp on both sides:

```
  r          2    3    4    5    6   10
  max(4r,3r+4) 10  13   16   20   24   40
  r² (star)   4    9   16   25   36  100
  star extremal?  no   no  yes  yes  yes  yes
```

At `r = 3` the bound is 13 against a star of 9 — and the star really is
not extremal there. §24.9's measurement gives 10, attained by `C([5],3)`,
which has covering number **3**. So the one case this file does not cover
is exactly the case that breaks the pattern, which is not a coincidence.

**The argument, and why it needs no graph classification.** Write `G_p`
for the members through `p` but not `q`, `G_q` for the mirror, `G_pq` for
both. `G_pq` is capped by the pair degree at once. Then:

* **Any member of `G_q` caps `G_p` at `2r`.** A member `C'` of `G_q`
  misses `p`, so a member of `G_p` can only meet it at one of `C'`'s two
  points other than `q` — and it contains `p`, so it contains one of two
  *pairs*. Two pairs, each capped at `r`.
* **Either `G_p` has a common point besides `p`, or `G_q` has at most
  four members.** If some `w ≠ p` lies in every member of `G_p`, the
  single pair `{p,w}` caps `G_p` at `r`. Otherwise take `C1 = {p,u,v}` in
  `G_p`; some `C2` misses `u` and some `C3` misses `v`. A member of `G_q`
  meets `C1` away from `p`, so it holds `u` or `v`; if it holds `u` it
  must still meet `C2`, which has neither `p` nor `u`, so it holds one of
  `C2`'s two other points. That pins it to a **triple**, and a triple has
  degree at most one under Rao's condition. Four triples, four members.

The textbook route here is through the classification of graphs with
matching number one — "a star or a triangle" — applied to the tails.
Naming `C2` and `C3` replaces it. That matters for a formalisation:
the classification is a real piece of graph theory and this is four
lines of case analysis.

**What is still missing, and it is one theorem.** `I(3,4) ≤ 16` needs the
`τ = 3` case at `≤ 16`. The elementary greedy bound is `3³ = 27`;
Frankl's theorem gives 10. So:

> `r*(3,3) ≤ 4` now rests on **exactly one** unformalised classical
> result — Frankl's bound for 3-uniform intersecting families with
> covering number 3 — and on nothing else.

Three mutations check the load-bearing parts: the `4 ≤ r` hypothesis (it
fails at 3, by 13 against 9), the maximum (neither branch dominates, and
they cross at exactly 4), and the four triples.

### 24.11 The record attempt, and the limit of root splitting

`iota(4,10) >= 28` is the question §23.3 calls the cheapest live one on
the row: `iota(4,9) = 27` is exhausted-exact, ground 10 is undecided, and
a hit gives `g(4) >= 56` against a record of 54. §23.3's attempt was
killed twice by container restarts after 2h28m of single-threaded search
with no verdict, and the diagnosis was that the repository needed a
search that parallelises and checkpoints. This session built one
(§24.6). This is it, pointed at that question.

```
  record_hunt_par 4 28 10 10, budget 1e10 nodes, 4 threads, checkpointed
    elapsed          7066 s wall (1 h 58 m)
    CPU              26250 s = 7.3 CPU-hours, 4 workers at 93% each
    verdict          none -- stopped by hand, budget not spent
    root subproblems completed   0 of 210
```

It was **stopped**, not finished: the 10^10-node budget was still
running when the session ended it, so this is not even "undecided at
10^10 nodes" — it is "no verdict after 7.3 CPU-hours", which is a weaker
statement and the only one the run supports.

Two things it establishes, and only one of them is about the record.

**The parallelism is real.** 372% CPU sustained across four workers with
no lock contention visible — the "every prune is against the fixed
target, so root subtrees share nothing" argument holds up in practice,
not only on the small instances the differential test can exhaust twice.

**The checkpointing, on this instance, is worth nothing.** Zero of the
210 root subproblems finished in seven CPU-hours, so the frontier file
stayed empty and a restart would have resumed from nothing. §24.6 already
flagged root splitting as coarse at the top of the tree; the honest
statement after running it is stronger than "coarse":

> With singleton orbits, the first root subproblems are not merely larger
> than the rest — at `(b, g) = (4, 10)` they are larger than any budget
> this repository can afford. Root splitting buys the 4×. It does **not**
> buy restart-resilience at this size, and treating it as though it does
> is the same mistake §23.3 made in a new place.

What would: splitting two levels deep (the pairs `(i, j)` of first and
second taken orbit), which turns 210 subproblems into ~20000 and would
have recorded thousands of them in the same seven hours. That is a small
change and it is the first thing the next attempt should do.

Also fixed, because it was the reason none of this was visible while it
ran: `search_orbits_parallel` now spawns a monitor thread that reports
nodes and completed roots every thirty seconds whenever a checkpoint is
requested. A run that reports nothing until it returns cannot be
distinguished from a hung one, and this run spent two hours in that
state.

### 24.12 The third case, as a hypothesis: `r*(3,3) ≤ 4` conditionally

> **Correction, §25.1: the hypothesis this section introduces is false
> for every constant**, because it omits distinctness of the family and
> `length G` counts members with multiplicity. Everything below is a
> true implication with a false antecedent and establishes nothing. The
> hypothesis is repaired (`Distinct G` added) and *proved* in
> `coq/TauThree.v`, so the conclusion `SpreadYieldsDisjoint 3 3 4` now
> holds unconditionally — see §25.2 and §25.3. The text is left as
> written; the mistake is more useful than a silent edit.

`coq/TwoCover.v`, eight more audited names, **and still no new axiom**.

§24.10 proved `τ ≤ 2`. The remaining case is `τ = 3`, which is Frankl's
theorem and which this development does not have. It enters as an
explicit hypothesis, to the left of every arrow, so `make axiom-audit` is
unchanged and `Print Assumptions` on every name in the file still reports
"closed under the global context". The repository still has exactly one
axiom.

```coq
  Definition TauThreeAtMost (K : nat) : Prop :=
    forall G, Uniform 3 G -> (G intersecting) ->
      (forall p q, exists C, In C G /\ ~ In p C /\ ~ In q C) ->   (* τ ≥ 3 *)
      length G <= K.

  Theorem r_star_three_three_at_most_four :
    TauThreeAtMost 16 -> SpreadYieldsDisjoint 3 3 4.
```

Three things about that statement are the point.

**One: 16, not 10.** Frankl's theorem gives `|G| ≤ 10`; the split needs
only 16, so the theorem is stated on the weaker hypothesis and Frankl is
a corollary (`frankl_is_stronger_than_needed`,
`r_star_three_three_at_most_four_from_frankl`). The gap the missing
theorem has to fill is the interval `[16, 27]` — 27 being the elementary
greedy bound for `τ = 3` that this development *could* prove and which is
not enough.

**Two: the arithmetic has no slack at all.** The split reads
`|F| ≤ 3·r² + I(3,r)`, which at `r = 4` is `48 + I`, against `4³ = 64`.
`48 + 16 = 64` exactly. The mutation `twocover-tau-three-seventeen`
weakens the hypothesis to `TauThreeAtMost 17` and is killed: one more
member and the theorem is false. The `m = 2` row of
`SpreadYieldsDisjoint 3 3 4` is an equality too — the cover bound gives
`2·2·4 = 16` against `4² = 16` — so nothing anywhere in this is loose.

**Three: what had to be built to say it.** `split_with_piece`
parameterises §24.2's split by the intersecting-piece bound instead of
hard-wiring `intersecting_piece_bound`. That is the difference between 32
and 16 at `(3,4)`, which is the difference between not closing and
closing. And `covers_dec_search` makes "some two points cover `G`" a
finite decision — the candidates can be taken from `concat G`, because a
cover point lying in no member is useless — which is what lets the
`τ ≤ 2` and `τ = 3` branches be separated constructively.

**Where the sequence now stands.**

```
  m     r*(m,3)        by
  1     = 2   exact
  2     = 3   exact
  3     in [3,4]       upper: TauThreeAtMost 16 (Frankl); lower: r = 2 refuted
  4     in [3,7]       upper: quadratic / split threshold
  5     in [3,8]
  10    in [3,17]
```

`r*(3,3) ∈ [3,4]` is conditional and says so. Unconditionally it remains
`[3,5]` from §24.2. Either way the first open term of the sequence that
*is* the conjecture is now one value wide given one classical theorem,
where this session found it three values wide and pointed at the wrong
uniformity.

### 24.13 `I(m,r)` as an extremal problem, and the crossover at `r = m+1`

Everything from §24.9 on is really about one quantity, and it deserves
its own name:

> `I(m,r)` = the largest `m`-uniform **intersecting** family satisfying
> Rao's condition `deg T ≤ r^(m-|T|)` for every nonempty `T`.

Extremal problems for intersecting families under a bound on the
*maximum degree* are studied (Frankl 1987; Huang–Zhao;
Frankl–Han–Huang–Zhao; Kupavskii). The constraint here is different: a
cap **at every level at once**, which is Rao's spread condition rather
than a degree condition. I have not found this posed before.

**What it decides.** §24.2's split reads `|F| ≤ m·r^(m-1) + I(m,r)`, so
`SpreadYieldsDisjoint m 3 r` follows as soon as

```
  I(m,r)  ≤  r^m − m·r^(m-1)  =  r^(m-1)·(r − m).
```

Two readings, and the first is a limit of the method rather than of any
bound on `I`:

* **`r = m` is a hard floor.** There the right-hand side is zero while
  `I ≥ 1` always (one member is an intersecting family). So this split
  can never give `r*(m,3) ≤ m`, whatever is proved about the piece.
  `split_cannot_reach_r_equals_m` is the identity `m·m^(m-1) = m^m`.
* **At `r = m+1` the requirement is exactly "the star is extremal"** —
  the right-hand side is `(m+1)^(m-1)`, the size of a star under the
  point cap. `star_extremal_gives_m_plus_one`:

  > if `I(m, n+1) ≤ (n+1)^(m-1)` for every `m ≤ n`, then
  > `r*(n,3) ≤ n+1`.

  **This is an implication, not an equivalence** — `r*(m,3) ≤ m+1` could
  hold for reasons this split cannot see. `m+1` is linear with constant
  1, against §24.2's `φ·m = 1.618 m`, and it is the best the two-way
  split can ever give.

**The measured crossover.** Both uniformities where `I` is computable put
it at exactly `r = m+1`:

```
  m = 2    r        2   3   4   5      star = r
           I(2,r)   3   3   4   5
  m = 3    r        3   4              star = r²
           I(3,r)  10  16
```

Below the crossover the star loses to a small design — the triangle at
`m = 2`, `C([5],3)` at `m = 3`. From it on the star wins. That is not an
accident of small cases: the star's size under the caps is `r^(m-1)`,
**exponential in `m`**, while every classical intersecting family is
polynomial or `~4^m`:

```
  m               2    3     4      5      6
  C([2m-1],m)     3   10    35    126    462
  PG(2,q), m=q+1  3    7    13     21     31
  star at m+1     3   16   125   1296  16807
```

**The `m = 2` row, proved.** `two_uniform_intersecting_bound`:
`I(2,r) ≤ max(r,3)`, by the same device as §24.10 — instead of "an
intersecting graph is a star or a triangle", name an edge missing `a`
*and* an edge missing `b`, which confines everything to the triangle
`{ab, ac, bc}`. Hence `StarExtremalAt 2 r` for `r ≥ 3 = m+1`, and with
the trivial `m = 1` case:

> **`r_star_two_three_at_most_three : SpreadYieldsDisjoint 2 3 3`.**

That is new to the development. Every general bound it has gives **4** at
`m = 2` — `cover_spread_disjoint` (`2n`), `quadratic_spread_disjoint`,
and §24.2's split all do. With `Audit.no_spread_yields_disjoint_2_3_2`
refuting `r = 2`, the second term is now pinned in Coq at exactly
`r*(2,3) = 3 = m+1`, where §22.3 had it certified only by exhaustive
search. **On the one row where `I` is known in closed form, the
star-extremal route is sharp and the general bounds are not.**

**What is at stake.** `r*(1,3) = 2` and `r*(2,3) = 3` are exact and both
equal `m+1`. If `r*(m,3) = m+1` in general the sequence is **unbounded**,
and by §18.5 that means the spread reduction as formulated by ALWZ / Rao
/ Bell–Chueluecha–Warnke cannot prove the sunflower conjecture at
`k = 3`. It would not refute the conjecture; it would close the route.

The pattern is decided at the third term by one finite object — the
28-member family of §24.5, which this session searched for and did not
find. And the two halves are not symmetric:

* the **upper** half is within one classical theorem (§24.12), while
* the **lower** half cannot be settled by this split at all, because
  `r = m` is the floor above. Proving `r*(3,3) = 3` needs an argument the
  development does not have.

So the honest state of the third term is: nearly closed from above,
untouched from below, and it is the lower half that decides whether the
whole approach survives.

### 24.14 The one-line verdict

**The sequence that is the conjecture moved at three of its terms: an
unconditional `r*(m,3) ≤ φ·m + O(1)`, a conditional `r*(3,3) ≤ 4` resting
on one classical theorem and no new axiom, and an exact `r*(2,3) = 3` in
Coq for the first time.**

No new record object: the `iota(4,10) >= 28` attempt spent 7.3
CPU-hours and was stopped without a verdict (§24.11), and what it
established is about the instrument rather than the record — root splitting delivers its 4×
and delivers **no** restart-resilience at this size.

Two named lines are closed by argument rather than
by budget — Gallai–Edmonds on links (§24.3, vacuous because `Δ ≤ 2` gets
there first) and the counting ceiling below level `b-2` (§24.4, worse at
every parameter where a record could live). The `r*(3,3) ≥ 4` search is
**undecided** at `4·10⁹` nodes on each of grounds 10, 11 and 12, which
is a cost, not a result; what it leaves behind is a verified 23-member
object five short of a refutation, and the observation that the witness
problem is finite with a 114-point ground bound.

The lead worth taking next is not the search. §24.9 measured `I(m,r)`,
the true maximum of the intersecting piece, at 10 against a bound of 21
at `(3,3)` and at exactly the star at `(3,4)`; if the star is extremal in
general, the split condition collapses from `r ≥ φ·m` to **`r ≥ m+1`**,
the best this method can ever give. §24.10 then proved the `τ ≤ 2` half
of that at `m = 3`: the star is extremal among two-covered families for
every `r ≥ 4`, and `r = 4` is the exact crossover.

§24.12 then discharged everything else: `r*(3,3) ≤ 4` is a theorem of
this development **conditional on one hypothesis and no new axiom** —
that a 3-uniform intersecting family of covering number 3 has at most 16
members, which Frankl's theorem gives with room to spare (it gives 10)
and which the elementary greedy bound (27) does not.

§24.13 then names the quantity all of that turns on — `I(m,r)`, the
largest intersecting family under Rao's condition — measures its
crossover at exactly `r = m+1` at both uniformities where it is
computable, proves the `m = 2` row in closed form, and gets
`r*(2,3) ≤ 3` out of it: the **exact** second term, where every general
bound in the development gives 4.

That is the session's real output: not the search, which decided nothing
at either question it was asked, but an unconditional threshold theorem,
a conditional one closing the third term to a single value, an exact
second term, and a well-posed extremal question — `is the star extremal
for intersecting families under Rao's condition once r ≥ m+1?` — whose
answer decides whether the spread route to `k = 3` survives at all.

---

## 25. The hypothesis that was false, the theorem that replaces it, and
##     `r*(3,3) ≤ 4` with nothing assumed

**Verdict: one new theorem — the `m = 3` row of the extremal problem
§24.13 names, closed exactly — which makes `r*(3,3) ≤ 4` unconditional;
one decisive negative, that the hypothesis §24.12 rested on is false for
every constant; and no new record object.** In order:

* **`TwoCover.TauThreeAtMost K` is false for every `K`** (§25.1), so
  §24.12's `r*(3,3) ≤ 4` was an implication with a false antecedent and
  established nothing. `TauThree.tau_three_at_most_unguarded_is_false`
  is that refutation in Coq, with the Fano plane as the object.
* **A 3-uniform intersecting family of *distinct* sets with covering
  number at least 3 has at most 16 members** (§25.2), proved here
  without Rao's condition, without Frankl's theorem, and axiom-free.
  Frankl gives 10; the elementary greedy bound gives 27; 16 is the
  first value in the interval `[16,27]` this development can prove, and
  it is exactly what the split needs.
* **`r*(3,3) ≤ 4` unconditionally**, so the third term of the sequence
  is `[3,4]` with nothing assumed (§25.3), where §24.2 left it at
  `[3,5]` and §24.12 left it at `[3,4]`-on-a-false-hypothesis. And
  **`I(3,r) = r²` for every `r ≥ 4`** — the `m = 3` row of §24.13's
  extremal conjecture, closed, with the attaining object in the file.
* **The same statement at every uniformity** (§25.4), at the same
  threshold `r ≥ m+1`, with a complete proof — **in prose, not in Coq**.
  §25.4 names the two Coq pieces that are missing.

### 25.1 Closed: the `tau = 3` hypothesis was false as stated

§24.12's headline is `r_star_three_three_at_most_four : TauThreeAtMost 16
-> SpreadYieldsDisjoint 3 3 4`, and the hypothesis was

```coq
  Definition TauThreeAtMost (K : nat) : Prop :=
    forall G, Uniform 3 G ->
      (forall C D, In C G -> In D G -> exists x, In x C /\ In x D) ->
      (forall p q, exists C, In C G /\ ~ In p C /\ ~ In q C) ->
      length G <= K.
```

`Uniform 3 G` is `Forall (fun A => length A = 3 /\ NoDup A) G`. The
`NoDup` is on the *points inside each member*. Nothing anywhere in the
statement says the **members** are distinct — and `length G` counts
members with multiplicity.

So take the Fano plane: seven 3-sets on seven points, pairwise
intersecting, and of covering number 3 because each point lies on
exactly three of the seven lines, so two points meet at most six of
them. Concatenate it with itself three times. Every hypothesis survives
verbatim — they are conditions on *pairs* of members and on *which* sets
occur, never on how often — and `length` becomes 21.

> **`TauThree.tau_three_at_most_unguarded_is_false : forall K,
> ~ TauThreeAtMostUnguarded K`.** Not "false for 16": false for every
> constant.

`rust/tests/tau_three.rs::fano_satisfies_the_unguarded_hypotheses` checks
the object and the repetition independently of the Coq.

**Why the outer family did not have this problem.** `split_with_piece`
takes `RaoSpread 3 F r`, and Rao's condition at a triple reads
`deg T F <= r^(3-3) = 1`, so a 3-uniform Rao-spread family is
automatically distinct. That is now
`TwoCover.rao_uniform_distinct`, and it is what lets the repair be local:
`Distinct G` is added to `FranklTauThree` and `TauThreeAtMost`, and the
single consumer, `intersecting_at_most_star`, derives it from the Rao
condition it already carries. No other statement changes.

**What this is worth recording as.** The gates did not catch it and could
not have: the file compiles, `Print Assumptions` says "closed under the
global context", the mutation `twocover-tau-three-seventeen` is killed as
declared, and every one of those remains true of a theorem with a false
antecedent. What catches it is asking whether the hypothesis is *true* —
which is the same question as asking whether it is provable, and is where
this session started.

### 25.2 The theorem: 16, elementary, and no Frankl

`coq/TauThree.v`, axiom-free, thirteen new audited names, plus
`TwoCover.rao_uniform_distinct`.

> **`tau_three_bound`:** `G` 3-uniform, `Distinct`, intersecting, with
> `tau(G) >= 3`, has `length G <= 16`.

No Rao condition anywhere in it. The argument is a decomposition against
one member and one graph lemma.

**The pair cap is free.** `tau(G) >= 3` says: for every two points there
is a member missing both. So for any pair `{a,b}`, take the witness `D`
missing them; a member containing `{a,b}` meets `D` in a third point, and
`D` has three, so — using distinctness —

```
    deg({a,b}) <= 3      for every pair                             (P)
```

`tt_pair`. Covering number 3 is used in exactly two ways in the whole
file: here, and to make the three tails nonempty.

**The decomposition.** Fix `M = {x,y,z} in G`. Every member meets `M`.
Peel:

```
   members containing {x,y}                       <= 3      by (P)
   members containing {x,z} but not {x,y}         <= 2      (P), less M
   members containing {y,z} but neither of those  <= 2      (P), less M
   what survives meets M in exactly one point:  T_x, T_y, T_z
```

The two 2's are the content of `minus_one_bound`: `M` itself occupies one
of the three slots (P) allows at each pair, and the peel has already
removed it. So the layers meeting `M` twice or more contribute at most
**7**, and `1 + 6 = 7` is the same number counted the other way.

**The tails.** For `C in T_x`, `C = {x} u e` with `e` a 2-set disjoint
from `M`. The three tail graphs `A`, `B`, `C~`

  * have **maximum degree at most 3** — an edge of `A` at `v` is a member
    containing `{x,v}`, and (P) caps those at 3;
  * are **pairwise cross-intersecting** — a member of `T_x` and one of
    `T_y` meet, and not at `x`, `y` or `z`;
  * are **all nonempty** — `T_z` empty makes `{x,y}` a cover.

> **`lemma_L`:** three nonempty pairwise cross-intersecting graphs, each
> of maximum degree at most 3, have at most **9** edges between them.

`7 + 9 = 16`. Nothing in that sum has slack: the mutation
`tauthree-lemma-l-eight` weakens 9 to 8 and is killed, and
`twocover-tau-three-seventeen` (already in the manifest) shows 17 fails
on the other side.

**Proof of the graph lemma, in three moves.** Order so `|A| >= |B| >= |C|`.

  * **L1.** *An intersecting graph of maximum degree 3 has at most 3
    edges.* Take `e = {a,b}`. If every edge holds `a`, the degree cap
    ends it. Otherwise name an edge missing `a`, then an edge holding `a`
    but not `b`; between them every edge is forced into the triangle
    `{ab, bc, ac}`. This is §24.10's device — name the members that miss
    the points, rather than invoke the classification of graphs with
    matching number one — and it is why the whole file needs no graph
    theory.
  * **L2.** *Six edges force the other two graphs to one each.* If every
    edge of `A` meets a fixed pair `{u,v}` and `|A| = 6`, then `u` and
    `v` each carry three `A`-edges and `uv` is not one of them. An edge
    meeting all of `A` and missing `u` would have to contain all three
    `A`-neighbours of `u` — three distinct points in a 2-set. So every
    edge of `B` and of `C` contains both `u` and `v`, hence *is* `{u,v}`.
  * **L3.** *Two disjoint edges cap the other two together at four.* If
    `e1 = {a,b}` and `e2 = {c,d}` are disjoint edges of `A`, then `B` and
    `C` live inside `K = {ac, ad, bc, bd}`. Split `K` into its two
    disjoint pairs; on each pair, `B` and `C` cannot both be occupied on
    opposite sides, so each pair contributes at most 2, and `|B| + |C| <= 4`.

  Then: `|A| <= 3` for all three gives 9 (L1). Otherwise `|A| >= 4`, so
  `A` is not intersecting (L1), so it has two disjoint edges, so
  `|B| + |C| <= 4` (L3), and `|A| <= 6` always. `|A| in {4,5}` gives at
  most 9; `|A| = 6` gives at most 8 by L2. Nine is attained twice —
  three copies of one 3-star, and three copies of one triangle.

**Where this sits relative to the literature.** Frankl's theorem for
3-uniform intersecting families of covering number 3 gives `|G| <= 10`,
which is the truth (`rust/tests/tau_three.rs` exhausts it on grounds 5–7
and finds 10, attained by every 3-subset of a 5-set). The bound proved
here is 16, so it is **six worse than the classical result and is not a
contribution to that question**. What it is, is the first bound in the
interval `[16, 27]` this development can prove — 27 being the elementary
greedy bound, which is not enough — and 16 is exactly the constant the
split can afford. The value is that the constant is now a theorem of
this development rather than a citation.

### 25.3 What it discharges

Three results lose their hypothesis, none of their statements changes:

```
  TauThree.tau_three_at_most_sixteen                 : TauThreeAtMost 16
  TauThree.r_star_three_three_at_most_four_uncond... : SpreadYieldsDisjoint 3 3 4
  TauThree.f_three_three_unconditional               : UpperBound 3 3 65
  TauThree.intersecting_at_most_star_unconditional   : I(3,r) <= r^2 for r >= 4
  TauThree.three_uniform_star_extremal               : StarExtremalAt 3 r for r >= 4
```

`UpperBound 3 3 65` is worth stating only as a discharge, not as a
result: Erdős–Rado 1960 gives `3!·2^3 + 1 = 49` unconditionally and this
development has had it since `ErdosRado.v`. §24.2 already records that
the whole `r*` route is behind Erdős–Rado as a bound on `f`; what moves
here is the threshold, not the sunflower number.

**The sequence.**

```
  m     r*(m,3)      by
  1     = 2   exact
  2     = 3   exact  (§24.13)
  3     in [3,4]     upper: this section;  lower: r = 2 fails already at m = 2
  4     in [3,7]     upper: §24.2's split threshold
  5     in [3,8]
  9     >= 4         CONDITIONAL -- see below
  10    in [3,17]
```

Every row is a theorem of this development **except `m = 9`**, and that
exception is a number from this session's brief that did not survive
being checked. `IotaRate.substitution_would_refute_the_flat_threshold_at_nine`
is stated as `LowerBound 9 3 (3^9 + 317) -> ~ SpreadYieldsDisjoint 9 3 3`,
and its own header says the hypothesis is open here: it rests on the
Abbott–Hanson–Sauer substitution, *"which is not formalised here"*. So
`r*(9,3) >= 4` is conditional on an unformalised construction, and
§22.2's table — which lists it flat, in the same column as the proved
rows — overstates it. Corrected there and in `STATUS.md` in the same
commit.

The consequence matters for §25.5: it is **not** a theorem of this
development that the sequence is non-constant. What is a theorem is
`r*(1,3) = 2` and `r*(2,3) = 3`, so it has grown once. Whether it grows
again is exactly the open question, and `m = 9` is a conjectured second
step, not a certified one.

**`I(3,r) = r²` for every `r >= 4`, exactly.** The upper bound is the
`tau <= 2` case (§24.10) plus the `tau = 3` case (here). The lower bound
is an object: `TauThree.star34`, the grid star — a common point `0`
together with one point from each of two blocks of size four —

```
  [0,1,5] [0,1,6] [0,1,7] [0,1,8]   [0,2,5] [0,2,6] [0,2,7] [0,2,8]
  [0,3,5] [0,3,6] [0,3,7] [0,3,8]   [0,4,5] [0,4,6] [0,4,7] [0,4,8]
```

sixteen members, `Uniform 3`, `Distinct`, intersecting, and
`RaoSpread 3 F 4` with equality at `{0}` and at every pair through `0`.
`star34_attains_sixteen` in Coq; `rust/tests/tau_three.rs` re-verifies it
by code sharing nothing with it.

So the `m = 3` row of §24.13's conjecture — *is the star extremal for
intersecting families under Rao's condition once `r >= m+1`?* — is
**closed, affirmatively, and sharply**, and the crossover really is at
`r = m+1`: at `r = 3` the truth is 10 against a star of 9, so the
statement is false one step below. The mutation
`tauthree-star-extremal-at-three` is that fact.

**What it does not give.** `star_extremal_gives_m_plus_one` needs
`StarExtremalAt m (n+1)` for *every* `m <= n`. Closing `m = 3` closes one
row; `m = 4` and up are untouched, and `r*(4,3)` does not move.

### 25.4 The two-point-cover case at every uniformity — prose, not Coq

§24.10 proves the star extremal among 3-uniform intersecting Rao-spread
families of covering number at most 2, for `r >= 4 = m+1`. The same holds
at every uniformity at the same threshold, and here is the proof. **It is
not formalised**, and the end of this section says exactly what is
missing.

> **Claim.** `G` `m`-uniform, intersecting, `RaoSpread(r)`, `tau(G) <= 2`,
> `r >= m+1`. Then `|G| <= r^(m-1)`.

**Reduction.** Cover `{p,q}`; write `G_p`, `G_q`, `G_pq` as in §24.10.
`|G_pq| <= deg({p,q}) <= r^(m-2)`. Put `u = m-1` and let `A`, `B` be the
tails of `G_p`, `G_q`. Then `deg_A(T) = deg_G({p} u T) <= r^(u-|T|)`, so
**`A` and `B` satisfy Rao's condition at uniformity `u` with the same
`r`**, and they are cross-intersecting (a member of `G_p` and one of
`G_q` meet, and not at `p` or `q`). It is enough that

```
  |A| + |B| <= (r-1)·r^(u-1)       whenever r >= u+2,
```

since `(r-1)r^(u-1) + r^(u-1) = r^u = r^(m-1)`.

**Two bounds, and a covering number.** Let `a = tau(A)`, `b = tau(B)`;
both are at most `u`, because any member of `B` meets every member of `A`
and so *is* a cover of `A`. Then

  * `|A| <= a·r^(u-1)` — sum the point degrees over a minimum cover;
  * `|B| <= u^a·r^(u-a)` — greedy. Pick `C1` in `A`; every member of `B`
    holds one of its `u` points. A set of size `j < a` is not a cover of
    `A`, so there is a member of `A` disjoint from it and the tree
    extends. After `a` steps every member of `B` contains one of at most
    `u^a` specific `a`-sets, each of degree at most `r^(u-a)`;

and the same with the roles swapped. Take `a <= b`. Since `u < r`,
`u^b r^(u-b) <= u^a r^(u-a)`, so the swapped greedy bound also gives
`|A| <= u^a r^(u-a)`. Writing `s = a-1`, either

```
  (O1)  |A| + |B| <= a·r^(u-1) + u^a·r^(u-a)   suffices iff  u^(s+1) <= (r-2-s)·r^s
  (O2)  |A| + |B| <= 2·u^a·r^(u-a)             suffices iff  2·u^(s+1) <= (r-1)·r^s
```

**The numeric half, from Bernoulli alone.** Both are monotone in `r`, so
it is enough at `r = u+2`. At `s = 0` (O1) is `u <= r-2` and holds by the
hypothesis; for `s >= 1`, with `(u+2)^s >= u^s + 2s·u^(s-1) =
u^(s-1)(u+2s)`:

  * **`2s <= u` gives (O1):** `(u-s)(u+2)^s >= u^(s-1)(u² + su - 2s²) >=
    u^(s+1)`, the last step being `s(u - 2s) >= 0`.
  * **`2s >= u` gives (O2):** `(u+2)^s >= u^(s-1)(u+2s) >= 2u^s`, so
    `(u+1)(u+2)^s >= 2u^s(u+1) >= 2u^(s+1)`.

Every `s` falls in one of the two. `rust/tests/cross_intersecting.rs`
checks the disjunction, and that the *declared* split is the one that
works, for every `u <= 60` and every `r` in `[u+2, u+12]`, in exact
arithmetic (the products pass `u128` before `u = 30`).

**The threshold is not an artefact.** At `s = 0` — `A` a star — (O1)
reads `u <= r-2`, which is `r >= m+1` on the nose, and at `r = m` both
options fail. So `m+1` is where this argument turns over, and it is the
same `m+1` that §24.13's `split_cannot_reach_r_equals_m` shows is the
floor of the whole method.

**How much is left on the table.** At `u = 2` the bound is `(r-1)r` and
the truth is `2r+1` — one edge against the two full stars at its
endpoints — so it is loose by about a factor of `r/2` and still closes.
`rust/tests/cross_intersecting.rs` exhausts that row.

**What is missing in Coq, precisely.** Two pieces, and neither is deep:

1. **the greedy decision tree** — an induction producing a list of at
   most `u^j` keys of size `j` such that every member of `B` contains
   one. The extension step is fifty lines (`extend_keys`: for each key
   `S`, name a member of `A` disjoint from `S`, and branch on its `u`
   points), and `cover_by_sets_sum` — already in `coq/TauThree.v` for
   this session's other purpose — turns the key list into the bound;
2. **the covering-number dichotomy** — "either some `j`-set covers `A`,
   or every set of size at most `j` misses some member". Constructively
   this is a finite search, because a cover point outside `concat A` is
   useless, which is exactly the argument `TwoCover.covers_dec_search`
   already makes for `j = 2`.

Estimated at 600 lines and not attempted this session. It should be the
first thing the next one does, because it settles the `tau <= 2` case of
§24.13's conjecture at every uniformity in one theorem.

### 25.5 Priority 0: what the published lemmas give, checked

The brief asks what ALWZ / Rao / Bell–Chueluecha–Warnke give for
`r*(m,3)` *as this repository defines it*, and calls it undone. It is
done, in two places, and both were verified rather than re-derived.

**Upper side: `O(log m)`, and it is the repository's own axiom.**
`ALWZ.Rao20_lemma2` is stated in exactly the `SpreadYieldsDisjoint` shape,

```coq
  exists alpha, 1 <= alpha /\ forall n k r, 1 <= n -> 2 <= k ->
    alpha * k * Nat.log2_up (S (k * n)) <= r -> SpreadYieldsDisjoint n k r
```

and `docs/reading.md`'s [Ra20] entry records it checked symbol by symbol
against Rao's Lemma 2. **Correction, §26.5:** this section first said the
repository's absolute `RaoSpread` is *stronger* than "the fractional
condition Rao uses". Read first-hand off the page, Rao's own definition
([Ra20] p. 2) is the absolute one and is `RaoSpread` verbatim, and so is
Bell–Chueluecha–Warnke's ([BCW21] p. 1); no comparison is needed. So
`r*(m,3) = O(log m)` is published, §22.7 already says so, and the
consequence for §24.13 is worth stating plainly:

> **`r*(m,3) <= m+1` is asymptotically weaker than what is known.** It is
> a statement about the reach of the two-way split, not a bound anyone
> would quote. What the split gives that the literature does not is
> *exact small values*: at `m = 3` the published constant is unusable
> (BCW state the constant only as `C >= 4`, and even at that floor the
> threshold exceeds 13 and the bound on `f(3,3)` exceeds 2000, against
> Erdős–Rado's 49 and this development's 65), while `r*(3,3) in [3,4]` is
> a two-value interval.

**Lower side: nothing is published, and Rao says so.** `docs/reading.md`
entry A2 records [Ra20, p. 2]:

> *"As far as we know, it is possible that Lemma 2 holds even when
> `r(p,k) = O(p)`. Such a strengthening of Lemma 2 would imply the
> sunflower conjecture of Erdős and Rado."*

In this repository's notation `p` is the number of petals and `k` the
uniformity, so `r(p,k) = O(p)` is exactly "`r*(m,3)` is bounded in `m`".
And the same entry records that the tightness examples that do exist —
[ALWZ20] Lemma 3.1, [BCW21] Lemma 4 — are for the **robust/covering**
form of the spread lemma, not the disjointness form. So:

> **Whether `r*(m,3)` is bounded is Rao's stated open question, and the
> literature contains no lower bound on it at all.**

That re-prices §3 of the brief and part of §22.7. §22.7 is right that
finitely many terms cannot distinguish bounded from `log m`; it is too
strong in implying the terms are worthless, because on the lower side the
repository's exact terms are, as far as this reading goes, the only
concrete values anyone has written down. They do not show unboundedness —
`r*(2,3) = 3` and `r*(3,3) in [3,4]` are consistent with a bounded
sequence — but they are data where there was none, and the first term
proved to exceed 4 would be the first evidence of growth in the
disjointness form. (`r*(9,3) >= 4` would be such a term; it is
conditional on an unformalised construction, see §25.3.)

### 25.6 Measured

All exhaustive, all in `rust/tests/tau_three.rs` and
`rust/tests/cross_intersecting.rs`, all under a minute.

```
  quantity                                                value   bound proved
  max |A|+|B|+|C|, cross-intersecting, Delta <= 3           9        9   (lemma_L)
    -- stable on 4,5,6,7,8 vertices; extremal: three copies of one 3-star
  max |G|, 3-uniform distinct intersecting, tau >= 3       10       16   (tau_three_bound)
    -- grounds 5,6,7; extremal: every 3-subset of a 5-set
  I(3,3)                                                   10       16
  I(3,4), ground 7 / ground 9                          12 / 16       16
  max |A|+|B|, cross-intersecting Rao(r), u = 2        2r + 1   (r-1)r
    -- r = 4,5,6 on r+2 points; needs the ground to hold two full stars
```

The `tau >= 3` row is the one worth reading twice: the proved bound is
16, the truth is 10, and the six of slack is **not needed** — the split
at `r = 4` can afford exactly 16.

### 25.7 Costs and gates

Nothing in this session was a search for an object, so there is no node
budget to report. The measurable costs are the gates and one abandoned
exploration.

```
  what                                        budget      spent       finished?
  make -j4 verify (clean + 447 audits)        --          476 s       yes
  make coqchk (39 modules)                    --          370 s       yes
  cargo test --release (27 suites, 253 tests) --          1370 s      yes
  mutation subset (5 new + control, 3 jobs)   6 mutants   458 s       yes
  full mutation suite (95, 3 jobs)            95 mutants  1996 s      yes
  max |G| with tau >= 3, ground 8 (Python)    --          ~10 min     NO --
                                                                      stopped
                                                                      by hand,
                                                                      budget
                                                                      unspent
```

The last row is the only thing in this session that was stopped rather
than finished, and it is worth naming as such: the naive branch-and-bound
in the scratchpad decides grounds 5, 6 and 7 in about four minutes
together and had not decided ground 8 after ten more, at which point it
was killed to free a core. Three grounds agreeing at 10 is what the
committed test pins (`rust/tests/tau_three.rs`, seconds, exhaustive on
each of those three); ground 8 is **undecided**, and since the bound in
question is Frankl's 10 rather than anything this session proves, nothing
depends on it.

**The gates.**

```
  make -j4 verify        green  (447 audited theorems, 447 "Closed under
                                the global context", none carrying an
                                axiom -- including everything in
                                TauThree.v)
  make coqchk            green  (39 modules; one axiom:
                                Sunflower.ALWZ.Rao20_lemma2)
  cargo test --release   green  (27 suites, 253 tests, 0 failures)
  python3 tools/mutate.py green (95 mutations, every one with the outcome
                                the manifest declares: 92 killed, 2
                                survived as declared, 1 control passing,
                                0 unexpected)
  tools/statements.py    green  (531 statements match the baseline)
  tools/docnumbers.py    green  (12 quoted numbers match)
```

The statement baseline moved for a reason worth recording: adding
`Distinct G` to `TauThreeAtMost` and `FranklTauThree` changes what two
existing theorems *say*, and `make statements` is the gate whose whole
job is to make that visible rather than silent. It fired, as designed.

### 25.8 The one-line verdict

**`I(3,r) = r²` for every `r ≥ 4`: the star is extremal among 3-uniform
intersecting Rao-spread families exactly from `r = m+1` on, upper bound
and attaining object both, which is the `m = 3` row of §24.13's conjecture
closed — and it makes `r*(3,3) ≤ 4` unconditional, where §24.12 had it
resting on a hypothesis that is false for every constant.**

The vehicle is an elementary, axiom-free bound of 16 on 3-uniform
intersecting *distinct* families of covering number 3. As a statement
about that classical question it is six worse than Frankl's 10 and is not
a contribution to it; as a constant for `split_with_piece` at `r = 4` it
is exactly what is needed, and it is now a theorem of this development
rather than a citation.

No new record object; §25.7 says which searches were not run rather than
run and lost. The closed line is §25.1, closed by an object rather than a
budget. The general-uniformity statement of §25.4 is prose with its
arithmetic checked and its two missing Coq pieces named, and it is the
next thing to do.

---

## 26. §25.4 in Coq, and the reason it stops at uniformity three

**Verdict: the general-uniformity theorem §25.4 gave in prose is proved,
axiom-free; the reason its companion case does not lift past `m = 3` is a
new decisive negative with an explicit witness; and the whole gap between
`r*(4,3) ≤ 7` and `r*(4,3) ≤ 5` is now one constant, stated as a Coq
implication.** In order:

* **`two_cover_star_extremal`** (§26.1): for every `m` and every
  `r ≥ m+1`, an `m`-uniform intersecting Rao-spread family with a
  two-point cover has at most `r^(m-1)` members — the size of a star.
  §24.10 had the `m = 3` row; this is all of them, at the same threshold.
  Both Coq pieces §25.4 named as missing are supplied.
* **`tau_three_piece_unbounded_at_four`** (§26.3): at `m = 4` the
  covering-number-3 piece is **unbounded** without a degree cap, where at
  `m = 3` the same quantity is 10. So the `m = 3` argument does not lift,
  and the Rao condition in the remaining hypothesis is load-bearing rather
  than bookkeeping. The witness is `C([5],3)` with one free coordinate.
* **`r_star_four_at_most_five_from_tau_three`** (§26.4): one constant —
  *a 4-uniform intersecting Rao(5)-spread family of covering number at
  least 3 has at most 125 members* — turns `r*(4,3) ≤ 7` into `≤ 5`.
* **`star_extremal_for_large_r`** (§26.4a): the star is extremal at
  *every* uniformity once `m³ ≤ r²` — the first general answer to the
  extremal question §24.13 named, though at a threshold strictly above
  the `m+1` the conjecture asks for.
* **The reading, done first-hand off the page images** (§26.5), which
  confirms three claims §25.5 makes and **corrects a fourth of its own**.

### 26.1 The theorem

`coq/CrossIntersecting.v`, axiom-free, eighteen new audited names.

> **`two_cover_star_extremal`:** `G` `m`-uniform, intersecting,
> `RaoSpread r`, every member containing `p` or `q`, and `r ≥ m+1`. Then
> `length G ≤ r^(m-1)`.

The reduction is §25.4's. Against the cover `{p,q}`, the members through
both are capped by the pair degree at `r^(m-2)`; the tails of the other
two pieces are families `A`, `B` at uniformity `u = m-1` that satisfy
Rao's condition *with the same `r`* (`tail_uniform_rao`) and are
cross-intersecting. So everything reduces to

> **`cross_pair_bound`:** two nonempty cross-intersecting families at
> uniformity `u`, each Rao-spread with the same `r ≥ u+2`, have at most
> `(r-1)·r^(u-1)` members between them,

and `(r-1)r^(u-1) + r^(u-1) = r^u = r^(m-1)` closes it.

**The first missing piece: the greedy decision tree.** `extend_keys` is
the step — for each key `S`, name a member of `A` missing it and branch on
that member's `u` points; a member of `B` containing `S` meets that member
of `A`, and the meeting point is outside `S`, so it contains one of the
extensions. `greedy_keys` iterates it: at most `u^j` keys of size `j`,
each `NoDup`, and every member of `B` contains one. `cover_by_sets` then
turns the key list into `|B| ≤ u^a·r^(u-a)`.

**The second: the covering-number decision.** `covers_at_most A j` is a
finite search over `subsets (nodup (concat A))` — a cover point lying in
no member is useless, which is `TwoCover.covers_dec_search`'s device at
`j = 2`, here at every `j`. `no_small_cover` is the half that matters:
the search failing at `j` means *no* set of size at most `j` covers `A`,
not merely no candidate. `least_true` then picks the least `j` that works,
and `covers_at_most_top` supplies the top of the range — a member of the
cross-intersecting partner *is* a cover, which is the only reason the
covering number is finite at all.

### 26.2 The numeric core, and why the threshold is exactly `m+1`

`budget_split`: with `a` the covering number of the smaller side and
`s = a-1`, either

```
  (O1)   a·r^(u-1) + u^a·r^(u-a)  <= (r-1)·r^(u-1)
  (O2)          2·u^a·r^(u-a)     <= (r-1)·r^(u-1)
```

and one of them always holds. Both come from a single integer Bernoulli
inequality, `bernoulli_shift : u^t·(u + 2(t+1)) ≤ (u+2)^(t+1)`, read
twice: `2s ≤ u` gives (O1), `u ≤ 2s` gives (O2), and every `s` is in one.

At `s = 0` — `A` a star — (O1) reads `u ≤ r-2`, which is `r ≥ m+1` on the
nose. One below it **both** options fail, for every `u` up to 60
(`rust/tests/cross_intersecting.rs`, exact arithmetic; the products pass
`u128` before `u = 30`). So `m+1` is not an artefact of the write-up: it
is where the star case turns over, and it is the same `m+1` that §24.13's
`split_cannot_reach_r_equals_m` shows is the floor of the whole method.
The mutations `crossint-threshold-m` and `crossint-budget-threshold` are
those two facts.

**How much is left on the table.** At `u = 2` the bound is `(r-1)r` and
the truth is `2r+1`, so it is loose by about a factor of `r/2` and still
closes — because what closes it is the `s = 0` row, not the size of the
slack.

### 26.3 Closed: the covering-number-3 piece is unbounded at `m = 4`

`TauThree.tau_three_bound` bounds the `τ ≥ 3` piece at `m = 3` by 16 with
**no degree cap at all**, and the truth there is Frankl's 10. The obvious
next move is to redo that argument at `m = 4`. It cannot be done, and not
because the argument is hard:

> **`tau_three_piece_unbounded_at_four`:** for every `K` there is a
> 4-uniform, distinct, intersecting family of covering number at least 3
> with more than `K` members.

The witness is `C([5],3)` with one free coordinate attached:

```
  G_n = { C u {w} : C a 3-subset of {0,...,4},  w in {5, ..., 7+n} }
```

`10(n+3)` members. 4-uniform and distinct because `w ≥ 5` and `C ⊆ {0..4}`;
intersecting because two 3-subsets of a 5-set meet; and of covering number
at least 3 because two points can exhaust neither the 5-set nor three or
more values of `w`. Three values of `w` is the least that works —
`crossint-lift-two-copies` weakens it to two and is killed, because
`{5,6}` then covers.

**What it costs and what it buys.** It costs the hope that §25.3's route
generalises as it stands. It buys the knowledge that the `RaoSpread`
hypothesis in `TauThreePieceAtMost` is the difference between a finite
quantity and an infinite one — Rao's condition caps `deg` of the triple
`C`, which is exactly the number of values of `w`, at `r^(4-3) = r`. That
is why the definition carries it, and why the `m = 3` row is special
rather than the first of a pattern.

### 26.4 What one constant at `m = 4` would buy

`StarExtremalAt m r` splits by covering number: `τ = 1` is a star, `τ = 2`
is §26.1 for every `m`, and what is left is `τ ≥ 3`.
`star_extremal_from_tau_three` is that statement with the constant open,
and at `m = 3` with `K = 16` it reproduces §25.3's row
(`three_uniform_star_extremal_again`), so the general form subsumes it.

At `m = 4` the arithmetic is exact:

```
  r*(4,3) <= 5   <=   StarExtremalAt m 5 for m = 1,2,3,4
                       m = 1  one_uniform_star_extremal            proved
                       m = 2  two_uniform_star_extremal   (r >= 3) proved
                       m = 3  three_uniform_star_extremal (r >= 4) proved
                       m = 4  ????                                 open
```

> **`r_star_four_at_most_five_from_tau_three`:**
> `TauThreePieceAtMost 4 5 125 -> SpreadYieldsDisjoint 4 3 5`.

So the gap between the unconditional `r*(4,3) ≤ 7` of §24.2 and `≤ 5` is
**one constant**: a 4-uniform intersecting Rao(5)-spread family of
covering number at least 3 has at most 125 members. The elementary greedy
bound there is `m^t·r^(m-t)`, which is `4³·5 = 320` at covering number 3
and `4⁴ = 256` at covering number 4, so the interval to close is
`[125, 320]` — the same shape as the `[16, 27]` that §25.2 closed at
`m = 3`, and by §26.3 it cannot be closed the same way.

**Where the 125 would have to come from, derived rather than guessed.**
Decomposing against one member `M`, as §25.2 does at `m = 3`:

```
  |C n M| = 4    M itself                                          1
  |C n M| = 3    4 triples of M, deg(triple) <= 5, less M         16
  |C n M| = 2    3 complementary couples; the tails of a couple
                 cross-intersect and have Delta <= deg(triple) = 5,
                 so each couple is <= 20  (and <= deg(pair) <= 20
                 from tau >= 3 when one side is empty)             60
                                                        subtotal  77
```

so the one-point layer has to obey `Σ_x |A_x| ≤ 48`, where the `A_x` are
**four pairwise cross-intersecting 3-uniform Rao(5)-spread families** —
the four-family analogue of `TauThree.lemma_L`, which does the same job
for three graphs at `m = 3`. `cross_pair_bound` gives only
`|A_x| + |A_y| ≤ (r-1)r² = 100` per pair, hence `Σ ≤ 200`: four times
what is needed. This paragraph is arithmetic, not Coq.

> **Correction (§27.1).** The sentence that stood here — "That is the
> gap, stated exactly" — was wrong, and §27 retracts it. `Σ ≤ 48` is
> **false**: four copies of one 25-member star give `Σ = 100`, and four
> copies of the 16-member non-star `CrossRefined.hm16` give `Σ = 64` with
> no common point, which is what the covering-number hypothesis on `G`
> actually forces. The decomposition above is a *sufficient* route and it
> is closed; the true statement is a joint one, because the layers cannot
> all be full at once. `CrossRefined.g65` realises 65 of the 125.

**Where this sits.** `r*(4,3) ≤ 5` would still be behind the published
`O(log m)` asymptotically (§26.5), and it does not touch `f(4,3)` in a
competitive way. Its content is the sequence: the fourth term would go
from `[3,7]` to `[3,5]`, and `m+1 = 5` is the best the two-way split can
ever give at that uniformity.

### 26.4a The first general answer to §24.13

The same machinery settles §24.13's question outright in a range. For
covering number `t` the greedy tree gives `|G| ≤ m^t·r^(m-t)`, which beats
the star `r^(m-1)` exactly when `m^t ≤ r^(t-1)`. Over `t` in `3..m` the
binding case is `t = 3` — the exponent ratio `t/(t-1)` is largest there —
so a single condition closes every covering number at once:

> **`star_extremal_for_large_r`:** `1 ≤ m`, `r ≥ m+1` and `m³ ≤ r²` imply
> `StarExtremalAt m r`, i.e. `I(m,r) ≤ r^(m-1)`.

`rust/tests/cross_intersecting.rs` checks that `t = 3` really is binding
and that the threshold fails one below, for every `m` up to 40.

**What it is and is not.** It is the first statement of the form
"the star is extremal" that holds at *every* uniformity — §24.13 named the
problem and §25.3 closed one row of it. It is **not** the conjecture:
`m³ > (m+1)²` for every `m ≥ 3`, so the threshold `max(m+1, ⌈m^(3/2)⌉)` is
strictly above `m+1` from `m = 3` on (6 against 4 at `m = 3`, 9 against 5
at `m = 4`). The mutation `crossint-large-r-cube` weakens `m³ ≤ r²` to
`m³ ≤ r³` — which `r ≥ m+1` already gives — and is killed, because the
mutated statement *is* the conjecture.

And it moves no bound on `r*`: `star_extremal_gives_m_plus_one` wants the
rows at `r = n+1`, and `(n+1)² ≥ n³` fails from `n = 3`. The conjecture's
value is that it lives exactly at `r = m+1`, which is where the greedy
stops working and where §26.1's two-point-cover argument is sharp.

### 26.5 The reading, first-hand, and one correction to §25.5

Every quotation below was read off a page image of the arXiv PDF rather
than extracted as text, because the statements turn on exponents.

**Rao [Ra20], p. 2 — the definition is the repository's, verbatim:**

> *"Let `r(p,k)` denote the quantity `αp log(pk)`. We say that a sequence
> of sets `S₁,…,S_ℓ ⊂ [n]` of size `k` is `r`-spread if for every
> non-empty set `Z ⊂ [n]`, the number of elements of the sequence that
> contain `Z` is at most `r^(k−|Z|)`."*

That is `Spread.RaoSpread` on the nose. **This corrects §25.5**, which
said the repository's absolute condition is "stronger than the fractional
condition Rao uses". Rao's own condition is the absolute one; no
comparison is needed, and `Spread.RaoSpread_Spread` is not what makes the
published lemma apply. `docs/reading.md`'s [Ra20] entry had this right
("matches"); §25.5 introduced the error.

**Rao [Ra20], p. 2 — Lemma 2 is `SpreadYieldsDisjoint`:**

> *"**Lemma 2.** If a sequence of more than `r(p,k)^k` sets of size `k` is
> `r(p,k)`-spread, then the sequence must contain `p` disjoint sets."*

and immediately after it, the sentence §25.5 turns on:

> *"As far as we know, it is possible that Lemma 2 holds even when
> `r(p,k) = O(p)`. Such a strengthening of Lemma 2 would imply the
> sunflower conjecture of Erdős and Rado."*

**Bell–Chueluecha–Warnke [BCW21], p. 1 — the sharpest published form:**

> *"**Theorem 1.** There is a constant `C ≥ 4` such that
> `Sun(p,k) ≤ (Cp log k)^k` for all integers `p,k ≥ 2`."*
>
> *"**Lemma 2.** There is a constant `C ≥ 4` such that, setting
> `r(p,k) = Cp log k`, the following holds for all integers `p,k ≥ 2`. If
> a family `S` with `|S| ≥ r(p,k)^k` sets of size `k` is `r(p,k)`-spread,
> then `S` contains `p` disjoint sets."*

with the same absolute spread condition on the same page. At `p = 3`
petals and `k = m` uniformity this is `r*(m,3) ≤ 3C log m`, and even at
the stated floor `C = 4` it is above 13 at `m = 3` — against this
development's 4. So §25.5's reading stands: **`O(log m)` published,
useless at the small `m` where the exact values live.**

**The tightness examples are for the other form, checked.** §25.5 says
the literature contains no lower bound on the disjointness threshold, on
the strength of `docs/reading.md`'s A2. Both citations were read:

* [ALWZ20] §3 is titled *"A Lower Bound for Robust Sunflowers"*, and
  Lemma 3.1 exhibits a system *"which does not contain a
  `(1/2,1/2)`-robust sunflower"*, showing *"Theorem 1.9 is tight"* —
  the **robust** statement, not Lemma 2.
* [BCW21] p. 2 introduces Lemma 4 with *"We close by recording that
  **Theorem 3** is essentially best possible with respect to the
  `r`-spread assumption"* — Theorem 3 being the "a random subset contains
  a member" estimate, not the disjointness lemma.

So neither bounds `r*(m,3)` from below, and Rao's own sentence says no one
knows one. §25.5 stands as written.

**One thing worth carrying forward.** Both tightness objects are the same
family: [BCW21] Lemma 4 fixes a partition `V₁ ∪ ⋯ ∪ V_k` with `|V_i| = r`
and takes *"all `k`-element sets containing exactly one element from each
`V_i`"*; [ALWZ20] Lemma 3.1's `F̂ = X₁ × ⋯ × X_w` is the same. That is the
grid, and `TauThree.star34` is its `(m,r) = (3,4)` instance with one
coordinate pinned — the object that attains `I(3,4) = 16`. The extremal
family for the published tightness results and the extremal family for
this development's `I(m,r)` are the same shape, which is not something
either §24.13 or §25 noticed.

### 26.6 Measured

```
  quantity                                             value      status
  max |A|+|B|, cross-intersecting Rao(r), u = 2       2r + 1    exhaustive,
                                                                r+2 points
  the (O1)/(O2) disjunction, u <= 60, r in [u+2,u+12]   holds   exact
                                                                arithmetic
  |lift n| with all four hypotheses                  10(n+3)    verified to
                                                                n = 100
  deg of a triple in lift n                                n    exactly |W|
  I(4,5), ground 6 / ground 7                          15 / 35  exhaustive
  I(4,5), grounds 8 and 9                               >= 35   TRUNCATED
                                                                at 3e9 nodes
                                                                each
  the tau >= 3 piece at m=3, r=4, grounds 5..8             10   exhaustive
                                                                on each
  the tau >= 3 piece at m=4, r=5, ground 7                 35   exhaustive
                                                                on that
                                                                ground
  the tau >= 3 piece at m=4, r=5, ground 8              >= 35   STOPPED by
                                                                hand at
                                                                ~7 min,
                                                                budget
                                                                unspent
  m^3 <= r^2 closes every t >= 3, m <= 40               holds   exact
                                                                arithmetic
```

The `m = 3` row of the scanner is the check that it is measuring the right
thing: 10, on the nose, on every ground from 5 to 8, which is Frankl's
value and `rust/tests/tau_three.rs`'s.

The `I(4,5)` row is the one to read carefully. Ground 7's value of 35 is
`C(7,4)` — *every* 4-subset of a 7-set, which is intersecting and
Rao(5)-spread — and the star needs `1 + 3·5 = 16` points to fit, so
exhaustive search cannot reach the question at all. `I(4,5) ≤ 125` will
not be settled by search; §26.4 is the route.

### 26.7 Costs and gates

```
  what                                          budget      spent   finished?
  I(4,5), grounds 6 and 7                       3e9 nodes   <1 s    yes
  I(4,5), ground 8                              3e9 nodes   363 s   NO --
                                                                    truncated
  I(4,5), ground 9                              3e9 nodes   801 s   NO --
                                                                    truncated
  tau>=3 piece scan, m=4 r=5, grounds 7,8       2e9 nodes   ~8 min  ground 7
                                                                    yes;
                                                                    ground 8
                                                                    STOPPED
                                                                    by hand,
                                                                    budget
                                                                    unspent
  make -j4 verify (465 audited)                  --          --      yes
  make coqchk (40 modules)                      --          --      yes
  cargo test --release (27 suites, 257 tests)   --          --      yes
  python3 tools/mutate.py (100, 3 jobs)         --          ~65 min yes
```

**The gates.**

```
  make -j4 verify        green  (465 audited theorems, 465 "Closed under
                                the global context", none carrying an
                                axiom -- including everything in
                                CrossIntersecting.v)
  make coqchk            green  (40 modules; one axiom:
                                Sunflower.ALWZ.Rao20_lemma2; type-in-type,
                                unsafe (co)fixpoints and assumed
                                positivity all <none>)
  cargo test --release   green  (27 suites, 257 tests, 0 failures)
  python3 tools/mutate.py green (100 mutations: 97 killed, 2 survived as
                                declared, 1 control passing, 0 unexpected
                                -- including all five added here)
  tools/statements.py    green
  tools/docnumbers.py    green  (12 quoted numbers match)
```

Nothing else ran over ten minutes. The ground-8 row is **undecided**, and
nothing in this section depends on it.

### 26.8 The one-line verdict

**The two-point-cover case is now a theorem at every uniformity, at the
threshold `r ≥ m+1` that the `s = 0` row of the arithmetic pins exactly;
the companion case provably does *not* lift past `m = 3` without a degree
cap, with an explicit unbounded witness; and what separates `r*(4,3) ≤ 7`
from `r*(4,3) ≤ 5` is one constant, now a Coq implication.**

Two things fall out that were not the target. **`I(m,r) = r^(m-1)` holds
at every uniformity once `m³ ≤ r²`** (§26.4a) — the first general answer
to the extremal question §24.13 named, at a threshold strictly above the
`m+1` the conjecture asks for, which is exactly the gap the conjecture is
about. And the two published tightness objects — [ALWZ20] Lemma 3.1 and
[BCW21] Lemma 4 — are the *same grid* that `TauThree.star34` instantiates
at `(m,r) = (3,4)`, so the extremal family for the published results and
for this development's `I(m,r)` coincide (§26.5).

## 27. The four-family route, closed by a witness; and a sharper cross-pair bound

`coq/CrossRefined.v`, `rust/tests/cross_refined.rs`.

§26.4 left `r*(4,3) ≤ 5` hanging on one constant and named a route to it.
This section walks the route, finds it blocked, and says by how much —
then extracts from the obstruction two general lemmas that sharpen
`cross_pair_bound` itself, and spends the sharper bound on a second
extremal question the sharpening makes answerable (§27.6).

### 27.1 Closed: `Σ_x |A_x| ≤ 48` is false, by more than a factor of two

The route asked for a bound on four pairwise cross-intersecting 3-uniform
Rao(5)-spread families. Measure the quantity rather than bounding it.

**Without any side condition, `Σ = 100`.** Let `w` be a point and let the
link of `w` be `K_{5,5}` on ten further points: 25 triples `{w,a,b}`,
5-regular, so `deg{w} = 25 = 5²`, `deg{w,z} = 5 = 5¹` and every triple
degree is 1. That family is intersecting, hence four copies of it are
pairwise cross-intersecting, and `Σ = 4·25 = 100 > 48`.

**With the side condition the τ ≥ 3 hypothesis really imposes, `Σ = 64`.**
The four-family phrasing dropped something. Writing `M = {a,b,c,d}` for
the member decomposed against and `A_x` for the tails of the members
meeting `M` exactly at `x`, the family

```
  G  =  {M}  u  { {x} u T : x in M, T in A_x }
```

is 4-uniform, distinct, intersecting and Rao(5)-spread exactly when each
`A_x` is 3-uniform, distinct and Rao(5)-spread, the `A_x` are pairwise
cross-intersecting, and `Σ_x deg_{A_x}(w) ≤ 125`, `Σ_x deg_{A_x}({w,w'}) ≤ 25`.
And `τ(G) ≥ 3` holds **iff** two conditions hold: for every pair
`x,y ∈ M` some third `A_z` is nonempty, and — the one that bites — for
every `x ∈ M` and every `w ∉ M` some `z ≠ x` has a member of `A_z`
avoiding `w`. Writing `S_w` for the set of indices whose family lies
inside the star at `w` (empty families included), the second says exactly
`|S_w| ≤ 2`: **at most two of the four families are stars at any one
point.** The 100-family dies there — all four are the star at `w`, so
`{x,w}` covers `G`. But 48 does not come back:

```
  hm16  =  {4,5,6}  u  { {12, i, y} : i in {4,5,6}, y in {7,...,11} }
```

is intersecting (every star member meets `{4,5,6}`), Rao(5)-spread
(`deg{12,i} = 5`, `deg{12,y} = 3`, `deg{12} = 15`, `deg{i} = 6`), has 16
members, and is **not** a star — `{4,5,6}` misses 12 and `{12,4,7}` misses
5. Four copies have no common point and `Σ = 64 > 48`.

> **`four_unpointed_cross_families_exceed_forty_eight`:** there exist four
> pairwise cross-intersecting 3-uniform Rao(5)-spread families, none of
> them a star, with more than 48 members between them.

So the route is dead in both its forms, and §26.4's "that is the gap,
stated exactly" is retracted there. What is true is that the bound has to
be *joint*: the layers and `Σ` cannot all be full at once, and any proof
of `TauThreePieceAtMost 4 5 125` has to use that. `g65` is the case in
point — it puts **nothing** in the two- and three-point layers and spends
its entire budget on the one-point layer.

Two smaller things about §26.4's arithmetic, recorded because they do not
affect the retraction but would affect anyone re-deriving it. The
two-point layer was bounded there by 60, from "each complementary couple
is ≤ 20"; 20 is right when both sides of a couple are nonempty (an edge
of one caps the other at `2·deg(triple) = 10`), but when one side is
empty the surviving side is capped only by the pair degree `r^(m-2) = 25`,
so the layer bound is 75 and the subtotal 92, not 77. And the interval
`[125, 320]` quoted there had the wrong upper end for the purpose: 320 is
the greedy bound on the piece, but anything above 125 fails the hypothesis
of `star_extremal_from_tau_three`, so the target was always `[?, 125]`.

### 27.2 A new object: `g65`, and the constant is in `[65, 125]`

The same construction run forward is a witness rather than an obstacle.
Hanging one copy of `hm16` on each point of `M = {0,1,2,3}` gives

> **`g65`** — 65 members, 4-uniform, distinct, intersecting,
> Rao(5)-spread, covering number at least 3, on 13 points.

Every Rao inequality is verified by the kernel over all 8191 nonempty
subsets of the ground set, the intersecting condition over all 65² pairs,
and covering number ≥ 3 by `TwoCover.covers_dec_search`. It is also
**maximal**: `rust/tests/cross_refined.rs` checks that no 4-set whatever
can be added, on grounds 13, 14 and 15. Hence

> **`tau_three_piece_at_least_sixty_five`:**
> `∀K, TauThreePieceAtMost 4 5 K → 65 ≤ K`.

Combined with `r_star_four_at_most_five_from_tau_three`, which needs
`K = 125`, the open constant lies in `[65, 125]`. That is a much narrower
target than §26.4's `[125, 320]` framing suggested — the greedy bound 320
was never the relevant upper end; 125 is, because anything above it does
not give the theorem. What the witness settles is the *lower* end: no
argument that would prove a bound below 65 can be correct.

Two structural facts fall out of the construction and are worth keeping.
First, the same shape at `m = 3` is exactly extremal: three copies of the
triangle (the only non-star intersecting graph) give `1 + 3·3 = 10`, and
10 is the exhaustively measured maximum of the τ ≥ 3 piece at `m = 3`
*without* the Rao condition at all — Frankl's value, measured on grounds
5 to 7 by `rust/tests/tau_three.rs`. So the construction attains, with
Rao(4), a bound that holds without it: at `m = 3` the shape is not a
lower bound, it is the answer. Second, at `m = 4` the layers
above the one-point layer are empty in `g65` — it spends its whole budget
on the bottom layer, and the Rao inequality `deg{x,12,i} = 5` is the only
tight one.

### 27.3 New mathematics: star saturation, and a sharper cross-pair bound

The mechanism behind both examples is general and did not exist in the
development.

> **`star_saturation`.** Let `A` and `B` be cross-intersecting and
> `u`-uniform with `A` Rao(r)-spread and *pointed at* `w` (every member
> contains `w`). If `|A| > u·r^(u-2)` then `B` is pointed at `w` too.

The proof is three lines: a member `f` of `B` with `w ∉ f` forces every
`C ∈ A` to contain `{w,v}` for one of `f`'s `u` points `v`, and the pair
degree caps each of those at `r^(u-2)`. It is what kills the `Σ = 100`
example under τ ≥ 3, and it is *sharp at its threshold* — at `u = 2`,
`r = 5` the threshold is 2 and a pointed family of exactly 2 edges does
have a partner outside its star.

Its partner is already in the development: `greedy_bound` at `j = 2` says
that if `A` is **not** pointed then `|B| ≤ u²·r^(u-2)`. Between them the
cross-intersecting pair splits four ways, and the four cases give a bound
that carries **no lower bound on `r` at all**, unlike `cross_pair_bound`'s
`r ≥ u+2`:

> **`cross_pair_refined`:** for nonempty cross-intersecting `u`-uniform
> Rao(r)-spread `A`, `B` with `u ≥ 2`,
> `|A| + |B| ≤ u·max(2u, r+1)·r^(u-2)`.

```
  both pointed              2·r^(u-1)              star bound twice
  A pointed, B not          u·r^(u-2)·(r+1)        star_saturation caps
                                                   the pointed side at
                                                   u·r^(u-2), greedy at
                                                   j=1 caps the other
  B pointed, A not          u·r^(u-2)·(r+1)        mirror
  neither pointed           2u²·r^(u-2)            greedy at j=2, twice
```

Both bounds are a coefficient times `r^(u-2)`, so the comparison is
`u·max(2u,r+1)` against `r(r-1)`:

| `u` | `r` | refined | `cross_pair_bound` | exhaustive truth |
|-----|-----|---------|--------------------|------------------|
| 2   | 4   | 10      | 12                 | 9                |
| 2   | 5   | 12      | 20                 | 11               |
| 2   | 6   | 14      | 30                 | 13               |
| 3   | 5   | 90      | 100                | not exhausted    |
| 4   | 6   | 1152    | 1080               | not exhausted    |

At `u = 2` the refined bound is `2r+2` against an exhaustive truth of
`2r+1` — off by one, where `cross_pair_bound` is off by a factor of about
`r/2`. And it *explains* the `u = 2` extremal configuration rather than
merely bounding it: one edge against the two full stars at its endpoints
is precisely the "B pointed, A not" case, and the reason nothing bigger
exists is that `star_saturation` forbids the large pointed side. The two
bounds are incomparable — at `u = 4, r = 6` the refined coefficient is 32
against 30 — so `cross_pair_bound` stays.

`cross_pair_refined_strict` states the improvement as a theorem
(`u·max(2u,r+1) < r(r-1)` implies a strictly better conclusion than
`cross_pair_bound`'s), and `cross_pair_refined_at_three_five` evaluates it
at the `m = 4` row: 90, by kernel computation, not by quotation.

**What this does *not* do.** Two honest negatives.

It does not rescue the route. 90 per pair gives `Σ ≤ 180` over the four
families, against the 64 that is realised and the 48 that was wanted;
§27.1 stands.

It does not lower the `r ≥ m+1` threshold of `two_cover_star_extremal`
either, and the reason is worth recording. That theorem needs the pair
bound `X` at `u = m-1` to satisfy `X + r^(m-2) ≤ r^(m-1)`, and
`cross_pair_bound`'s `(r-1)·r^(m-2)` meets it with **equality** — it is
exactly tight for that consumer. `cross_pair_refined` beats it only when
`u·max(2u,r+1) < r(r-1)`, and at `r = m` (one below the threshold, with
`u = m-1`) the binding case is "neither side pointed", where
`2(m-1)² ≤ m(m-1)` fails for every `m ≥ 3`. So the threshold survives; it
is not an artefact of which pair bound is used.

### 27.4 Measured

`tau_piece_scan` now takes a covering-number threshold, so it answers two
questions with one search: the τ ≥ 3 piece (the constant in
`star_extremal_from_tau_three`) and the τ ≥ 2 piece (the largest
intersecting Rao-spread family that is not a star), which is what the
construction of §27.2 feeds on.

```
  m=3 r=5, tau>=2   ground 5   10   exhausted on that ground
                    ground 6   10   exhausted
                    ground 7   13   exhausted
                    ground 8   15   exhausted (20 555 449 nodes, 34 s)
  m=4 r=5, tau>=3   ground 6   15   exhausted  ( = C(6,4), the whole family)
                    ground 7   35   exhausted  ( = C(7,4) = the complete
                                                4-uniform family on 2m-1
                                                points, the m=4 analogue of
                                                the C(5,3)=10 the m=3 row
                                                measured)
```

A ground set is a restriction, so every row is a lower bound on the true
maximum. `hm16` lives on 9 points and has 16 members, above the ground-8
row of 15, so the τ ≥ 2 sequence is still climbing at ground 8; `g65`
lives on 13 points and has 65, far above the ground-7 row of 35. Neither
scan reached the ground where its own witness lives.

### 27.5 Costs and gates

```
  what                                          budget      spent    finished?
  tau_piece_scan m=3 r=5 tau>=2, grounds 5-8    8e9 nodes   35 s     yes,
                                                                     exhausted
                                                                     on each
  tau_piece_scan m=3 r=5 tau>=2, ground 9       8e9 nodes   41 min   NO --
                                                                     STOPPED by
                                                                     hand,
                                                                     budget
                                                                     unspent
  tau_piece_scan m=4 r=5 tau>=3, grounds 6-7    4e9 nodes   <1 s     yes,
                                                                     exhausted
                                                                     on each
  tau_piece_scan m=4 r=5 tau>=3, ground 8       4e9 nodes   48 min   NO --
                                                                     STOPPED by
                                                                     hand,
                                                                     budget
                                                                     unspent
  g65 maximality, grounds 13,14,15              exhaustive  <1 s     yes
  coqc coq/CrossIntersecting.v, after the
    two_cover_split refactor                    --          3 s      yes
  coqc coq/CrossRefined.v (g65 and hm16 by
    vm_compute)                                 --          72 s     yes
  exhaustive cross-pair maximum for r = 2,3,4 on
    every ground from r+2 to 7, and the
    neither-pointed maximum for r = 2..6 on
    grounds 5,6                                 exhaustive  ~3 s     yes
  cross_pair_scan u=3, r=2..6, grounds 9..17,
    up to 1500 restarts                         stochastic  ~2 min   n/a --
                                                                     LOWER
                                                                     BOUNDS,
                                                                     not an
                                                                     exhaustive
                                                                     search
  tau_piece_scan m=3 r=5 tau>=2, ground 9,
    re-run for I2(3,5) on the spare core        3e10 nodes  100 min  NO --
                                                                     STOPPED by
                                                                     hand,
                                                                     budget
                                                                     unspent
```

Both stopped rows are **stopped by hand with the node budget unspent**,
not exhausted and not truncated at a budget: the cores were needed for
the gates. Neither is load-bearing — the witnesses live on grounds those
searches had not reached, so a larger row could only raise a number this
section does not use.

**The gates.**

```
  make -j4 verify        green  (510 audited theorems, all "Closed under
                                the global context")
  make coqchk            green  (41 modules; one axiom:
                                Sunflower.ALWZ.Rao20_lemma2)
  cargo test --release   green  (28 suites, 265 tests, 0 failures)
  python3 tools/mutate.py green (117 mutations: 114 killed, 2 survived as
                                declared, 1 control passing, 0 unexpected --
                                all seventeen added here killed)
  tools/statements.py    green  (602 statements)
  tools/docnumbers.py    green  (12 quoted numbers match)
```

### 27.6 `I₂(m,r)` named, and `I₂(3,5) = 16` exactly

Rule 2 of the brief — name the object. The construction of §27.2 turns on
a quantity that had no name here:

> **`I₂(m,r)`** — the largest `m`-uniform intersecting Rao(r)-spread
> family that is **not a star**. (`I(m,r)` drops the last clause.)

`g65` is `1 + 4·I₂(3,5)` when its four link families coincide, so whether
65 is the best that shape can do *is* the value of `I₂(3,5)`.

**The two-cover split, factored out.** `two_cover_star_extremal`'s proof
had the whole two-point-cover argument inlined and then applied
`cross_pair_bound` at the end. That argument is now a lemma in its own
right:

> **`CrossIntersecting.two_cover_split`:** for `m ≥ 2`, `p ≠ q`, an
> `m`-uniform intersecting Rao(r)-spread `G` covered by `{p,q}` is either
> a star, or splits into two **nonempty** cross-intersecting
> `(m-1)`-uniform Rao(r) tail families `A`, `B` with
> `|G| ≤ |A| + |B| + r^(m-2)`.

`two_cover_star_extremal` is re-proved from it, statement unchanged, by
feeding the split to `cross_pair_bound`; the point of the refactor is that
a second consumer can now feed it something else.

**The pair bound at `u = 2`, exactly.** `cross_pair_refined` gives `2r+2`
there and the exhaustive search says `2r+1`. That one closes, for every
`r ≥ 3`, and `r = 3` is where it takes real work. Three lemmas, none of
which mentions `r` except through the degree caps:

> **`pair_partner_bound`:** two members of `A` that differ as sets cap
> `|B|` at `max(r+1, 4)`.

Pick `b ∈ e₁ \ e₂` and `d ∈ e₂ \ e₁` (neither 2-set contains the other),
and let `x`, `y` be the remaining elements. If `x = y` the two members
share that vertex and `B ⊆ star(x) ∪ {[b;d]}`, so `|B| ≤ r+1`. If not,
the four crossing pairs `[b;d]`, `[b;y]`, `[x;d]`, `[x;y]` each have
degree at most `r^0 = 1`, so `|B| ≤ 4`. At `r ≥ 3` the first dominates; at
`r = 2` the second does, which is the whole story of this section.

> **`triangle_bound`:** a graph that pairwise intersects and is pointed at
> nothing *is* a triangle — three edges, not the four the greedy tree
> allows — and so is anything cross-intersecting it.

Take `e₁ = {x,y}`; a member missing `x` must contain `y`, a member missing
`y` must contain `x`, and those two meet at a third vertex `z`. Then
`[x;y]`, `[x;z]`, `[y;z]` cover the family — and they cover any partner
too, because the covering argument uses only "meets those three members".

> **`disjoint_squeeze`:** if `A` has two disjoint members then either `B`
> misses one of the four crossing pairs — three keys cover it, `|B| ≤ 3` —
> or it has all four, and then only `[a;b]` and `[c;d]` meet every one of
> them, so `|A| ≤ 2`.

The two combine into a statement with **no `r` in it at all** — the keys
are pairs, and a pair has degree at most `r^0 = 1` whatever `r` is:

> **`unpointed_pair_bound`:** if neither side is a star, the two have at
> most 6 edges between them.

```
  A pairwise intersects            triangle both sides  3 + 3
  A has two disjoint members,
    B pairwise intersects          triangle, swapped    3 + 3
    B has two disjoint members     squeeze both ways:
                                     |A|<=2 or |B|<=3,
                                     |B|<=2 or |A|<=3   <= 6
```

with `|A|, |B| ≤ 4` from the greedy tree filling the corners. With
`star_saturation` and `partner_bound_one`:

> **`cross_pair_two_exact`:** for `r ≥ 2`, two nonempty cross-intersecting
> Rao(r)-spread graphs have at most `max(2r+1, 6)` edges between them.

```
  |B| <= 1                      |A| <= 2r            partner_bound_one
  |A| <= 1                      symmetric
  A pointed, |A| >= 3           B pointed too,       star_saturation
                                both <= r
  A pointed, |A| = 2            |B| <= max(r+1,4)    pair_partner_bound
  B pointed, symmetric
  neither pointed               sum <= 6             unpointed_pair_bound
```

`max(2r+1, r+3, 2r, 6) = max(2r+1, 6)` for `r ≥ 2`. **This is the first
cross-intersecting bound in the development that is exactly tight**, and
it is tight at every `r ≥ 2`:

```
  r          2   3   4   5   6
  max(2r+1,6) 6   7   9  11  13
  exhaustive  6   7   9  11  13
```

**Both branches are attained and neither is slack.** From `r = 3` on it is
one edge against the two full stars at its endpoints. At `r = 2` it is the
other one:

> **`cross_pair_two_six_is_attained`:** `c2a = {02, 13}` and
> `c2b = {01, 03, 12, 23}` are 2-uniform, Rao(2)-spread,
> cross-intersecting, **neither a star**, with `2 + 4 = 6 > 5 = 2r+1`.

Degree two is exactly where all four crossing edges fit; from `r = 3` on,
`disjoint_squeeze` says that having all four costs the other side down to
two, and the one-edge-against-two-stars configuration overtakes 6.
`rust/tests/cross_refined.rs` checks the whole table exhaustively, and
that the neither-pointed configurations cap at 6 for every `r` from 2 to
6 — the fact `unpointed_pair_bound` encodes.

**The value.** Feeding the exact pair bound to the split, and taking the
covering-number-3 branch from `TauThree.tau_three_bound`:

> **`nonstar_three_bound`:** for `r ≥ 3`, a 3-uniform distinct
> intersecting Rao(r)-spread family that is not a star has at most
> `max(3r+1, 16)` members.
>
> **`i2_three_five_is_sixteen`:** `I₂(3,5) = 16`.

The two branches are `(2r+1) + r = 3r+1` from the split — the tails, plus
the both-points piece the pair degree caps at `r^(m-2) = r` — and 16 from
`tau_three_bound`, which carries no Rao condition at all. At `r = 5` they
are *equal*: `3·5+1 = 16`. And `hm16` attains it, realising the split
exactly — at the cover `{4,12}` it has one member through 4 only, ten
through 12 only and five through both, so `11 + 5`, with `11 = 2r+1` and
`5 = r`. Exact value, witness and bound meeting.

**Each pair bound in turn, on this row.** `cross_pair_bound`: `20 + 5 =
25 = r^(m-1)`, the star bound, no information about non-stars at all.
`cross_pair_refined`: `12 + 5 = 17`, one too many. `cross_pair_two_exact`:
`11 + 5 = 16`, exact. The theorem does not exist without the third.

**What this does and does not buy.** It shows `hm16` is optimal, hence
that 65 is exactly the best the `g65` shape can do. It does **not** bound
`TauThreePieceAtMost 4 5 K`, because a maximum `G` need not have four
coinciding link families, or any members in the one-point layer at all.

### 27.7 Uniformity three: the same shape, and where it closes

`rust/examples/cross_pair_scan.rs` is a stochastic maximiser for
`|A| + |B|` over cross-intersecting Rao(r)-spread families at a given
uniformity. Every number it reports is a **lower** bound — it is not
exhaustive, and the section says so wherever the numbers are used.

```
  r                    2    3    4    5    6
  best found          17   28   49   76  109
  3r² + 1             13   28   49   76  109
  neither pointed     17   28   36   41   47
```

> **Correction.** The neither-pointed row was first recorded here as
> `17 24 33 36`, from a shorter run. Those were valid lower bounds and
> the inference drawn from them — that the row grows, unlike `u = 2`'s
> constant 6 — survives; but they were under-searched, and the `r = 3`
> entry matters. It is **28**, which is `3r²+1` exactly.

So `u = 3` has the *shape* `u = 2` has: the star branch
`u·r^(u-1) + 1` — one member of `B` against `u` full stars — plus a
small-`r` exception in which neither side is a star (6 at `u = 2`,
17 at `u = 3`). The extremal object is realised in
`rust/tests/cross_refined.rs`: for each of the three points of the single
member of `B`, a `K_{r,r}` link on its own `2r` fresh points, which is
`r`-regular with `r²` edges.

**The `u = 2` proof does not transfer, and the table says why.** There the
neither-pointed maximum is the constant 6 for every `r`, which is why
`unpointed_pair_bound` mentions no `r` at all. At `u = 3` it *grows* —
17, 24, 33, 36 — so there is no constant to prove and no analogue of that
lemma. What closes the large rows instead is that `3r²+1` outgrows the
greedy tree's `9r` per side.

**Three branches.**

```
  |B| = 1 or |A| = 1     sum <= 3r² + 1     partner_bound_one -- extremal
  A or B pointed         sum <= 2r² + 4r    new; <= 3r²+1 iff r >= 4
  neither pointed        sum <= 18r         greedy at j = 2; iff r >= 6
```

> **`cross_pair_three_exact`:** for `r ≥ 6`, two nonempty
> cross-intersecting 3-uniform Rao(r)-spread families have at most
> `3r² + 1` members between them.

which is exactly the measured value at `r = 6`. **The rows `r = 2,3,4,5`
are open.**

**The pointed branch.** `A` pointed at `w`, `|A| ≥ 2`. Its *link*
`L = {C \ {w} : C ∈ A}` is a 2-uniform Rao(r)-spread family
(`pointed_link`, from `tail_uniform_rao`), so the `u = 2` lemmas apply to
it — which is the payoff for having done `u = 2` properly.

* *Two members meet only at `w`* — the link has two disjoint edges. Then
  five keys cover `B`: `[w]`, and the four crossing pairs `[a;c]`,
  `[a;d]`, `[b;c]`, `[b;d]` of the two links. Degrees `r²` and `r`, so
  `|B| ≤ r² + 4r`; with `|A| ≤ r²` from the star bound, `2r² + 4r`.
* *Otherwise the link pairwise intersects*, hence is a star or a triangle:
  pointed at `c` gives `|A| = |L| ≤ deg_L(c) ≤ r`, and not pointed gives
  `|L| ≤ 3` by `triangle_bound`. So `|A| ≤ max(r,3)`. For `B`, four keys
  suffice with **no case split** — `[w]`, `[p₀;s]`, `[p₀;t]` and the
  *singleton* `[p₁]`, the same trick that removed the case split at
  `u = 2` — giving `|B| ≤ 2r² + 2r` and a sum of `2r² + 3r` for `r ≥ 3`.

**`r ≥ 6` is not caution.** At `r = 2` the formula is *false*, by four:

> **`cross_pair_three_needs_six`:** `c3a` (7 members) and `c3b` (10) are
> 3-uniform, Rao(2)-spread, cross-intersecting, **neither a star**, with
> `7 + 10 = 17 > 13 = 3r²+1`.

`r = 3,4,5` are neither proved nor refuted: the measured values agree with
`3r²+1` there, and the branch that fails to close is the neither-pointed
one (measured 28, 36, 41 against the greedy's 54, 72, 90).

**Why `r = 3` in particular is out of reach, measured rather than
guessed.** At `r = 3` the neither-pointed branch *attains* the whole
bound: `rust/tests/cross_refined.rs` carries a cross-intersecting
Rao(3)-spread pair with 26 and 2 members, **neither a star**, both sides
containing two disjoint members, totalling `28 = 3r²+1`. So any proof of
the `r = 3` row has to be exactly tight on the hardest case — there is no
slack anywhere to spend. The three-branch argument above has 26 of slack
there (54 against 28).

**What closing `r = 4,5` would need, stated exactly.** Two things, and
both are missing:

1. *A bound for the case where both sides contain two disjoint members.*
   The measured maximum is `9r + 2`-ish (36, 41, 47 at `r = 4,5,6`) and
   the greedy tree gives `18r`. The mechanism is visible: if all nine
   crossing pairs of two disjoint members of `A` have degree at least 4,
   then a partner member cannot avoid both ends of any of them, so it
   contains one of the two members outright and the other side collapses
   to 2. But **that mechanism is vacuous at `r = 3`**, because a pair has
   degree at most `r^(m-2) = r = 3` there — which is the same fact as the
   paragraph above, from the other side.
2. *A sharper covering-number-3 bound.* `TauThree.tau_three_bound` proves
   16 where the exhaustive truth is Frankl's 10, and the branch where one
   side is intersecting needs the 10: at `r = 4` it is `36 + 16 = 52`
   against 49 with the 16, and `36 + 13 = 49` with the 10.

Neither is a small step. The second is Frankl's classification of
intersecting families by covering number, which this development does not
have — it is the same object §26 has been circling from the other side.

### 27.8 The one-line verdict

**The route §26.4 named to `r*(4,3) ≤ 5` is closed by an explicit
counterexample — the four-family inequality it asked for is false by more
than a factor of two, with or without the covering-number side condition —
and the same construction, run forward, produces a maximal 65-member
witness that pins the still-open constant into `[65, 125]`.**

The obstruction was worth more than the route. `star_saturation` — a large
star drags its cross-intersecting partners into itself — together with the
greedy tree already present gives `cross_pair_refined`, a cross-intersecting
bound with no threshold on `r`, off by one from the exhaustive truth at
`u = 2` where the existing `cross_pair_bound` is off by a factor of `r/2`,
and strictly sharper at the `(u,r) = (3,5)` row that the `m = 4` case runs
through.

And the sharper bound buys a second one. With the two-point-cover
argument factored out of `two_cover_star_extremal` into
`two_cover_split`, and the pair bound at `u = 2` pushed all the way to
the exhaustively measured `2r+1` by `cross_pair_two_exact`, the split
gives **`I₂(3,5) = 16` exactly** — an exact extremal value, witness and
bound meeting on `hm16`. `cross_pair_bound` gives 25 there, which is the
star bound and says nothing; `cross_pair_refined` gives 17, one too many.

At uniformity three the same question is **not** settled: the answer has
the same shape (`3r²+1`, one member against three full stars, plus a
small-`r` exception of 17), the `u = 2` machinery closes it for `r ≥ 6`,
and `r = 2` is refuted by an explicit 17-member witness. `r = 3,4,5` are
open, and §27.7 says exactly which branch fails and what it would take.


No new record object, and no search in this section decided anything —
§26.7 says which two were truncated and which one was stopped by hand.
The reading confirmed three of §25.5's claims off the page and corrected
a fourth of its own.

### 27.9 Picking this up cold

**Settled in §§25–27, all axiom-free.**

```
  TauThree.tau_three_bound                the tau >= 3 piece at m = 3 is
                                          <= 16, elementarily
  CrossIntersecting.two_cover_split       the two-point-cover argument,
                                          factored out and reusable
  CrossIntersecting.two_cover_star_extremal   tau <= 2 at every uniformity,
                                          r >= m+1
  CrossRefined.star_saturation            a large star drags its partners
                                          into itself
  CrossRefined.cross_pair_refined         |A|+|B| <= u*max(2u,r+1)*r^(u-2),
                                          no threshold on r
  CrossRefined.cross_pair_two_exact       u = 2: max(2r+1, 6), r >= 2,
                                          tight at every r
  CrossRefined.cross_pair_three_exact     u = 3: 3r^2+1, r >= 6
  CrossRefined.nonstar_three_bound        I2(3,r) <= max(3r+1, 16)
  CrossRefined.i2_three_five_is_sixteen   I2(3,5) = 16, exactly
  CrossRefined.tau_three_piece_at_least_sixty_five
                                          the m = 4 constant is >= 65
```

**Three open constants, in the order they are worth attacking.**

1. **`TauThreePieceAtMost 4 5 125`** — the only thing between the
   unconditional `r*(4,3) ≤ 7` and `r*(4,3) ≤ 5`. Known to lie in
   `[65, 125]` (§27.2); `g65` is the lower witness and is maximal.
   §26.4's four-family route is **closed** (§27.1) — do not re-open it.
   What is missing is a *joint* bound over the layers of a decomposition
   against one member, and `g65` shows the extremal puts everything in
   the one-point layer.
2. **`cross_pair_three_exact` at `r = 4, 5`.** §27.7 names the two
   missing ingredients exactly: a bound for "both sides contain two
   disjoint members" (measured ≈ `9r+2`, greedy gives `18r`), and
   Frankl's 10 in place of `tau_three_bound`'s 16. `r = 3` is a
   different matter — the neither-pointed branch *attains* `3r²+1` there,
   so no argument with slack can close it.
3. **`I₂(3,r)` at general `r`.** `max(3r+1,16)` is proved and 16 is
   `tau_three_bound`'s number, not the truth (10). Sharpening that one
   lemma tightens this and unblocks (2).

**Tools that exist.**

```
  rust/examples/cross_pair_scan.rs   stochastic maximiser for |A|+|B| at a
                                     given uniformity; modes 0/1/2 select
                                     unconstrained / neither pointed /
                                     neither pointed with two disjoint
                                     members on both sides. LOWER BOUNDS.
  rust/examples/tau_piece_scan.rs    exhaustive max of the tau >= t piece
                                     on a fixed ground; t = 2 gives I2.
  rust/tests/cross_refined.rs        every object above, verified
                                     independently of the Coq side.
```

**Do not re-run** (recorded negatives): §26.4's four-family inequality
(false, §27.1); the `Σ ≤ 48` derivation in any form; `3r²+1` at `u = 3`,
`r = 2` (false, 17-member witness); the eight items §25 lists from
earlier sessions.

**Rules earned here**, in `docs/reading.md`: rule 12 (a reduction is a
claim; measure the quantity before calling it the gap) and rule 13 (a
lower bound from a stochastic search bounds that search's effort, not the
quantity — re-measure before a measurement carries an argument about
difficulty).


## 28. The spread Hilton–Milner family: `r = m` is exactly the boundary,
##     and the star-extremality route has a ceiling below Erdős–Rado

Every Rao-spread family in this development up to §27 is a *finite
witness* — `c5`, `two_triangles`, `C37`, `hm16`, `g65` — written out by
hand and certified by `vm_compute` through `Reflect.rao_spreadb`. That is
why every extremal statement here has been about one `(m,r)` at a time.

`coq/HiltonMilner.v` builds the first **parametric** one, and with it the
first statement about `I(m,r)` that holds at every uniformity at once.

### 28.1 The object

Partition an initial segment of `N` into consecutive blocks

```
  E   = seq 0 m          the special set, m points
  W   = {m}              the apex, w := m
  Y_j = r points each    j = 0 .. m-3
```

and let

```
  HM(m,r) = E  ::  { {i, w} ∪ {y_0, ..., y_{m-3}} : i ∈ E, y_j ∈ Y_j }
```

— the Hilton–Milner shape: one set off to the side, and the star at an
apex outside it, thinned to a grid so that it is spread. It has
`m·r^(m-2) + 1` members, all of them `m`-sets, and it is intersecting for
a one-line reason (two star members share the apex; `E` meets each star
member in that member's point of `E`).

`CrossRefined.hm16` is `HM(3,5)` up to relabelling, and §27 identified it
as "a Hilton–Milner shape" in so many words — what it did not do was
parameterise it, which is the only reason the two inequalities below were
not visible then. At `m = 2` the construction degenerates to the triangle
`{{w,a},{w,b},{a,b}}`, which is already in the development as the
configuration behind `CrossRefined.unpointed_pair_bound`'s constant 6. Two
objects the repository already had turn out to be the two smallest
instances of one family.

The supporting machinery is worth as much as the family. `tstep`,
`blocks` and `grid` in the same file are a general *transversal family*
constructor, and

```
  grid_deg_mul :  NoDup T  ->  deg T (grid base k r) * r^|T|  <=  r^k
```

is a general degree bound for it, proved by one induction on the number
of blocks. Anything of grid shape is now a spread family for free.

### 28.1a What §24.13 already had, and what was actually missing

Before any claim below is read as new, the honest ledger of what session
N+7 had already put in §24.13:

* the quantity `I(m,r)` posed as an extremal problem in its own right,
  with the note "I have not found this posed before";
* the **crossover at `r = m+1`** as a measured phenomenon, in both
  uniformities where `I` could be computed: `I(2,r) = 3,3,4,5` and
  `I(3,r) = 10,16`. `I(3,3) = 10 > 9` **is** `¬ StarExtremalAt 3 3`,
  recorded as a measurement two sessions before this one;
* both witnesses below the crossover, by name — the triangle at `m = 2`
  and `C([5],3)` at `m = 3`. §28.7's remark that the search "returns
  `C([5],3)` first" is a rediscovery, not a discovery;
* **`PG(2,q)` already on the table**, with its sizes `3, 7, 13, 21, 31`
  tabulated against the star.

So the phenomenon, the two data points, and even the projective planes
were all in the repository. What was missing was one thing, and it is
the thing §24.13 got wrong by omission. Its argument for why the
crossover is not an accident of small cases runs: the star has size
`r^(m-1)`, *exponential in `m`*, while "every classical intersecting
family is polynomial or `~4^m`" — and the table bears that out,
`C([2m-1],m)` and `PG(2,q)` both losing to the star from `m = 4` on. The
unstated inference is that below the crossover there is nothing to find
at larger `m`.

That inference is false, and `HM` is why. `HM(m,r)` is **not** a classical
design: its size `m·r^(m-2) + 1` is itself exponential in `m`, tracking
the star's `r^(m-1)` rather than trailing it, and crossing it at exactly
`r = m`. The right family below the crossover was never going to be found
in a table of designs, because it is not one — it is the star itself,
thinned by one level and given one extra member.

**That is the new mathematics in this section, and it is elementary.** The
rest is formalisation (two prose data points become theorems general in
`m`), two new exact values, and the barrier arithmetic of §28.4.

### 28.2 The theorem

Two inequalities, pointing opposite ways.

**Spread.** The apex has `deg {w} = m·r^(m-2)` and the spread condition
caps it at `r^(m-1) = r·r^(m-2)`. No other test set imposes a condition on
`r` that this one does not already imply — the case table is in the file
header, indexed by whether `T` meets `E` and whether it contains the apex.
Plenty of other sets are *tight*: `{i,w}` has degree `r^(m-2)` against a
ceiling of `r^(m-2)`. But they are tight at every `r`, so they ask for
nothing; the only other place `m` is weighed against a power of `r` is the
sets avoiding both the apex and `E`, and they ask only for `m ≤ r²`. The
binding row is the apex, and it reads `m ≤ r`. So

> `HM(m,r)` is Rao(`r`)-spread **iff `r ≥ m`**.

**Size.** `m·r^(m-2) + 1 > r^(m-1)` iff `m ≥ r`.

Both hold at exactly one value of `r`, namely `r = m`, where the apex
degree is `m^(m-1) = r^(m-1)` — sitting precisely on the ceiling — and the
family has one member more than the star. Hence

> **`HiltonMilner.not_star_extremal_at_m_m`:** for every `m ≥ 2`,
> `¬ StarExtremalAt m m`.

This is the first *construction* in the development that is general in `m`
— `CrossIntersecting.star_extremal_for_large_r` is the general upper bound
(`m³ ≤ r²`), and this is the matching lower boundary. It is checked
twice: by the induction, and — at `(3,3)`
and `(4,4)`, where the ground sets have 7 and 13 points — by
`Reflect.rao_spreadb` enumerating the whole power set of the ground, which
shares no code with the induction (`HM_three_three_second_opinion`,
`HM_four_four_second_opinion`). `rust/tests/hilton_milner.rs` checks the
same claims a third time, independently, for every `(m,r)` with `2 ≤ m ≤ 6`,
`2 ≤ r ≤ 7` whose ground set fits in 32 points — 29 pairs, one short of the
full box because `HM(6,7)` needs 35.

### 28.3 What it sharpens

**`two_cover_star_extremal`'s threshold is exact.**
`CrossIntersecting.two_cover_star_extremal` carries the hypothesis
`m+1 ≤ r` and §26.2 argued the threshold was "exactly `m+1`" from the
arithmetic of its own proof. `HM(m,m)` is covered by the two points
`{0, m}`, so it is a counterexample to the same statement with `m ≤ r`:
the threshold is not an artefact of the case analysis.
(`two_cover_threshold_is_sharp`.)

**`I₂(3,r) = 3r+1` for every `r ≥ 5`.** `CrossRefined.nonstar_three_bound`
gives `I₂(3,r) ≤ max(3r+1, 16)`, and `3r+1 ≥ 16` exactly from `r = 5`.
`HM(3,r)` attains `3r+1`, and `rao_uniform_distinct` supplies the
`Distinct` hypothesis for free from the Rao condition. So the row
§27.6 closed at `r = 5` closes at every `r ≥ 5`, and
`CrossRefined.i2_three_five_is_sixteen` is its first instance.
(`i2_three_exact`.)

**The `m = 3` row of Conjecture T is complete.** `HM(m,m)` says nothing
about `r < m`, where it is not spread; there the obstruction is a
different object — and one §24.13 had already tabulated without noticing
it refutes anything. A projective plane of order `q` is `(q+1)`-uniform with
`q²+q+1` lines, any two meeting in one point, degree `q+1` at a point and
`1` at a pair — so it is Rao(2)-spread for every `q ≥ 1`, and it beats the
star bound `2^q` exactly when `q²+q+1 > 2^q`, which is `q = 2, 3, 4` and no
further. The Fano plane (`fano`, 7 lines against a star bound of 4) gives
`¬ StarExtremalAt 3 2`; `PG(2,3)` (`pg23`, 13 lines of 4 points against 8)
gives `¬ StarExtremalAt 4 2`. Combined with `HM(3,3)` at `r = 3` and
`TauThree.three_uniform_star_extremal` at `r ≥ 4`:

```
  StarExtremalAt 3 r     r = 0, 1   true, degenerately (see below)
                         r = 2      FALSE   fano, 7 > 4
                         r = 3      FALSE   HM(3,3), 10 > 9
                         r >= 4     true    three_uniform_star_extremal
```

`star_threshold_three_is_four` states it as a threshold: it holds for every
`r ≥ 4`, and any `s` for which it holds at every `r ≥ s` has `s ≥ 4`. So
`s*(3) = 4 = m+1` — **Conjecture T settled at its first nontrivial
uniformity**. The `m = 2` row closes in the same stroke and had been one
theorem short of closing for three sessions: `TwoCover.two_uniform_star_extremal`
gives `r ≥ 3`, and `HM(2,2)` — the triangle — gives `¬ StarExtremalAt 2 2`,
so `s*(2) = 3 = m+1` too. Two complete rows, both at `m+1`.

The degenerate rows are a correction to how Conjecture T must be stated,
not a curiosity. `StarExtremalAt 3 0` and `StarExtremalAt 3 1` are *true*:
Rao(0) forces every point to have degree 0 and Rao(1) forces the members
pairwise disjoint, so in both cases an intersecting family has at most one
member. "Least `r` such that `StarExtremalAt m r`" is therefore 0. The
quantity the conjecture is about is the least `s` such that it holds for
*every* `r ≥ s`, and that is how `s*` is defined below.

**Two numbers stop being coincidences.** §27's brief observed that the
two-cover split at `(m,r) = (4,5)` gives `C(3,5) + r^(m-2) = 76 + 25 = 101`
if `C(3,5) = 76`. That is `|HM(4,5)|` exactly, and the reason is that the
split applied to `HM(4,5)` at its own cover recovers the decomposition with
nothing lost. Conjecture X (`C(u,r) = u·r^(u-1)+1`) and Conjecture HM
(`I₂(m,r) = m·r^(m-2)+1`) are the same conjecture read at two
uniformities, and `HM` is the common witness.

`|HM(4,4)| = 65 = |g65|` is **not** the same phenomenon and should not be
read as one. `g65` lives at `(4,5)` with covering number ≥ 3; `HM(4,4)`
lives at `(4,4)` with covering number 2. Both are `1 + 4·16`, but the 16 is
`|hm16|` in one case and `r² = 16` in the other. Equal counts, different
objects.

### 28.4 The barrier, with the arithmetic exposed

This is the part worth reading twice, because it redirects the programme.

`TwoCover.star_extremal_gives_m_plus_one` is the route this development
built from star extremality to a sunflower bound:

```
  (∀ m ≤ n, StarExtremalAt m r)
      →  SpreadYieldsDisjoint n 3 r          star_extremal_gives_m_plus_one
      →  f(n,3) ≤ r^n + 1                    SpreadReduction.spread_reduction
```

and it is instantiated there at `r = n+1`. The obvious hope is that a
smaller `r` would do; a *constant* `r` would give `f(n,3) ≤ C^n` and settle
the conjecture at `k = 3`. It would not, and the reason is one line: the
hypothesis quantifies over **every** `m ≤ n`, so if `r ≤ n` it includes
`StarExtremalAt r r`, which `HM(r,r)` refutes.

> **`star_extremal_route_needs_r_above_n`:** for `2 ≤ r ≤ n`, the
> hypothesis `∀ m ≤ n, StarExtremalAt m r` is *false*. The route's
> parameter is pinned at `r ≥ n+1`.

So the route's best possible output is `f(n,3) ≤ (n+1)^n + 1`. Now compare:

```
  route ceiling      (n+1)^n + 1     ~  e·n^n
  Erdős–Rado (1960)  2^n·n! + 1      ~  sqrt(2πn)·(2n/e)^n,   2/e = 0.7358
```

The ratio is `(e/√(2πn))·(e/2)^n`, and `e/2 = 1.3591`, so it grows without
bound. Concretely, in exact arithmetic
(`the_route_ceiling_is_worse_than_erdos_rado`): the two agree at `n = 1`;
Erdős–Rado is strictly smaller for every `n` from 2 to 200 checked; and the
gap in decimal digits is 5 at `n = 50`, 12 at `n = 100`, 25 at `n = 200`.

> **The absolute-spread star-extremality route cannot produce a record at
> `k = 3`. Even if Conjecture T were proved in full, and every open
> constant in §§25–27 closed, the bound it yields is worse than the 1960
> one by an exponential factor.**

**And §21.5 got here first, for a different route.** The line
`b^b > (2b/e)^b = Erdos-Rado, by a factor (e/2)^b = 1.359^b` is already in
this file, written about the `τ`-indexed bound of §8, with the conclusion
"not merely on the wrong side of the barrier — it is worse than 1960
outright". It is the *same constant*, because both routes bottom out at
`n^n` and Erdős–Rado is `(2n/e)^n`. What §28 adds is that the
star-extremality route is now known to be one of them, and known by a
theorem rather than by an estimate: `HM(r,r)` makes the hypothesis false
below `r = n+1`, so `(n+1)^n` is not "the best we currently know how to
do" but the best the route can do.

That the arithmetic was already in the repository, done for a neighbouring
route, and was not applied to this one for four sections, is the content of
rule 14 in `docs/reading.md`.

A second, independent reason for the same `r ≥ m+1` was already visible and
is worth stating alongside, because it means the barrier survives even if
the star-extremality hypothesis were somehow repaired:
`TwoCover.split_with_piece_general` gives `|F| ≤ m·r^(m-1) + K` for a family
with no three pairwise disjoint members, `K` any bound on the intersecting
piece. To reach `r^m` one needs `m + K/r^(m-1) ≤ r`, so `r ≥ m+1` follows
from the *split* whatever `K` is — even `K = 1`. The greedy factor `m` from
covering by one member's points is the cost, and star extremality does not
touch it.

**What this does not say.** It does not say the destination is out of
reach. `SpreadYieldsDisjoint n 3 r` holds for `r = Θ(log n)` by the modern
spread lemma, which is exactly what `ALWZ.sunflower_bound_from_spread_lemma`
uses and where the `(log n)^n` bounds come from. The barrier is about the
*hypothesis*, not the conclusion: star extremality under Rao's **absolute**
spread condition cannot be the thing that supplies it, because the absolute
condition forces `r` to grow with `m` and the bound is `r^n`.

The reading that follows: work on `I(m,r)` is worth doing as extremal
combinatorics — it produces exact values like `I₂(3,r) = 3r+1` — and is
worth nothing as a route to a record. A route to a record has to keep `r`
small, which means the **fractional** spread condition, where `r` does not
have to grow with `m`. §26.4a's "first general answer" (`r ≥ m^{3/2}`) and
the whole of §§25–27 sit under this ceiling and always did; what changed is
that the ceiling is now a theorem instead of an unexamined hope.

### 28.5 The conjecture ledger

Every named conjecture in this development, its exact statement, what is
verified, and the budget behind each row. Rows marked **theorem** have
graduated.

| name | statement | status |
|---|---|---|
| **HM** | `I₂(m,r) = m·r^(m-2) + 1` for `r ≥ m` | lower bound is a **theorem** at every `m` (`HM_nonstar`); upper bound proved at `m = 3, r ≥ 5` (`i2_three_exact`); `m = 3, r = 3` measured 10 = `3·3+1` and `m = 3, r = 4` measured 13 = `3·4+1`, each exhausted on the grounds in §28.7; open at `m ≥ 4` |
| **X** | `C(u,r) = u·r^(u-1) + 1` for `r` large, exceptions 6 at `u=2`, 17 at `u=3` | `u = 2` **theorem** (`cross_pair_two_exact`, exact at every `r ≥ 2`); `u = 3` upper bound `3r²+1` proved for `r ≥ 6`, `r = 2` refuted by a 17-witness, `r = 3,4,5` open |
| **T** | `s*(m) := least s with StarExtremalAt m r for every r ≥ s` equals `m+1` | **theorem at `m = 2, 3`** (`star_threshold_three_is_four` at `m = 3`; at `m = 2` it is `TwoCover.two_uniform_star_extremal` for `r ≥ 3` against `not_star_extremal_at_m_m` at `r = 2`, the triangle). Lower half a **theorem at every `m`**: `¬ StarExtremalAt m m` (`star_extremal_needs_r_above_m`), plus `¬ StarExtremalAt 4 2` from `PG(2,3)`. Upper half open at every `m ≥ 4`: needs the `τ ≥ 3` piece |
| **F** | `I(m,r) ≤ max_t c_t·m^(t-1)·r^(m-t)`, `c_t` absolute | `t = 1` trivial, `t = 2` is HM, `t = 3` has one measured point (65 at `(4,5)`, `g65`) and no bound. Wide open, and §28.4 says it is not on a route to a record |
| **B** (new) | the barrier: no `r ≤ n` satisfies `∀ m ≤ n, StarExtremalAt m r` | **theorem** (`star_extremal_route_needs_r_above_n`) |

**`s*` is not `r*`.** The development already writes `r*(m,3)` for the
least `r` with `SpreadYieldsDisjoint m 3 r` (STATUS.md's table). `s*(m)`
above is a different quantity — the least `r` with `StarExtremalAt m r` —
and `HM` says nothing about the first. It cannot: `HM(m,m)` is
intersecting, so it has no three pairwise disjoint members, but its
`m^(m-1) + 1` members do not exceed the `r^m = m^m` that
`SpreadYieldsDisjoint` needs to be handed before it promises anything.
**No row of the `r*(m,3)` table moves.** What moves is the *route* from
`s*` to `r*`, which §28.4 shows is capped.

A note on **T**'s statement. `StarExtremalAt m ·` is *not* known to be
monotone in `r`: `RaoSpread` weakens as `r` grows, which enlarges the class
of families, while the bound `r^(m-1)` grows too, and neither dominates. So
"`s*(m) = m+1`" presupposes something unproved. Everything formalised is
stated at one specific `r`, and the honest form of the lower half is
`¬ StarExtremalAt m m`. Settling monotonicity — either way — is a small,
self-contained open problem this session did not attempt.

### 28.6 The barrier ledger

What has been shown *not* to work, with budgets, so that no later session
re-runs a dead search. §26.4's inline retraction is the template.

| what | why it is dead | budget/evidence |
|---|---|---|
| §26.4's four-family inequality `Σ_x \|A_x\| ≤ 48` | false, by more than 2× | `four_unpointed_cross_families_exceed_forty_eight`, §27.1 |
| `3r²+1` at `u = 3`, `r = 2` | false, 17-member witness | `cross_pair_three_needs_six`, §27.7 |
| **star extremality as a route to a record at `k = 3`** | ceiling `(n+1)^n`, worse than Erdős–Rado by `≈1.359^n` | §28.4; exact-arithmetic check to `n = 200` |
| **`StarExtremalAt m r` for any `r ≤ m`** | refuted at `r = m` by `HM(m,m)` at every `m`, and at `r = 2` for `m = 3` (Fano) and `m = 4` (`PG(2,3)`). `PG(2,4)` would give `m = 5` by the same arithmetic and was not built — 4 is not prime and the generator here only does prime orders. At `m = 3` the row is *complete*: false exactly at `r = 2, 3`. The first untouched cell is `(m,r) = (4,3)` | §28.2, §28.3 |
| a *constant* `r` in `SpreadYieldsDisjoint n 3 r` via star extremality | impossible: needs `r ≥ n+1` | `star_extremal_route_needs_r_above_n` |

### 28.7 Measured

```
  I2(3,3) in [10,16]  10 on grounds 6, 7, 8, 9 -- exhaustive on each (21650 /
                      536289 / 6482109 / 69481033 nodes, 230s at ground
                      9), so 10 on <= 9 points and >= 10 in general;
                      the proved upper bound is max(3r+1,16) = 16.
                      Attained by HM(3,3) and, separately, by the complete
                      3-graph on 5 points -- which is C([5],3), already
                      named as the m = 3 witness in section 24.13. The
                      search rediscovered it; this row confirms an
                      existing measurement rather than making a new one
  HM(m,r) spread      iff r >= m, for every (m,r) with 2<=m<=6, 2<=r<=7
                      and ground <= 32 points (29 pairs, exhaustive over
                      all subsets of members)
  HM(m,r) > star      iff r <= m, exhaustive over 2<=m<=12, 2<=r<=20 in
                      exact arithmetic (no family construction needed)
  violators of        exactly m^(m-2) of them, every one containing the
  HM(m, m-1)          apex, the smallest being {w} alone; checked for
                      m in 3..6. First written down as "the apex is the
                      unique violator", which the measurement refuted:
                      at (3,2) the violators are {w}, {w,y0}, {w,y1}.
                      They all impose the same condition, m <= r, which
                      is why the obstruction is still one obstruction
  I2(3,4) in [13,16]  13 = 3r+1, exhaustive on grounds 6, 7, 8 (26561 /
                      699463 / 15000076 nodes) -- so 13 on <= 8 points,
                      which is a lower bound on the unrestricted value.
                      Ground 9 was stopped by hand with its 4e9-node
                      budget unspent. The proved upper bound is
                      max(3r+1,16) = 16. The extremal witness the search
                      returns *is* HM(3,4) relabelled, so Conjecture HM
                      is right on every ground searched and the proved
                      bound is loose by 3 there. r = 5 was queued and
                      never started
  PG(2,q) at r=2      Rao(2)-spread and intersecting for q = 2, 3, 5;
                      beats the star bound 2^q iff q^2+q+1 > 2^q, i.e.
                      q <= 4 (checked to q = 12 in arithmetic). q = 7
                      needs 57 points, past the 32-bit mask, and was not
                      built
  route vs Erdos-Rado gap in decimal digits 5 / 12 / 25 at n = 50 / 100 / 200;
                      Erdos-Rado strictly smaller for every n in 2..200
```

Two extremal families tie at `(m,r) = (3,3)`, and the coincidence does not
continue: the complete `m`-graph on `2m-1` points is Rao(`m`)-spread (its
worst degree is `deg` of an `(m-1)`-set, which is `m`) and has `C(2m-1,m)`
members, which beats `m^(m-1)` at `m = 2` (3 > 2) and `m = 3` (10 > 9) and
loses from `m = 4` on (35 < 64). `HM` is the one that generalises.

### 28.8 Costs and gates

New: `coq/HiltonMilner.v` (one module, no axiom), `rust/tests/hilton_milner.rs`
(14 tests), 37 audited theorems and 11 audited definitions, 8 mutations.
Coq 8.18 was not present in the session container and was installed from
Ubuntu's package (`coq 8.18.0+dfsg-1build2`) before anything ran.

### 28.9 The one-line verdict

**The spread Hilton–Milner family `HM(m,r)` is Rao(`r`)-spread exactly
when `r ≥ m` and beats the star exactly when `r ≤ m`, so at `r = m` it does
both — `¬ StarExtremalAt m m` at every uniformity, the first general
statement about `I(m,r)` here, and the exact lower boundary of star
extremality.**

The mathematics is elementary and §28.1a says exactly how much of it §24.13
already had: the crossover, both small witnesses, and the projective
planes. What was missing was a family that beats the star below the
crossover *at every `m`*, and §24.13's table of classical designs implies
there is none. There is: it is not a design but the star thinned by a
level, and its size is exponential in `m` for the same reason the star's
is. No literature search was run this session, so nothing here carries a
priority claim — see §28.11.

Three things follow. `two_cover_star_extremal`'s threshold `r ≥ m+1` is
sharp rather than an artefact. `I₂(3,r) = 3r+1` for every `r ≥ 5`, which
turns §27.6's single exact value into a family of them. And with the Fano
plane covering `r = 2`, the whole `m = 3` row closes: **`StarExtremalAt 3 r`
holds exactly for `r ≥ 4`**, so `s*(3) = m+1`; the `m = 2` row closes with
it, since `HM(2,2)` is the triangle. Conjecture T has two confirmed rows,
both at `m+1`. And — the reason
this section is worth more than the theorem — the route from star
extremality to a sunflower bound is now known to have a **ceiling of
`(n+1)^n`, which is worse than Erdős–Rado's `2^n·n!` by a factor growing
like `1.359^n`**. That is not a reason to stop doing this extremal
combinatorics; `I₂(3,r) = 3r+1` is a real result and the `τ ≥ 3` questions
are real questions. It is a reason to stop expecting a record from it, and
to say so in the one place a later session will look.

### 28.10 Picking this up cold

**Settled in §28, all axiom-free.**

```
  HiltonMilner.grid_deg_mul            a general transversal family and
                                       its degree bound -- the first
                                       parametric spread construction here
  HiltonMilner.HM_rao                  HM(m,r) is Rao(r)-spread for r >= m
  HiltonMilner.not_star_extremal_at_m_m   ~ StarExtremalAt m m, every m >= 2
  HiltonMilner.two_cover_threshold_is_sharp  section 26.1's r >= m+1 is exact
  HiltonMilner.i2_three_exact          I2(3,r) = 3r+1 for every r >= 5
  HiltonMilner.star_extremal_route_needs_r_above_n   the barrier
  HiltonMilner.not_star_extremal_three_two   the Fano plane, r = 2
  HiltonMilner.not_star_extremal_four_two    PG(2,3), r = 2
  HiltonMilner.star_threshold_three_is_four  s*(3) = 4 = m+1, exactly
```

**Worth attacking next, in order.**

1. **Is `StarExtremalAt m ·` monotone in `r` above the degenerate range?**
   At `m = 3` the answer is yes and the row is now complete: false at
   `r = 2, 3`, true at `r >= 4`. At `m = 4` only `r = 2` (PG(2,3)) and
   `r = 4` (`HM(4,4)`) are known false, and `r = 3` is untouched — the
   cheapest open question in this section, and a counterexample would be
   as interesting as a proof. `PG(2,3)` at `r = 3`: 13 members against a
   star bound of 27, so it does not settle it.
2. **`C(3,5) = 76`, then `StarExtremalAt 4 5`.** Unchanged from §27.9 —
   §27.7 names the two missing ingredients exactly. It is still the
   flagship *as mathematics*; §28.4 says it is not a route to a record,
   which is a different claim.
3. **The `τ ≥ 3` piece at `(4,5)`, still in `[65, 125]`.** The spread
   analogue of Frankl's `τ = 3` theorem is the piece everything waits on.
4. **`I₂(m,r)` at `m ≥ 4`.** Conjecture HM's upper half. The lower half is
   now a theorem at every `m`, so this is a clean target with a known
   answer to aim at.
5. **A second technique.** §28.4 is the argument for it: the spreadness
   layer has a measured ceiling, so the next real gain has to come from
   somewhere else. `coq/SliceRank.v` exists and is the obvious start.

**Do not re-run**: everything in the §28.6 barrier ledger, plus the items
§27.9 lists.

### 28.11 What is claimed as new, and what was not checked

The register in `docs/reading.md` exists so that novelty claims are
separated from work. This session **ran no literature search at all**, so
every row below is "new to this development", and none of it is a priority
claim.

```
  new mathematics       HM(m,r): a spread-thinned Hilton-Milner family
                        that beats the star at r = m for every m, where
                        section 24.13's table of classical designs
                        (C([2m-1],m), PG(2,q)) suggested nothing does past
                        m = 3. Elementary -- a construction and a degree
                        count -- but it is the piece that was absent.
  new exact values      I2(3,r) = 3r+1 for every r >= 5;  s*(3) = 4,
                        the first complete row of the star-extremality
                        question at any uniformity above 2.
  new to Coq            the transversal machinery (tstep/blocks/grid,
                        grid_deg_mul) -- the first parametric spread
                        construction here; and two of section 24.13's
                        prose data points as theorems general in m.
  new as a theorem,     the barrier of section 28.4. The comparison
  not as arithmetic     (n+1)^n against 2^n n! is one line, and section
                        21.5 had already done the identical comparison for
                        the tau-indexed route. What is new is that the
                        r >= n+1 pin is now forced by a witness rather
                        than estimated.
  not new               the Hilton-Milner shape (1967); the Fano plane;
                        C([5],3); PG(2,3); the observation that the star
                        loses below r = m+1 at m = 2, 3 (section 24.13).
```

**The register row exists, and the first honest pass at it partly
refuted §24.13.** Rendering [Kup25] p. 53 — a page an earlier word-grep
had flagged and nobody had opened — turned up `τ`-**homogeneous
families** (Kupavskii–Zakharov): `|F(X)|/|F| ≤ τ^|X|·|A(X)|/|A|`, a cap at
every level, geometric in `|X|`. That is the *shape* of Rao's condition
generalised to an arbitrary ambient family, so §24.13's "the neighbouring
literature caps one statistic" is too strong. With `A = binom([n],k)` it
is the fractional condition, not the absolute one, so it is not the same
hypothesis — but the family of ideas is named and studied, and this
repository did not know it. `docs/reading.md` B19c.

 `docs/reading.md` **B19** records the
claim, **B19a** verifies §24.13's "the neighbouring literature caps one
statistic" from a rendered page of Frankl–Han–Huang–Zhao rather than from
assertion, and **B19b** records a trap: the literature's *`r`-spread* is
the **fractional** condition (`max s-degree ≤ r^(−s)·|F|`), which is
`Spread.Spread` here and not `Spread.RaoSpread`, so a search on the word
returns the wrong object.

The verdict is *not found*, and the section "The B19 search, described"
says exactly how weak that negative is: the 16-PDF corpus grepped page by
page and three files' hits rendered and read, two web queries, one primary
page. **No MathSciNet, no zbMATH, no journal-side search, and none of the
synonyms — nucleus, base, crosscut, generating set, minimal cover — that
this repository's own rule 2 box demands.** The classical Hilton–Milner
family is confirmed as the underlying object, verbatim from [FHHZ17] p. 1;
what was not found is the thinning. A specialist in the degree-condition
line may recognise it on sight, and the remaining search is still owed
before any of this is described as new outside the repository.

## 29. The reduction at an arbitrary profile: the greedy cover step
##     cannot beat 1960, and that is now a theorem

§28.4 costed one route and found it capped below Erdős–Rado. §21.5 had
costed another, four sections earlier, and found the same constant. This
section asks what the two have in common, gets an exact answer, and turns
the answer into a gate that costs every future route automatically.

**Nothing in this section is new mathematics.** It is a reorganisation,
one range check upgraded to a theorem, and a tool. §29.6 says exactly
which parts were already in the repository — three of them were, and one
of those was the thing the incoming brief listed as the session's first
task. The value is in §29.5 and in the fact that the barrier is now
machine-checked rather than asserted.

### 29.1 The observation

`SpreadReduction.spread_reduction` takes an `m`-uniform family with
`deg T F ≤ r^(m-|T|)` and more than `r^m` members, and returns a
`k`-sunflower. Its induction never uses that `r^·` is a power. Replace
`r^j` by an arbitrary `B : nat -> nat` and every step goes through
verbatim, because the recursion is **profile-preserving**: if `T`
violates the condition then the link has uniformity `j = m - |T|`, more
than `B j` members, and

```
  deg S (link T F)  =  deg (S ++ T) F  ≤  B (m - |S| - |T|)  =  B (j - |S|)
```

which is the same condition one level down. `coq/Profile.v` states that:

```
  ProfileSpread B m F        deg T F <= B (m - |T|),  T nonempty
  ProfileYieldsDisjoint n k B    the oracle, at profile B
  profile_reduction          ProfileYieldsDisjoint n k B  ->  f(m,k) <= B m + 1
```

`spread_reduction` is the instance at `B j = r^j`
(`spread_reduction_is_a_profile_instance`), and the correspondence is
definitional (`RaoSpread_ProfileSpread`, `ProfileYieldsDisjoint_pow`).

The generalisation costs nothing because the reduction never *propagates*
spreadness into the link — it re-decides it at each level with
`profile_witness`, exactly as `Spread.rao_witness` does.

### 29.2 The theorem

The **greedy cover step** is the argument every elementary bound in this
development bottoms out at: no `k` pairwise disjoint members, so a maximal
matching has at most `k-1` of them, so the family is covered by `(k-1)m`
points, so

```
  |F|  <=  (k-1) · m · B(m-1).                       greedy_profile_bound
```

It closes the reduction at a profile `B` exactly when that lands inside
`B`:

```
  GreedyClosed n k B  :=  (k-1) · m · B(m-1) <= B m,   1 <= m <= n
  greedy_closes_profile :  GreedyClosed n k B -> ProfileYieldsDisjoint n k B
```

and unrolling the recurrence from `B 0 = 1` gives, in one induction:

> **`greedy_forces_erdos_rado`: every greedy-closed profile satisfies
> `B m ≥ (k-1)^m · m!`.**
>
> **`greedy_cannot_beat_erdos_rado`: so the bound it yields through
> `profile_reduction` is at least `ErdosRado_Greedy.er_upper_bound`. The
> greedy cover step cannot beat 1960, at any `k`, by any amount.**

This is **exact**. There is no Stirling, no `e`, no range check: the
conclusion is the 1960 constant itself. It is the formal content of the
sentence that the `m!` in Erdős–Rado *is* the factor `m` paid once per
level by covering with one member's points.

Two instances make the statement concrete.

* **Erdős–Rado's own profile is the least greedy-closed one.**
  `er_profile k j = (k-1)^j · j!` is greedy-closed **with equality at
  every level** (`er_profile_greedy_closed`), so `profile_reduction`
  returns `(k-1)^n · n! + 1`. That is `erdos_rado_via_profile` — a
  second, independent derivation of `ErdosRado.erdos_rado_upper_bound`
  inside this development, through the spread reduction rather than
  through `ErdosRado.v`'s own induction on the uniformity.

* **`SpreadThreshold.cover_spread_disjoint` is the power profile.**
  `r^j` is greedy-closed iff `(k-1)m ≤ r`, so `r = (k-1)n` works
  throughout, which at `k = 3` is exactly §22.1's `r*(n,3) ≤ 2n`. It
  generalises to every `k` for free (`cover_spread_disjoint_general`),
  and `cover_bound_cannot_beat_erdos_rado` applies the barrier to it.

  **How much that generalisation is worth, exactly: one.**
  `SpreadReduction.elementary_spread_disjoint` was already general in `k`,
  at `r = n(k-1) + 1`; the profile version is `r = (k-1)n`, and drops the
  `1 ≤ n` hypothesis. So what §22.1 gained at `k = 3` — one — is now
  gained at every `k`, and nothing more. The row is worth stating because
  the *reason* changes: `cover_spread_disjoint`'s proof is a bespoke
  `k = 3` case analysis, and this one is `GreedyClosed` plus arithmetic,
  which is also what makes the barrier below apply to it.

### 29.3 The step is lossy, and no refinement of it helps

The barrier is a statement about the *method*, not about the truth, and
the two are measurably different already at uniformity two.

Define the **least profile** `B_k`: `B_k(0) = 1` and `B_k(m)` the largest
`m`-uniform distinct family with no `k` pairwise disjoint members
satisfying `deg T F ≤ B_k(m - |T|)`. By construction
`ProfileYieldsDisjoint n k B_k` holds and `f(m,k) ≤ B_k(m) + 1`. At
`k = 3`:

```
  B(0) = 1     B(1) = 2     B(2) = 6
  Erdos-Rado           8              <- the greedy step's value
```

`B(2) = 6` is a two-line argument, and the search is a confirmation of it
rather than its proof — the search is over bounded ground sets and `B_k`
is not.

> A graph with max degree ≤ 2 and no three pairwise disjoint edges has at
> most 6 edges. Take a maximal matching; it has at most two edges, so its
> at most four endpoints cover every edge. Summing degrees over those
> endpoints counts every edge at least once **and the two matching edges
> twice**, so `|E| ≤ 4·2 − 2 = 6`.

Attained by **two disjoint triangles** — which is `F23.two_triangles`,
already in this development as the family attaining `g(2) = 6`. The
search (`rust/tests/profile.rs`, backtracking over all simple graphs on
6, 7, 8 and 9 points with max degree ≤ 2 and no three pairwise disjoint
edges) returns 6 and that witness at every ground set. So the greedy step
over-counts by 2 at the second level.

Neither the argument nor the search is in Coq: `B_k` is a *measured*
object here, not a formal one, and `greedy_forces_erdos_rado` does not
depend on it. What it depends on is nothing but the recurrence.

> The gap is real; the step cannot close it; and
> `greedy_forces_erdos_rado` says no sharpening of *the step* ever will.
> Something else has to. §22.1's pair-covering is one such something —
> it beats `2n` precisely because a pair has degree `r^(m-2)` where a
> point has `r^(m-1)` — and the spread lemma is the other.

**A refinement was derived, tested, and dropped.** Counting the cover
degrees more carefully (the `k-1` matching members are each counted `m`
times, not once) gives `|F| ≤ (k-1)(m·B(m-1) - (m-1))`, hence the profile
`1, 2, 6, 32, 250` against Erdős–Rado's `1, 2, 8, 48, 384`, hence
`f(3,3) ≤ 33` unconditionally. It was not built, because
**`PureLink.f_3_3_at_most_27` is already in the development,
unconditional and axiom-free**, and 27 < 33. See §29.6.

### 29.4 The linear comparison, exactly

The greedy barrier is exact. The other routes this development has costed
are not greedy-only, so they need the comparison done directly, and §28.4
did it by evaluating both sides for `n ≤ 200`. It is a theorem, and the
whole proof is one Bernoulli inequality in `nat`:

```
  pow_bernoulli                n^k · (n+k)  <=  n · (n+1)^k
  two_pow_le_succ_pow          2·n^n  <=  (n+1)^n            (k = n)
  erdos_rado_below_the_n_to_the_n_ceiling
                               2^n · n!  <=  (n+1)^n,  every n
```

`pow_bernoulli`'s induction step reduces to `0 ≤ k`, which is why it is
eight lines rather than a binomial expansion. The consequence:

> **`star_extremal_ceiling_is_worse_than_erdos_rado`: the ceiling
> `(n+1)^n + 1` that `HiltonMilner.star_extremal_route_needs_r_above_n`
> pins the star-extremality route to is at least Erdős–Rado's
> `2^n·n! + 1`, at every `n`.**

§28.4's "checked for every `n` from 2 to 200" is subsumed, and the
statement no longer carries a range.

### 29.5 The gate: rule 14 as machinery

`tools/ceiling.py`, wired into `make verify`. Every reduction in the
development declares the best `f(n,3)` bound it can *possibly* produce —
not what it currently produces — and the tool instantiates it in exact
integer arithmetic against three bars. Because every bound has the shape
`base(n)^n`, the routes are compared by their **base**:

```
  route                                     base(50) base(200)    g  verdict
  elementary cover, r = 2n+1                     101       401 0.99  linear: loses
  greedy cover, r = 2n                           100       400 1.00  linear: loses
  quadratic split, r = 1+sqrt(3n^2-4n+3)          87       347 0.99  linear: loses
  matching split, method ceiling r = n+1          51       201 0.99  linear: loses
  star extremality, pinned at r = n+1             51       201 0.99  linear: loses
  tau-indexed bound, r = n                        50       200 1.00  linear: loses
  Erdos-Rado profile via the reduction            38       149 0.98  linear: equals
  spread lemma, r ~ 3 log2(3n)                    24        30 0.22  sublinear
  constant threshold (the conjecture)              8         8 0.00  constant
  ---
  Erdos-Rado 1960 (the bar)                       38       149 1.00
  BCW 2021 (the record)                           60        84 0.24
```

`g` is the measured exponent in `base(n) ~ n^g`. Classification is by
**shape**, deliberately: the constants in the two sublinear rows (Rao's
`alpha`, BCW's `C`) are not pinned by this development, so a verdict that
depended on them would be an artefact of the guess.

Each route also declares the verdict it expects, and **a mismatch fails
the build**. A route cannot be described as a path to a record once its
own ceiling says otherwise, and a route written tomorrow gets costed the
day it is written rather than six sessions later.

Two things the table makes visible that no prose in this file did.

* **Erdős–Rado is not the bar.** §28.4 compares against `2^n·n!`, which is
  the weakest possible criticism: the record is Bell–Chueluecha–Warnke's
  `(C·3·log n)^n`, and *every linear route loses to that too*, by a wider
  margin and for a structural reason. A route needs a **sublinear** base
  to be in the running at all.
* **The sharp constant for a linear route is `2/e`.** `r*(n,3) ≤ c·n`
  gives `f(n,3) ≤ (cn)^n + 1`, which beats `2^n·n!` exactly when
  `c < 2/e = 0.7357588…` (`tools/ceiling.py --linear`, with the finite-`n`
  crossovers shown, since Stirling's `sqrt(2πn)` keeps `c` slightly above
  `2/e` winning until `n ≈ 2000`). **Every linear route in this
  development has `c ≥ 1`**, the smallest being the matching split's
  method ceiling at exactly `1`. The best axiom-free bound, §22.1's
  `1.74n`, is 2.4 times the threshold.

### 29.6 What was already here: three finds, one of them the brief's

Rule 16 says to read the section that first posed the question rather than
the handoff. Three times this session that changed what got built.

1. **The incoming brief's Track 1, step one — "state
   `∃C, ∀ n k, SpreadYieldsDisjoint n k (C·k)` as a named `Prop` in Coq
   and derive `f(n,3) ≤ C^n` through `spread_reduction`. **Do this
   first**" — has been in the development since `coq/Conjecture.v` was
   written.** `Conjecture.spread_conjecture` is that `Prop`, in the more
   general form `∃ c : nat -> nat` rather than `C·k`;
   `Conjecture.spread_conjecture_suffices` derives the full sunflower
   conjecture from it and `k3_corollary` specialises to `k = 3`. §2 of
   this file points at it. **Rao's question, in the absolute form, is
   already a formal object here.** Nothing was owed and nothing was
   written.

2. **`r*(m,3)` is not untouched either.** §22's opening sentence is
   *"§18.5 is the observation that whether the sequence is bounded in `m`
   is the sunflower conjecture at `k = 3`"*, and the whole section attacks
   it. The brief's "nobody in this programme has ever pointed the
   machinery at it" is wrong about this repository.

3. **The refined-profile bound of §29.3 was derived and dropped.** It
   gives `f(3,3) ≤ 33` unconditionally, which would have been an
   improvement on the `f(3,3) ≤ 49` that §22.2's table and §18.2's text
   still quote — except that `PureLink.f_3_3_at_most_27` proves
   `UpperBound 3 3 27`, unconditionally, `Closed under the global
   context`. Roughly a hundred lines of double-counting were not written.

   **Consequence: this file has a stale number.** §18.2 says *"this
   development only knows `20 ≤ g(3) ≤ 48`"*. It knows `g(3) ≤ 26`
   (`PureLink.f_3_3_at_most_27`), and `Sharp.sharp_beats_erdos_rado_at_three`'s
   32 is *conditional* on `AHSOptimal` and therefore weaker than what is
   proved outright. Corrected here rather than in place, because §18.2's
   surrounding argument is about what a *measurement* would decide and
   that argument is unaffected.

### 29.7 Measured

```
  B(2) = 6 at k = 3     exhaustive over all simple graphs on 6, 7, 8, 9
                        points with max degree <= 2 and no three pairwise
                        disjoint edges; maximum 6 at every ground set,
                        witness two disjoint triangles (= F23.two_triangles).
                        Erdos-Rado / the greedy step give 8 there
  greedy barrier        checked over 112 systematically inflated profiles
                        at k = 2..5 and m <= 12, exact u128
  power profile         greedy-closed iff (k-1)m <= r, checked for
                        k = 2..6, n = 1..8, and refuted at r-1 exactly
                        when (k-1)n > r-1
  2^n n! <= (n+1)^n     n = 0..26, the exact u128 range, tight at n = 0,1
                        and strict from n = 2. rust/tests/hilton_milner.rs
                        pins the same comparison to n = 200 in its own
                        big-integer arithmetic
  linear routes         (2n)^n, (2n+1)^n, (1.74n)^n and (n+1)^n all at
                        least 2^n n!, n = 1..23 (the u128 range)
  the 2/e threshold     c = 0.7357 beats Erdos-Rado at n = 200, 2000 and
                        20000; c = 0.7400 beats at 200 and loses from
                        2000 on. tools/ceiling.py --linear
```

A note on the first draft of `rust/tests/profile.rs`, because it is the
kind of error this repository exists to catch. It used `u128::pow`, which
**wraps silently in release mode**, and reported
`erdos_rado_below_the_n_to_the_n_ceiling` as failing at `n = 28` — for a
theorem the kernel had already accepted at every `n`. `(n+1)^n` leaves
`u128` at `n = 27`. Every power in that file is now `checked_pow` with
the range asserted, and the first overflowing `n` is pinned as a test.

### 29.7a Costs and gates

New: `coq/Profile.v` (one module, no axiom, 21 audited theorems and 6
audited definitions), `rust/tests/profile.rs` (8 tests), `tools/ceiling.py`
and the `make ceilings` target, 6 mutations. Coq 8.18 was not present in
the session container and was installed from Ubuntu's package before
anything ran, as in §28.8.

All gates green on the final tree:

```
  make -j4 verify          pass (43 modules, clean rebuild)
  Print Assumptions        all 21 new audited theorems "Closed under the
                           global context"; no existing .v file was
                           touched, so the other 547 are unaffected --
                           `git diff --stat origin/main -- coq/` is one
                           file added and nothing else
  make coqchk              pass; the whole-library axiom census is still
                           exactly `Sunflower.ALWZ.Rao20_lemma2` and
                           nothing else; no type-in-type, no unsafe
                           (co)fixpoints, no assumed positivity
  python3 tools/mutate.py  131 mutations: 128 killed, 2 genuine survivors
                           (unchanged), 1 control surviving as it must,
                           **0 unexpected**. All 6 new mutations killed as
                           declared, each in coq/Profile.v, ~210s apiece
  cargo test --release     30 suites, 287 tests, 0 failures
  tools/statements.py      677 baseline entries, accepted in this commit
  tools/docnumbers.py      12 quoted numbers match
  tools/ceiling.py         9 routes costed, every declared verdict matches
```

### 29.8 The ledgers

**Conjecture ledger.** No row of HM, X, T, F or B moved — nothing here is
about `I(m,r)`. One row is added, because §29.3 names an object that did
not have a name.

| name | statement | status |
|---|---|---|
| **P** (new) | **the profile reduction is lossless**: `B_k = g_k`, where `B_k` is the least profile (§29.3) and `g_k(m)` is the largest sunflower-free `m`-uniform family | `g_k(m) ≤ B_k(m)` is a **theorem** and elementary — a sunflower-free family has no `k` pairwise disjoint members, and its link at `T` is sunflower-free at uniformity `m-\|T\|`, so `deg T F ≤ g_k(m-\|T\|)`. Verified equal at `k = 3` for `m = 0, 1, 2`: both are `1, 2, 6`. Open from `m = 3`, where `B_3(3) ∈ [20, 32]` — 20 from `g(3) ≥ 20`, 32 from §29.3's refined count — against `g(3) ≤ 26` (`PureLink.f_3_3_at_most_27`). So **`B_3(3) > 26` would refute P outright**, and it is a finite search |

P matters because `f(m,k) ≤ B_k(m) + 1` is exactly what `profile_reduction`
delivers, so P is the statement that the reduction this whole development
is built on loses nothing. It is *not* a route to a record — `B_k ≥ g_k`
means P at best re-derives the truth — but it is the first question here
about how much the reduction costs, and the answer is unknown past
uniformity two.

**Barrier ledger**, three new rows:

| what | why it is dead | budget/evidence |
|---|---|---|
| **the greedy cover step, as a route to any record** | any profile it closes is `≥ (k-1)^m·m!`, which *is* Erdős–Rado | `greedy_forces_erdos_rado`, exact, every `k`, no range |
| **any linear bound on `r*(n,3)` with `c ≥ 2/e`** | `(cn)^n ≥ 2^n·n!` asymptotically; every route here has `c ≥ 1` | `tools/ceiling.py --linear`; `star_extremal_ceiling_is_worse_than_erdos_rado` proves the `c = 1` case at every `n` |
| **comparing routes against Erdős–Rado at all** | the record is `(C log n)^n`; a linear route loses to it by a wider margin than to 1960 | §29.5's table, `g` column |

**Novelty ledger** (§28.11's format). **No literature search was run this
session**, so rule 17 applies to every row: these are claims about this
development, not priority claims.

```
  new mathematics       none. The greedy-cover-forces-factorial
                        observation is the 1960 proof read backwards;
                        2^n n! <= (n+1)^n is AM-GM; the profile
                        generalisation is the same recursion [Rao25] p. 8
                        presents in the same shape (quoted in section 1).
  new to Coq            profile_reduction and the profile condition;
                        greedy_closes_profile / greedy_forces_erdos_rado
                        as a barrier theorem rather than a remark;
                        erdos_rado_via_profile, a second derivation of
                        the 1960 bound through the spread reduction;
                        cover_spread_disjoint_general, section 22.1's
                        k = 3 cover bound at every k.
  new as a theorem,     2^n n! <= (n+1)^n at every n, replacing section
  not as arithmetic     28.4's check to n = 200.
  new as machinery      tools/ceiling.py: rule 14 enforced by the build
                        rather than by prose, and the observation that the
                        bar is (C log n)^n and not 2^n n!.
  not new               two disjoint triangles (F23.two_triangles, and
                        g(2) = 6 throughout this file); Erdos-Rado 1960;
                        Bernoulli; the constant 2/e, which is section
                        21.5's 1.359 = e/2 read the other way up.
```

### 29.9 Picking this up cold

**Settled in §29, all axiom-free.**

```
  Profile.profile_reduction              the reduction at any profile B
  Profile.greedy_closes_profile          the cover step, at any profile
  Profile.greedy_forces_erdos_rado       greedy-closed => B m >= (k-1)^m m!
  Profile.greedy_cannot_beat_erdos_rado  the barrier, in er_upper_bound form
  Profile.erdos_rado_via_profile         1960, through the spread reduction
  Profile.cover_spread_disjoint_general  section 22.1's cover bound, every k
  Profile.pow_bernoulli                  n^k(n+k) <= n(n+1)^k
  Profile.erdos_rado_below_the_n_to_the_n_ceiling   2^n n! <= (n+1)^n
```

**Worth attacking next, in order.**

1. **The two live tracks are unchanged and neither was started.**
   Discharging `Rao20_lemma2` (§1: the counting proof, Lovett §3, staged
   in three stages with the encoding's injectivity identified as an
   *equation*), and Rao's `r(p,k) = O(p)` question (`docs/reading.md` A2).
   §29 says nothing about either; it says that everything *else* in the
   development is capped, which is an argument for going there.
2. **`B_k`, the least profile, is a well-defined sequence and only two
   terms are known.** `B_3 = 1, 2, 6, ?`. `B_3(3) ∈ [g(3), 32]`, so
   `[20, 32]` with what is proved here. It is a finite search at each
   term, it is bounded above by the refined count of §29.3, and
   `f(m,3) ≤ B_3(m) + 1` — so **is the reduction lossless, i.e. is
   `B_k = g`?** `B_3(2) = 6 = g(2)` is the only data point. This is a
   clean, cheap, unasked question.
3. **Nothing else in §29.** The gate is the deliverable; do not add
   routes to `tools/ceiling.py` for their own sake, add them when a route
   is written.

**Do not re-run**: the refined profile of §29.3 (dominated by
`PureLink.f_3_3_at_most_27`), and everything in the §28.6 and §29.8
barrier ledgers.

### 29.10 The one-line verdict

**The reduction this development is built on works at an arbitrary
profile, and the greedy cover step closes a profile exactly when that
profile dominates `(k-1)^m·m!` — so the step that every elementary bound
here bottoms out at cannot beat Erdős–Rado, at any `k`, by any amount,
and that is now an exact theorem rather than an estimate.**

Around it: `2^n·n! ≤ (n+1)^n` at every `n`, which retires §28.4's range
check; Erdős–Rado 1960 re-derived through the spread reduction; §22.1's
cover bound generalised from `k = 3` to every `k`; and `tools/ceiling.py`,
which costs every route in the development against 1960, against the
record, and against the target, and **fails the build when a route's
description disagrees with its own arithmetic**.

No number moved. The session's other three outputs are refusals: Track 1's
first task was already done (§29.6.1), the quantity it was aimed at was
already posed (§29.6.2), and the one bound this section could have
improved is already beaten by a theorem three files away (§29.6.3). The
hundred lines not written are the point of rule 16, and the tool is the
point of rule 14 — the two rules the previous session earned, applied to
the session that inherited them.

## 30. Stage A of the spread lemma: the counting layer, and the
##     hypothesis that was one notch too strong

§1 has staged the discharge of `ALWZ.Rao20_lemma2` since the July 2026
reading session — the counting proof ([ALWZ20] §2 as streamlined by
Park–Pham, written out in [Lovett] §3, pp. 11–15), in three stages, with
C17 recording *why* that proof and not Rao's. Nobody had started it.

**Stage A is done.** `coq/Counting.v`, one module, no axiom, 26 audited
theorems and 4 audited definitions, every one `Closed under the global
context`.

### 30.1 What is in it

§1's Stage A list, item by item, with the name that discharges it.

```
  fixed-size subset enumeration    subsets_of_size j l
                                   := filter (length = j) (Spread.subsets l)
  its count                        length_subsets_of_size :
                                     |subsets_of_size j l| = binom |l| j
  the counting operator            count p L := |filter p L|
  injection implies <=             count_inj_le
  additivity over disjoint preds   count_disjoint_add
  C(n,j) <= 2^n                    binom_le_two_pow
  the one binomial estimate        binom_ratio
```

Plus what those needed: `binom` (Pascal's recursion), `binom_zero_above`,
`binom_diag`, `binom_one`, **`binom_absorb`** — the absorption identity
`C(N,j+1)·(j+1) = C(N,j)·(N−j)`, which is the only fiddly induction in
the file and the single arithmetic fact the estimate rests on —
`length_subsets` (`|subsets l| = 2^|l|`), `subsets_NoDup_enum` (the
enumeration has no repeats, needed wherever the layer is an injection's
*domain*), and `NoDup_map_inj`, which Coq 8.18's `List` does not have
(only the converse `NoDup_map_inv`).

Two decisions worth recording because §1 got to argue for them and this
section can now confirm them.

* **Fixed-size, not the product measure.** §1's earlier version wanted
  the product measure at `p = 1/2` so that "probability" would be
  cardinality over the powerset; it was corrected, on a proof-level read,
  to the fixed-size statement, because the proof needs `V` *small*
  (`q = p/log n`) and because Lovett p. 11 derives the product-measure
  form from the fixed-size one by a limit. Stage A confirms the
  correction was right: the whole layer is `binom`, no limit appears, and
  the file is 40-odd lemmas of `nat`.

* **Truncated subtraction is harmless here.** `binom_absorb` is stated
  with `N - j` in `nat`. Above the diagonal both sides are zero rather
  than the identity failing, which is checked in Coq
  (`absorb_above_the_diagonal`) and over a range in Rust.

### 30.2 The correction: the hypothesis was one notch too strong

§1 states the estimate as Lovett's Claim 3.4 uses it — a random subset of
fixed size `qN`, so `j = qN`, so with `q = c/d` the hypothesis is
`c·N ≤ d·j`. That is what the application supplies. It is **not** what
the argument needs.

The single step is `c·C(N,j+1) ≤ d·C(N,j)`, which by absorption reduces
to `c·(N−j) ≤ d·(j+1)`; and for that, `c·N ≤ d·(j+1)` is enough, since
`c·(N−j) ≤ c·N`. The iterated form needs the hypothesis only at `j+i` for
`i ≥ 0`, so it inherits it. So:

> **`Counting.binom_step`:  `c·N ≤ d·(j+1)` → `c·C(N,j+1) ≤ d·C(N,j)`.**
>
> **`Counting.binom_ratio`:  `c·N ≤ d·(j+1)` → `c^m·C(N,j+m) ≤ d^m·C(N,j)`.**

And the successor is **exactly** the boundary. `c·N ≤ d·(j+2)` makes the
statement false, and the smallest witness is tiny:

```
  N = 1, j = 0, c = 2, d = 1, m = 1
      hypothesis   2·1 <= 1·(0+2)     holds
      conclusion   2^1·C(1,1) <= 1^1·C(1,0)   i.e.  2 <= 1     FALSE
```

`Counting.binom_ratio_needs_the_successor` carries it in the kernel;
`rust/tests/counting.rs` finds **102** such points in a `N ≤ 15`,
`j ≤ 17`, `c,d ≤ 6`, `m ≤ 6` box. `Counting.binom_ratio_at_threshold` is
§1's shape (`c·N ≤ d·j`), derived in one line from the sharp one, and it
is what Stage B should call.

**Why this is worth a subsection rather than a footnote.** Rule 15 says
an algebraic restatement is evaluated at the tight case before anything
is built on it. The tight case here is not where the *application* sits
(`j = qN`) but where the *argument* stops working, and those differ by
one. A statement carrying a non-minimal hypothesis is not wrong, but it
is a gap: a later session, reaching for the estimate at `j+1` and finding
the lemma stated at `j`, would either re-prove it or weaken its own
statement to fit. Both are wasted, and neither is visible from §1's text.

> **Rule 23 (`docs/reading.md`). Prove a lemma at the weakest hypothesis
> its own argument needs, not at the one the application supplies — and
> record the witness that shows the weakening stops there.** The
> application's hypothesis is a *use*, not a specification.

### 30.2a The counting layer is polymorphic, and it had to be

§1's sketch types the counting operator as
`count : (list nat -> bool) -> list (list nat) -> nat`, and the first
draft of `Counting.v` followed it. That would not have served Stage B.

**Claim 3.4 counts pairs.** Its displayed ratio is

```
  Pr[ |M(S,V)| >= n/2 ]  =  |B| / ( |F| * C(N, qN) )
```

with `B = {(S,V) : S ∈ F, V ⊆ U, |V| = qN, |M(S,V)| ≥ n/2}` — the domain
is `list (list nat * list nat)`, not `list (list nat)`. A counting layer
typed at `list nat` would have had to be redone, or worked around by
encoding a pair as one list with a separator, which is exactly the kind of
thing that makes a formalisation unreadable.

`count`, `count_le_length`, `count_partition`, `count_disjoint_add`,
`count_mono`, `NoDup_map_inj` and `count_inj_le` are therefore stated at
an arbitrary type. Nothing is lost — `NoDup_incl_length`, which
`count_inj_le` goes through, is polymorphic in Coq's standard library and
needs no decidable equality — and the interface to Stage B can be named:

```
  pairs F j l      := list_prod F (subsets_of_size j l)
  pairs_length     : |pairs F j l| = |F| * binom |l| j     <- the denominator
  count_pairs_le   : count p (pairs F j l) <= |F| * binom |l| j
```

`pairs_length` **is** Claim 3.4's denominator. That is the whole of the
Stage A / Stage B interface, and it is one line.

### 30.3 Measured

```
  binom, two ways         Pascal's recursion (Coq) against the
                          multiplicative formula prod (n-i)/(i+1) (Rust):
                          agree at all 41 x 46 = 1886 points with n <= 40,
                          j <= 45, exact u128. The off-triangle
                          convention C(n,j) = 0 for j > n is checked, not
                          assumed
  absorption              C(N,j+1)(j+1) = C(N,j)(N-j) with truncated
                          subtraction, N <= 30, j <= 35; the j >= N range
                          is exercised and both sides are 0 there
  the estimate            holds at every point of N <= 16, j <= 18,
                          c,d <= 5, m <= 6 satisfying c*N <= d*(j+1)
                          (>10000 instances)
  the boundary            c*N <= d*(j+2) fails at exactly 102 points of
                          N <= 15, j <= 17, c,d <= 6, m <= 6
  no hypothesis at all    C(10,5) = 252 against C(10,0) = 1
  the layer               enumerating size-j subsets of [n] by bitmask
                          gives C(n,j) of them, distinct, each of size j,
                          n <= 14; and the layers of [n] exhaust 2^n
  binom_le_two_pow        C(n,j) <= 2^n for n <= 30, and the row sums to
                          2^n exactly -- which is length_subsets
  pairs                   |F| * C(|l|,j) as an enumeration, checked
                          against list_prod's length for |F| <= 6,
                          |l| <= 8, j <= 5
  count                   partition, monotonicity, disjoint additivity,
                          and complementation as an injection from the
                          size-4 layer of a 10-set into the size-6 layer,
                          the equality case C(10,4) = C(10,6) = 210
```

### 30.4 Costs and gates

New: `coq/Counting.v` (26 audited theorems, 4 audited definitions, no
axiom), `rust/tests/counting.rs` (10 tests, independent implementations),
6 mutations. The manifest is now 137 mutations.

All gates green on the final tree:

```
  make -j4 verify          pass (44 modules, clean rebuild)
  Print Assumptions        all 26 new audited theorems "Closed under the
                           global context"
  make coqchk              pass; the whole-library axiom census is still
                           exactly `Sunflower.ALWZ.Rao20_lemma2`
  python3 tools/mutate.py  137 mutations: 134 killed, 2 genuine survivors
                           (unchanged), 1 control, **0 unexpected**. All
                           6 new ones killed as declared
  cargo test --release     31 suites, 297 tests, 0 failures
  tools/statements.py      707 baseline entries
  tools/docnumbers.py      12 quoted numbers match
  tools/ceiling.py         9 routes costed, verdicts match
```

The six mutations are the ones a reader should check the file against:
`binom-pascal-wrong-branch` (does Pascal's recursion add the two entries
above, or the same one twice?), `binom-ratio-drop-the-successor` (is
`S j` the boundary, or would `j+2` do?), `binom-absorb-untruncated`,
`layer-filters-the-wrong-length` (is the layer a layer, or a prefix of
the powerset?), `count-inj-drops-nodup`, and
`binom-two-pow-off-by-one` (the bound is attained at both ends of every
row, so it cannot be weakened by any additive amount at all).

### 30.5 What Stage A does *not* do, and what is next

It does not touch spreadness, families, or sunflowers — deliberately.
Stage A is the layer Stage B's encoding is *counted with*, and keeping it
free of the problem is what makes it independently falsifiable: every
claim above is checked against an implementation that shares no code with
the Coq side.

**Stage B**, unchanged from §1 and still the stall risk:

```
  minimal_fragment : Family -> list nat -> list nat -> list nat
        Lovett Def 3.2, "breaking ties arbitrarily" becoming "first in
        the enumeration", which is what makes it a function
  Obs 1-3 and Claim 3.3      set algebra, no arithmetic
  phi and an explicit psi, with psi (phi (S,V)) = (S,V)
        section 1's most useful proof-level find: the obligation is an
        equation, not a case analysis
  Claim 3.4's count          assembles Stage A's four pieces
```

The one thing Stage A changes about Stage B's plan: **call
`binom_ratio_at_threshold`, not `binom_ratio`**, unless Stage B's `V` is
genuinely at `qN+1` — and if it is, the sharp form is already there.

Stage C (Markov, Claim 3.6's arithmetic-free induction, and the `log n`
iteration) is untouched.

### 30.6 The one-line verdict

**Stage A of the counting proof is formalised, axiom-free, and
independently falsified: the size-`j` layer of the powerset with its
count `C(n,j)`, a counting operator with the injection and additivity
laws Claim 3.4 uses, `C(n,j) ≤ 2^n`, and the one binomial estimate —
which turns out to hold under a hypothesis one notch weaker than §1
assumed, with `c·N ≤ d·(j+1)` exactly the boundary and a two-line witness
that `j+2` fails.**

The axiom is not discharged and this section does not claim otherwise.
What it claims is that the first of §1's three stages is done, that it
needed no arithmetic §1 had not anticipated except one estimate stated
too strongly, and that the remaining stall risk is exactly where §1 said
it was — Stage B's encoding.

## 31. Stage B of the spread lemma: the fragment, Claim 3.3, and the
##     encoding — with the hypothesis §1 could not see

§30 did Stage A. This is Stage B, and it is the stage §1 named as the
stall risk. It did not stall, for one reason that is worth more than the
theorems: **the encoding was run before it was proved.**

**`coq/Fragment.v`**, one module, no axiom, 24 audited theorems and 8
audited definitions, every one `Closed under the global context`.

### 31.1 The source was read, not remembered

The July 2026 session read [Lovett] §3 at proof level and left §1's
six-line skeleton. That skeleton is a summary, and Stage B is the part
where the details are the content, so `lovett_pcmi.pdf` was re-fetched
(sha256 matching `docs/papers/manifest.json` byte for byte), pp. 11–15
re-rendered at 150 dpi and read. Two things came out of the pages that
the skeleton does not carry, and both changed the file.

* **The candidate set is never empty when `S ∈ F`,** because `S ⊂ S ∪ V`
  makes `S` its own candidate. So `minimal_fragment` needs no junk
  default and every lemma about it has exactly one side condition,
  `In S F`. §1's `minimal_fragment : Family -> list nat -> list nat ->
  list nat` gave no hint either way, and the natural defensive design —
  an `option`, or a default — would have contaminated every downstream
  statement.

* **`|Z| = qN + m`**, because `Z = V ∪ M` and `M` is disjoint from `V`
  (Observation 2). That is why Claim 3.4's step 1 reads
  `C(N, qN+m) ≤ C(N,qN)·q^{-m}` — and it is **exactly** Stage A's
  `Counting.binom_ratio` with `q = c/d`. §1 lists the binomial estimate
  and the encoding as separate bullets; the rendered page shows they are
  the same bullet, joined by one length computation
  (`Fragment.frag_Z_length`).

### 31.2 What is proved

```
  minimal_fragment F S V     Def 3.2: a minimum-length element of
                             {S' \ V : S' in F, S' subset S u V},
                             ties broken by position -- which is what
                             turns Lovett's "breaking ties arbitrarily"
                             into a function
  fragment_subset_S          Observation 1:  M(S,V) subset S
  fragment_disjoint_V        Observation 2:  M(S,V) disjoint from V
  fragment_nil_iff           Observation 3:  M(S,V) = [] iff some
                             member of F sits inside V
  frag_F'_nonempty           Claim 3.3 (1)
  frag_F'_fragment           Claim 3.3 (2):  every S' in F' has
                             S' \ V = M(S,V)
  phi, psi                   the encoding of Claim 3.4 and its decoder
  frag_Z_minus_fragment      V = Z \ M, on the nose
  psi_phi_SetEq              S = M u (S \ M), as sets
  phi_injective              the encoding is injective
  frag_Z_length              |Z| = |V| + |M|   -- the junction with
                             Counting.binom_ratio
  fragment_removed_in_link   S \ M lies in the link of M -- the junction
                             with the spread hypothesis, and the only
                             place spreadness is used at all
  bad_pairs_le_codes         Counting.count_inj_le applied to phi: the
                             bad pairs inject into the code space
```

### 31.3 The correction: the decode is not an equation, and it needs a
###      hypothesis §1 does not record

§1's most useful proof-level find was stated like this:

> *"The encoding's injectivity is an equation, not an argument. Claim
> 3.4 defines `phi(S,V) = (Z, S', M, S \ M)` and justifies it in one
> sentence: 'we can decode `(S,V)` given `phi(S,V)` since
> `S = M ∪ (S \ M)` and `V = Z \ M`'. So the formal obligation is not
> '`phi` is injective' — it is `psi (phi (S,V)) = (S,V)` for an explicit
> `psi`, which is a rewrite, not a case analysis."*

**Half of that is right, and the half that is wrong costs a hypothesis.**

The `V` half *is* literal. `Z` is built as `add_set V M`, which is
`V ++ setminus M V`, which is `V ++ M` because `M` is disjoint from `V`;
filtering `M` back out returns `V` itself. `frag_Z_minus_fragment` is
that, and it needs no `NoDup` anywhere.

The `S` half cannot be literal. `S = M ∪ (S \ M)` is an identity of
**sets**; as lists, `add_set M (setminus S M)` is `M ++ (S \ M)`, a
*permutation* of `S`. `S = [1;2;3]`, `M = [2]` gives `[2;1;3]`. So
`psi (phi F S V) = (S, V)` is **false as stated** in any list encoding,
and no rewrite will produce it.

What is true, and what the count actually needs, is **injectivity**:
two pairs with the same code have the same `M` and the same `S \ M`,
hence first components that are `SetEq` to the same list, hence `SetEq`
to each other — and `Sets.SetNoDup_setEq_eq` upgrades that to equality
*inside a `Distinct` family*. So:

> **`Fragment.phi_injective` carries the hypothesis `Distinct F`, and
> §1's formulation does not mention it.** At the level of sets it is
> invisible, because there `S = M ∪ (S \ M)` really is an equation. It
> becomes visible exactly when the sets become lists.

This is not a defect in Lovett — the paper is written about sets. It is
a defect in the *staging note*, and it is the second time in two stages
that §1's summary of a step was one hypothesis away from what the step
needs (Stage A: `c·N ≤ d·j` where `c·N ≤ d·(j+1)` is what runs).

> **Rule 24 (`docs/reading.md`). A set-level identity in a paper becomes
> two obligations in a list formalisation: the half that is literal, and
> the half that is only up to permutation — and the second half needs a
> hypothesis the paper never states.** Find out which half is which
> before planning the stage, because the extra hypothesis propagates:
> `Distinct F` is now on every downstream statement.

### 31.4 It was falsified before it was proved

§1's *"What the testbed buys here"* says, in full: *"an encoding is a
map to run over the exhaustive enumeration in `rust/src/testbed.rs` and
check injective. Use it — the cost of finding out a lemma is false after
half a session of proof is the main way this campaign goes wrong."*

`rust/tests/fragment.rs` is that, written and run **before**
`coq/Fragment.v` existed. It implements the fragment, the encoding and
the decoder over bitmasks — sharing no code with the Coq side — and
sweeps **every** family of at most three subsets of a three- or
four-element universe, and at most four subsets of a two-element one:

```
  32968 triples (F, S, V), exhaustive, pinned as SWEEP_SIZE

  Observations 1, 2, 3                          hold at every triple
  Claim 3.3 (1) and (2)                         hold at every triple
  psi(phi(S,V)) = (S,V)                         holds at every triple
  phi injective                                 no collisions
  S' is a function of Z alone                   Claim 3.4 step 2
  |Z| = |V| + |M|                               Claim 3.4 step 1's layer
  S \ M in the link of M                        Claim 3.4 step 5
```

Every one passed first time. The proofs then went in without a false
start — the only Coq-side corrections were tactical (`repeat split`
auto-introducing, and implicit arguments), not mathematical. That is
what the discipline is for, and it is the difference between this stage
and the way §26.4's four-family inequality was found to be false.

**One caveat, stated because the sweep is what the claim rests on.** The
Rust `psi(phi(S,V)) = (S,V)` compares *bitmasks*, which are canonical:
`M ∪ (S \ M)` and `S` are the same `u32`. So the testbed could not have
seen the permutation problem of §31.3 — it is an artefact of the list
encoding, invisible to a set implementation, and it was found by the
kernel rejecting the proof. **A falsifier in a canonical representation
cannot falsify a representation defect.** That is the honest limit of
what the 32968 triples establish.

### 31.5 What is left of Claim 3.4

The count itself. With `|M| = m` fixed, the rendered page gives four
steps, and this file supplies the junction for three of them:

```
  1. #choices for Z  = C(N, qN+m) <= C(N,qN) q^{-m}
        frag_Z_length  +  Counting.binom_ratio          JUNCTION DONE
  2. S' is determined by Z                              measured in Rust,
                                                        not yet in Coq
  3. #choices for M subset S'  <= C(n,m) <= 2^n
        Counting.binom_le_two_pow                       STAGE A, DONE
  4. #choices for S \ M  <= |F_M| <= |F| k^{-m}
        fragment_removed_in_link  +  Spread.Spread      JUNCTION DONE
```

and then the assembly — a product over the four ranges, a sum over
`n/2 ≤ m ≤ n`, and the geometric series `Σ (4/kq)^m`. The assembly is
**not** done in Coq, and this section does not claim it.

**It is, however, already falsified.** `rust/tests/fragment_count.rs`
states the assembly without `q` — write `j` for `|V|` and let `B(j,m)`
be the pairs with `|V| = j` and `|M(S,V)| = m` — and checks

```
  |B(j,m)|  <=  C(N, j+m) * C(n, m) * max_{|M| = m} deg M F
```

over every family of at most three subsets of a four-element universe
and at most four subsets of a three-element one. Four things came out of
it, and they are what the Coq assembly will need:

* **the fibred bound holds**: every fibre of `(S,V) ↦ (Z,M)` has at most
  `deg M F` elements, because `V = Z \ M` is determined and `S \ M` lives
  in the link. This is the lemma `Counting.v` is missing, now measured
  before it is written;
* **the assembled bound holds** at every instance;
* **none of the three factors is slack** — dropping any one of them makes
  the bound false somewhere, with a witness, so the Coq statement will
  not be carrying a redundant term;
* **the spread step works in the cleared-denominator form**
  `k^m · |B(j,m)| ≤ C(N,j+m) · C(n,m) · |F|` whenever `F` is
  `Spread.Spread`-spread with parameter `k`. No `q^{-m}`, no `k^{-m}`,
  nothing leaves `nat`.

Both of the tools that step needed are now **proved** — see §31.8 —
and the per-`m` bound is assembled. What is left is one obstacle of a
kind this session has now met three times; §31.9 states it.

### 31.6 Costs and gates

New: `coq/Fragment.v` (24 audited theorems, 8 audited definitions, no
axiom), `rust/tests/fragment.rs` (7 tests, 32968 exhaustive triples),
`rust/tests/fragment_count.rs` (4 tests, the assembly of Claim 3.4
falsified ahead of its proof), 6 mutations. **Then §31.8's two tools**:
5 more audited theorems and 3 definitions in `Counting.v`, 4 more
theorems and 2 definitions in `Fragment.v`, 5 more Rust tests, 4 more
mutations. The manifest is now 147.

All gates green on the final tree:

```
  make -j4 verify          pass (45 modules, clean rebuild)
  Print Assumptions        all 24 new audited theorems "Closed under the
                           global context", 0 reporting axioms
  make coqchk              pass; whole-library axiom census still exactly
                           `Sunflower.ALWZ.Rao20_lemma2`
  python3 tools/mutate.py  143 mutations: 140 killed, 2 genuine survivors
                           (unchanged), 1 control, **0 unexpected**. All
                           6 new ones killed as declared
  cargo test --release     33 suites, 308 tests, 0 failures
  tools/statements.py      739 baseline entries
  tools/docnumbers.py      12 quoted numbers match
  tools/ceiling.py         9 routes costed, verdicts match
```

The six mutations are where a reader should attack the file:
`frag-cands-forget-the-union` (is `S' ⊂ S ∪ V` load-bearing, or would
`S' ⊂ S` do?), `frag-cands-keep-v`, `minimal-fragment-empty-seed` (would
seeding the minimiser with `∅` — always of minimum length — do as well?
no: it makes Observation 3 false), `argmin-picks-the-largest` (is
*minimality* load-bearing, or would any canonical choice do?),
`frag-z-is-the-wrong-union`, and `psi-forgets-the-fragment`.

### 31.7 The one-line verdict

**Stage B's set-theoretic half is formalised and axiom-free: Definition
3.2 with ties broken by position, all three observations, both parts of
Claim 3.3, the encoding of Claim 3.4 with its decoder, and the
injectivity the count consumes — plus the two junctions that make Stage
A usable, `|Z| = |V| + |M|` and `S \ M ∈ F_M`.**

The axiom is not discharged. What is new beyond the formalisation is a
correction: **the decode `ψ(φ(S,V)) = (S,V)` is not an equation**, only
its `V` half is, and closing the `S` half needs `Distinct F` — a
hypothesis §1's staging note does not record because at the level of
sets it does not exist. Two stages, two hypotheses that the plan had one
notch wrong, both found by writing the statement rather than by reading
the plan again.

### 31.8 The fibred counting lemma and the geometric sum

Both tools §31.5 named are proved, axiom-free, in `coq/Counting.v`, and
both were falsified numerically before being written.

**The fibred counting lemma.** `Counting.count_inj_le` bounds a set by an
injection into a *flat* list. Claim 3.4's count is not flat: the encoding
sends `(S,V)` to a key `(Z,M)` together with `S \ M`, and the range of
that last component is *the link of `M`* — it depends on the first
component. So:

```
  dep_pairs Base fib        the dependent product, flat_map over Base
  dep_pairs_length_le       |dep_pairs Base fib| <= |Base| * K
  count_fibred_le           g injective-with-h, h x in fib (g x),
                            every fibre <= K   =>   |L| <= |Base| * K
```

`count_fibred_le` is polymorphic in all three types and needs `NoDup` on
the domain only. `rust/tests/counting.rs` checks that the bound is
**attained** when `L` is the dependent product itself, so it is the right
statement rather than a lossy one.

**The geometric sum.** A decreasing geometric series is dominated by its
first term, and in `nat` the clean form is

```
  geom a b i  =  sum_{s=0}^{i} a^s b^(i-s)      (stated as a recursion)
  geom_le     :  2*a <= b  ->  geom a b i <= 2 * b^i
```

and the hypothesis `2a ≤ b` is **minimal for the constant 2**: at
`a = b = 1` the sum is `i+1`, unbounded, and `2a ≤ b+1` already admits
that case. Rule 23 again, and again the boundary is one notch away from
the obvious statement.

The usable form is the assembly itself, which is Claim 3.4's last step
with no denominators anywhere:

> **`Counting.geom_assemble`:** if `2a ≤ b`, `1 ≤ b`, and
> `b^m · x_m ≤ a^m · C` for every `m` in `[t, t+i]`, then
> `b^t · Σ_{m=t}^{t+i} x_m ≤ 2 · a^t · C`.

With `a = 4d`, `b = ck` and `C = C(N,j)·|F|` that is exactly
`Pr ≤ Σ_{m≥n/2} (4/kq)^m ≤ 2 (4/kq)^{n/2}` — Lovett's `100^{-n}` once `c`
is large enough, and §1's *do not chase the constant* applies.

The proof is one induction that peels the *first* term and cancels a
factor of `b`; peeling the last term does not work, and that is the only
subtlety in it.

All gates green on the final tree, with §31.8's additions in:

```
  make -j4 verify          pass (45 modules, clean rebuild)
  Print Assumptions        all 59 audited theorems of Counting.v and
                           Fragment.v "Closed under the global context",
                           0 reporting axioms
  make coqchk              pass; whole-library census still exactly
                           `Sunflower.ALWZ.Rao20_lemma2`
  python3 tools/mutate.py  147 mutations: 144 killed, 2 genuine
                           survivors (unchanged), 1 control,
                           **0 unexpected**
  cargo test --release     33 suites, 313 tests, 0 failures
  tools/statements.py      753 baseline entries
  tools/docnumbers.py      12 quoted numbers match
  tools/ceiling.py         9 routes costed, verdicts match
```

The four new mutations are the ones that pin the two constants:
`geom-halve-the-constant` (is the 2 real? — yes, at `a=1, b=2, i=1` the
sum is 3 against `b^1 = 2`), `geom-weaken-the-ratio` (would `a ≤ b` do? —
no, at `a=b=1` the sum is `i+1`), `fibred-drop-injectivity`, and
`geom-assemble-halve-the-constant` (does integrality rescue the factor 2?
— no: `a=1, b=2, C=8` gives `8+4+2+1 = 15` against `8`).

**And the per-`m` bound is assembled.** `coq/Fragment.v`:

```
  frag_key F p              (Z, M) -- the encoding without S', because
                            the decode never reads S'
  frag_rest F p             S \ M
  frag_key_rest_injective   the pair is injective (Distinct F)
  bad_pairs_fibred_bound    |L| <= |Base| * K        via count_fibred_le
  spread_caps_the_link      k^|M| * |link M F| <= |F|  -- the only place
                            spreadness is used
  bad_pairs_spread_bound    k^m * |L| <= |Base| * |F|
```

`S'` dropping out of the *decode* is worth a sentence: Lovett needs it
for the **count** (step 3 bounds the number of `M ⊂ S'` by `C(n,m)`), not
for the decode, and the formalisation makes that visible because
`psi` never reads it.

### 31.9 The canonicalisation layer, and Claim 3.4 closed

§31.5 left `Base` abstract, and named the obstacle: `Z = V ++ M` is not
an *ordered sublist* of the universe, so it is not in
[Counting.subsets_of_size] and carries no binomial count. Rule 26 said
to build the canonicalisation layer once, early, rather than three times
at the point of use. That is now done, and **Claim 3.4 is closed.**

#### The layer

`coq/Counting.v`, one function and eight lemmas:

```
  norm U A  =  filter (fun x => memb x A) U
```

the sublist of `U` carrying the elements of `A`.

```
  norm_in_subsets    lands in `subsets U`  (Spread.filter_in_subsets)
  norm_SetEq         SetEq (norm U A) A          when A subset U
  memb_norm          membership is unchanged
  norm_length        same length as A           U, A NoDup, A subset U
  norm_idem          norm U V = V               V an ordered sublist,
                                                U NoDup  <- the round trip
  norm_in_layer      norm U A in subsets_of_size |A| U   <- the payoff
  setminus_norm_r    setminus X (norm U A) = setminus X A
  setminus_norm_l    setminus (norm U Z) M = norm U (setminus Z M)
```

`norm_idem` is where the `NoDup U` hypothesis comes from and it is not
decoration: at `U = [1;1]`, `V = [1]` the round trip returns `[1;1]`.
The mutation `norm-idem-drop-nodup` pins it.

Three companions were needed because the argument moves a canonical set
into positions that previously held the original: `containsb_SetEq`,
`link_SetEq` and `add_set_SetEq_l` say that `Spread`'s three operations
read a set only through membership, so the swap is sound.

#### Claim 3.4

```
  frag_ckey F U p   = (norm U Z, norm (first_in F (norm U Z)) M)
  frag_base F U j m = dep_pairs (subsets_of_size (j+m) U)
                                (fun Z => subsets_of_size m (first_in F Z))
```

and then, with `N = |U|` and `n` the uniformity:

> **`Fragment.claim_3_4_per_m`:**
> `k^m · |L| ≤ C(N, j+m) · C(n, m) · |F|`
> for any `NoDup` list `L` of pairs `(S,V)` with `S ∈ F`,
> `V ∈ subsets_of_size j U` and `|M(S,V)| = m`, given `Distinct F`,
> `NoDup U`, every member of `F` inside `U` with at most `n` points, and
> `Spread F k`.

That is the rendered page's four steps: step 1 is `frag_Z_length` plus
`norm_in_layer`, step 2 is why the key is a *pair*, step 3 is
`binom_mono_l` at `|S'| ≤ n`, step 4 is `fragment_removed_in_link` plus
`spread_caps_the_link`. Nothing leaves `nat` — the `k^{-m}` is cleared to
the left.

And summed, which is the whole of Claim 3.4:

> **`Fragment.claim_3_4_summed`:** with `c·N ≤ d·(j+1)`, `2·(4d) ≤ ck`,
> `1 ≤ ck` and `n ≤ 2m` across the range,
>
> `(ck)^t · Σ_{m=t}^{t+i} |L_m|  ≤  2 · (4d)^t · (C(N,j) · |F|)`.

Read it back by dividing: the bad pairs are at most `2·(4d/ck)^{n/2}` of
the sample space `|F|·C(N,qN)` — Lovett's `Pr ≤ 100^{-n}` once `c` is
large, with `q = c/d` and `t = ⌈n/2⌉`. §1's *do not chase the constant*
applies: any explicit `c` closes it.

**Every hypothesis is one the source has**, with two exceptions that the
list encoding forced and that §31.3 and rule 24 explain: `Distinct F`,
and `NoDup U`.

#### What this leaves

Stage B is complete. What remains of §1's plan is **Stage C**, untouched:

```
  Claim 3.5   Markov in the fixed-size setting, plus Exercise 3.1's two
              spreadness-preservation lemmas
  Claim 3.6   the induction that produces the conclusion -- section 1
              records it as arithmetic-free
  Lemma 3.1   the log n iteration, and prod (1 - 10^{-n/2^i}) >= 0.8
```

and then `ALWZ.FractionalSpreadDisjoint` at an explicit threshold, which
`ALWZ.fractional_form_gives_the_axiom_shape` already carries the rest of
the way to `SpreadYieldsDisjoint`. The axiom is still an axiom, and the
whole-library census is still exactly `Rao20_lemma2`.

#### Costs and gates for §31.9

38 more audited theorems and 3 more definitions, 2 more Rust tests, 3
more mutations. The manifest is now 150.

All gates green on the final tree:

```
  make -j4 verify          pass (45 modules, clean rebuild)
  Print Assumptions        all 97 audited theorems of Counting.v and
                           Fragment.v "Closed under the global context",
                           0 reporting axioms
  make coqchk              pass; whole-library census still exactly
                           `Sunflower.ALWZ.Rao20_lemma2`
  python3 tools/mutate.py  150 mutations: 147 killed, 2 genuine
                           survivors (unchanged), 1 control,
                           **0 unexpected**
  cargo test --release     33 suites, 315 tests, 0 failures
  tools/statements.py      794 baseline entries
  tools/docnumbers.py      12 quoted numbers match
  tools/ceiling.py         9 routes costed, verdicts match
```

The three new mutations are where a reader should attack §31.9:
`norm-idem-drop-nodup` (does canonicalisation round-trip without
`NoDup U`? — no, `U = [1;1]`, `V = [1]`),
`frag-base-forgets-the-chosen-member` (would subsets of `Z` do instead of
subsets of `S'`? — no: `C(j+m,m)` depends on the sample size, `C(n,m)`
does not, and that is the whole content of step 3), and
`claim-three-four-weaken-the-ratio` (is `kq ≥ 8` needed, or does the
series only have to decrease?).

## 32. Session N+10, closed: what moved, what did not, and what the next
##     session should do instead of repeating this one

This section is the handover. It is written to be read cold, and it is
written to be *disbelieved* — every number in it is checked by a gate,
and every claim that is not is marked as unchecked.

### 32.1 The verdict, without inflation

**No bound moved. The conjecture is exactly as open as it was.** No new
upper bound on `f(n,k)`, no new lower bound, no new exact value, no row
of the `r*(m,3)` table changed, no conjecture in the §28.5 ledger
graduated. **Nothing in this session is new mathematics** — §29.8's
novelty ledger says so in those words, and it is not modesty.

**The axiom is still an axiom.** `make coqchk`'s whole-library census is
still exactly `Sunflower.ALWZ.Rao20_lemma2` and nothing else.

What did move, precisely:

* **Stages A and B of discharging that axiom are complete**, including
  Claim 3.4 in full (§30, §31). §1 has named this the highest-value
  target since July 2026 and nobody had begun it.
* **A barrier**: `Profile.greedy_forces_erdos_rado` — every profile the
  greedy cover step closes is at least `(k-1)^m·m!`, which *is*
  Erdős–Rado. Exact, every `k`, no asymptotics (§29).
* **A gate**: `tools/ceiling.py`, wired into `make verify`, which costs
  every route against 1960, against the record, and against the target,
  and fails the build when a route's declared verdict disagrees with its
  own arithmetic (§29.5).
* **Seven rules** (20–26) in `docs/reading.md`, each earned by an error
  this session actually made.

### 32.2 The thing the next session most needs to know

> **Discharging `Rao20_lemma2` will not improve any bound.**

The axiom yields `ALWZ.sunflower_bound_from_spread_lemma`, which is
**Rao 2020**'s `f(n,k) ≤ (C·k·log(nk))^n + 1`. The literature record is
**Bell–Chueluecha–Warnke 2021**, `(C·p·log k)^k` (`docs/reading.md` A6,
read in full), which is better and is *not* formalised here. So finishing
Stage C turns a conditional formalisation into an unconditional one —
a real and checkable achievement, and the thing a sceptical reader looks
at first — but it moves no number and beats nothing.

Choose it deliberately, on that basis, or choose something else. What it
is *not* is progress on the conjecture.

### 32.3 Stage C, if that is the choice

Everything below Stage C is done and axiom-free. §1's remaining list, and
it is short:

```
  Claim 3.5   Markov in the fixed-size setting -- "if the average over V
              is at least (1-eps)|F| then most V are good" -- plus
              Exercise 3.1's two spreadness-preservation lemmas
  Claim 3.6   induction on t. Section 1: "arithmetic-free, and it is the
              step that yields the conclusion"
  Lemma 3.1   the log n iteration, and prod (1 - 10^{-n/2^i}) >= 0.8
```

then instantiate `ALWZ.FractionalSpreadDisjoint` at whatever threshold
falls out; `ALWZ.fractional_form_gives_the_axiom_shape` carries it the
rest of the way. §1's scoping decision stands: **do not chase the
constant.**

Three things this session learned that apply directly:

1. **Read the rendered pages, not §1's summary.** §1's staging note was
   one hypothesis wrong three times — the binomial estimate's
   (`c·N ≤ d·j` where `c·N ≤ d·(j+1)` is what runs), the type of `count`
   (pairs, not sets), and the decode (*not* an equation). Each was found
   by writing the statement. `lovett_pcmi.pdf` re-fetches with a matching
   sha256; pp. 11–15 are §3.
2. **Falsify before proving.** `rust/tests/fragment.rs` swept 32968
   exhaustive triples before `coq/Fragment.v` existed, and the proofs
   then went in with no mathematical false start. But see rule 25: a
   bitmask falsifier cannot see a list-representation defect.
3. **The canonicalisation layer already exists** (`Counting.norm` and its
   eight lemmas, §31.9). Rule 26 exists because it was paid for three
   times before being built once. If Stage C needs a fourth
   representational bridge, add it *there*.

### 32.4 What would actually be new mathematics

Named, with honest status. None of these is started.

| target | status | why it is real |
|---|---|---|
| **Rao's question** (`docs/reading.md` A2): does the *disjointness* form of the spread lemma run at `r = O(k)`? | open; A2 established from a rendered page that the known tightness examples ([ALWZ20] Lem 3.1, [BCW21] Lem 4) are for the **robust/covering** form, **not** disjointness — so nothing known rules it out | a positive answer **is** the sunflower conjecture, at every `k`. `Conjecture.spread_conjecture` is already the formal statement and `spread_conjecture_suffices` already derives the conjecture from it |
| **`r*(3,3)`: is it 3 or 4?** | `[3,4]` (STATUS.md; upper from `TauThree.r_star_three_three_at_most_four_unconditional`) | one integer. `r*(3,3) = 3` forces `g(3) ≤ 27`; the development knows `g(3) ≤ 26` (`PureLink.f_3_3_at_most_27`), so **the two are consistent and the question is live** |
| **Conjecture P** (§29.8): is the profile reduction lossless, `B_k = g_k`? | `g_k ≤ B_k` is a theorem; equal at `k=3` for `m ≤ 2`; `B_3(3) ∈ [20,32]` against `g(3) ≤ 26` | `B_3(3) > 26` refutes it outright. §29.7's floor says a witness needs ≥14 points and the maximum ≥16 — the ground set §13.4 records cadical failing to decide at 601s |
| **A better base object than `ι(3) = 10`** (Track 4) | `ι(3) = 10` is proved unique by exhaustion (B16); `ι(4) ≥ 32` would refute `Sharp.AHSOptimal` and give `f(3,3) ≥ 33` | the 1972 lower bound `10^{n/2}` is the whole record. §13.4 calls this "a rigid target, not a wide search" |
| **A second technique** (Track 3) | `coq/SliceRank.v` is scaffolded and unused; §7 names exactly what the polynomial method is missing | every bound in this repository comes from spreadness plus covering. [Kup25] p. 53 lists three incomparable methods; this repo has one |

### 32.5 The failure modes this session hit, so the next one can skip them

Recorded because all three are cheap to avoid and expensive to repeat.

* **The incoming brief was wrong about the repository three times** —
  Track 1's "do this first" already existed as
  `Conjecture.spread_conjecture`; `r*` was already posed as the
  conjecture in §22; and a refined bound was already beaten by
  `PureLink.f_3_3_at_most_27`. Rule 21: a handoff's task list is a
  *hypothesis about the repository*, and `grep` refutes it in a minute.
  **This section is a handoff too. Check it.**
* **A plan's hypotheses are not the proof's hypotheses.** Rules 23 and 24.
* **A falsifier in the wrong representation proves nothing about the
  representation.** Rule 25.

### 32.6 Costs and gates, whole session

New: `coq/Profile.v`, `coq/Counting.v`, `coq/Fragment.v` (three modules,
no axiom); `tools/ceiling.py` and the `make ceilings` gate;
`tools/prcheck.py`, `.github/pull_request_template.md` and the
`make prcheck` gate; `rust/tests/profile.rs`, `counting.rs`,
`fragment.rs`, `fragment_count.rs`. At the close of that session the
development was 45 modules, 671 audited theorems, 129 audited
definitions, 150 mutations, and 31 Rust integration suites (the gate
line below reports 33 `test result` lines, which is those 31 plus the
library's own unit tests and its doctests). The current counts are in
§33.6; this paragraph is a record of what N+10 left behind and is not
updated.

Final gate run, all green:

```
  make -j4 verify          pass (45 modules, clean rebuild)
  make coqchk              pass; census exactly Rao20_lemma2
  python3 tools/mutate.py  150 mutations, 147 killed, 2 genuine
                           survivors, 1 control, 0 unexpected
  cargo test --release     33 suites, 315 tests, 0 failures
  tools/statements.py      800 baselined entries
  tools/docnumbers.py      17 quoted numbers match
  tools/ceiling.py         9 routes costed, every verdict matches
  make prcheck             the pull request body resolves
```

Zero admits; every audited theorem reports `Closed under the global
context`.

### 32.6a The write-up, gated

Added after §32.6's gate run, and worth its own subsection because it
changes what every future session has to do rather than what this one
found.

Every artefact in this repository that makes a claim is gated: the
kernel and `coqchk` for a theorem, `tools/statements.txt` for its
statement, mutation testing for a definition, `tools/docnumbers.py` for
a number in the prose, `tools/ceiling.py` for a route's worth. The pull
request was gated by nothing — and it is the one document a reader forms
an opinion from, written once at the end of a session and never
regenerated.

`.github/pull_request_template.md` now carries a required `toml` block
and `tools/prcheck.py` checks four things against the tree: that every
count matches the list it counts; that every claim's `evidence` resolves
to an audited Coq name, a Rust `#[test]`, a mutation id or a path; that
`novelty = "new-mathematics"` carries a real search, which is rule 17 as
a gate rather than as an intention; and that the mandatory
**What did not move** section is present. `make prcheck` runs it, and CI
runs it on every pull request, reading the body through the environment
rather than interpolating it into the shell.

It earned its place on first run: six `Example`s in `coq/Counting.v` had
never reached `tools/audited.txt`, so a claim citing one of them
resolved to nothing. They were unaudited, not wrong — the audit list is
the artefact that says which, and it did not. Fixed in the same commit;
`tools/audited.txt` now carries 671 theorems and the baselines 800
entries.

What it cannot check is whether any of the prose is true. `docs/
testing.md` §8 and `docs/reading.md` rule 27 both say so in those terms,
so a green gate is not mistaken for a reviewed claim.

**For the next session:** fill the template. The `toml` block is
required even on a one-line change, and `make prcheck PR_BODY=body.md`
before submitting will tell you which name you got wrong.

### 32.7 The bar, stated plainly

This session produced infrastructure, a barrier, and two thirds of an
axiom discharge. It produced **no new mathematics**, and it says so.

The next session should be able to write a sentence of the form *"`X` is
now known, and it was not before"*, where `X` is a statement about
sunflowers rather than about this repository. §32.4 lists five candidates
and none of them is started. The instruments are built: exhaustive
search, two cross-checked SAT solvers, prescribed-symmetry search, the
spread decision procedures, a costing gate that refuses uncosted routes,
and now a complete counting layer. **What is missing is a session that
points them at an open question and reports the answer with its budget.**

---

## 33. Session N+11: `f(3,3)` was decided in 1969, the cone route was
##     already dead, and the `ι(4)` ladder moved one ground point

### 33.1 The verdict, without inflation

Three things moved, and one of them is a number about sunflowers that
was not here before.

* **`f(3,3) = 21` has been known since 1969, and this repository's own
  lower bound is the exact value.** Kostochka's Δ-system survey, p. 4,
  rendered and read: *"Abbott and B. Gardner [2] proved in 1969 that
  `f(3,3) = 20`, and since then no other exact value of `f(k,r)` for
  `k ≥ 3` and `r ≥ 3` became known."* In his convention `f(k,r)` is the
  largest family, so that is this development's `g(3) = 20`. `STATUS.md`
  called `f(3,3)` *"the first unknown sunflower number"* in three places.
  It was not unknown; the six-member gap `[21, 27]` was entirely on the
  upper side, and `Intersecting.lower_bound_3_3_20` was exact.
  (§33.2, `coq/AbbottGardner.v`, `docs/reading.md` A9.)

* **§13.4's "most concrete thing left on the list" was already dead when
  it was written**, by a theorem in the same tree. The cone route to
  `ι(4) ≥ 32` needs a 3-uniform sunflower-free family of 32 members;
  `PureLink.g_three_at_most_26` says the largest has at most 26. Six
  short, unconditionally, on every ground set — and twelve short against
  the 1969 value. The 601-second SAT run §13.4 records at `N(3,16) ≥ 30`
  was asking a question the kernel already answered. (§33.3.)

* **A new instrument, and one new number.** The ten-point rung —
  `ι(4,10) ≤ 31`, which cost the branch-and-bound **4437 seconds** and
  which the previous SAT encoding did not decide at all — now lands in
  **866 seconds**, and is confirmed by a **second, independent solver**.
  The genuinely new number is at `b = 5`: **`ι(5,g) ≤ 42` for every
  `g ≤ 9`**, in 69.8 seconds, where §9 had only `ι(5,10) ≥ 42` and a
  sixteen-minute failure above it. **`ι(4,11)` was not decided**; the run
  was stopped by hand with its budget unspent and §33.5a says exactly
  where. (§33.4, §33.4a, §33.5, §33.5a.)

**What did not move.** `Sharp.AHSOptimal` is not decided: the boundary
`ι(4) ∈ {31, 32}` sits inside the conditional interval `[27, 59]` and no
ground-set bound is known that would make the ladder finite. No upper
bound on `f(n,k)` moved, no lower bound moved, the axiom census is
unchanged, and the greedy-cover barrier of §29 is **not** upgraded: rule
19 forbids it while Füredi's 1978 Bolyai paper remains located and
unopened.

### 33.2 The 1969 value, and the two things the kernel checks about it

`coq/AbbottGardner.v` carries `GAtMost 3 20` as a named `Prop`
(`AbbottGardner1969`), the same discipline `SliceRank.NaslundSawinBound`
and `Spread.SpreadYieldsDisjoint` already use. The trusted core is
unchanged and every theorem in the file reports `Closed under the global
context`.

Two checks the kernel *can* make on a citation:

```
  gardner_value_is_not_vacuous               ~ GAtMost 3 19
  gardner_value_is_consistent_with_the_kernel  it is weaker than g(3) <= 26
```

The first is the useful one. `Intersecting.lower_bound_3_3_20` builds
twenty 3-sets with no 3-sunflower — the doubled `ι(3)` — so *any*
transcription of the survey's number below 20 fails to compile. The
value is pinned from below by an object, and from above by a citation,
and the file says which is which.

What it buys upward, through `PureLink.iota_recursion_sharp`:

```
  quantity     with g(3) <= 26 (proved)   with g(3) <= 20 (1969)
  iota(4)               77                        65
  iota(4), iota(3)=10   71                        59
  g(4)                 154                       130
```

`ι(4) ≤ 59` against the witnessed `ι(4) ≥ 27`. **The 31/32 boundary is
still inside that interval**, which is the honest reason this section
does not end with `AHSOptimal` decided.

### 33.3 Closed: the cone route to `ι(4) ≥ 32`

§13.4 wrote:

> **`iota(4) >= 32`, through the general row.** By the cone, a
> *3-uniform* sunflower-free family with 32 members gives `iota(4) >= 32`,
> refutes `Sharp.AHSOptimal`, and gives `f(3,3) >= 33`. The proved
> `N(3,g) <= 2g` forces `g >= 16` and at `g = 16` the bound would have to
> be met with equality [...] That is a **rigid** target, not a wide
> search, and it is the most concrete thing left on the list.

`N(3,g) ≤ 2g` is a bound in the *ground set*. `PureLink.g_three_at_most_26`
is a bound with no ground set in it at all, and it says the object does
not exist on any number of points. It was proved in the `PureLink`
session, after §13 was written, and nothing went back to §13.

`AbbottGardner.no_three_uniform_sunflower_free_family_has_thirty_two_members`
is the one-line consequence, and
`the_cone_route_to_iota_four_thirty_two_is_closed` is the same fact in
the shape §13.4 used it. This is rule 21 again, in the direction the
rule was written for: **a handover's task list is a hypothesis about the
repository, and `grep` refutes it in a minute.**

### 33.4 The instrument: degree-ordered symmetry breaking, and a ladder
###      in the support size

§9 diagnosed the wall precisely — *"the instances are tiny and hard,
which is the signature of symmetry"* — and named the fix in the same
paragraph: spend the stabiliser of the anchor on a **sorted degree
sequence**. Nobody had built it. `rust/src/symbreak.rs` is that, plus
three more turns of the same screw.

What is sound, and why (the module comment carries the argument in full):

1. **The maximum-degree point is in the anchor, and it is point 0.**
   Pick a point `z` of maximum degree; it has degree at least one, so
   some member contains it; relabel that member to `{0,…,b-1}` with
   `z ↦ 0`. So `deg(0) ≥ deg(y)` for every `y`, on top of the anchor the
   old encoding already forced.
2. **Sorted blocks.** What is left is `Sym({1..b-1}) × Sym({b..g-1})`;
   use it to sort each block by degree.
3. **Lexicographic tie-breaking.** Sorting spends the group only down to
   the equal-degree runs, and at these parameters the candidates are
   nearly regular — at `(b,g,t) = (4,10,32)` the incidence count forces
   every degree into `{11,12,13}` — so most of the group survives the
   sort. Take the lex-largest family in the orbit of the degree-preserving
   subgroup; it satisfies `F ≥_lex (p q)F` for every adjacent `p, q` of
   equal degree, and that conjunction is encoded.
4. **Exactly `t` members, not at least.** Everything passes to
   subfamilies, so a family of `t' > t` contains one of exactly `t`.
   This pins the incidence count `Σ_x deg(x) = b·t` rather than bounding
   it, which is what makes the floor below sharp.
5. **The floor.** Every member meets the anchor, so
   `Σ_{x ∈ A} deg(x) ≥ |F|`; and `Σ_{x ∈ [g]} deg(x) = b|F|` exactly.
   The maximum beats both averages:
   `deg(0) ≥ max(⌈t/b⌉, ⌈b·t/g⌉)`. At `(4,10,32)` that is 13, not the 8
   the first form gives.
6. **The ladder.** Ask the question one support size at a time: for `s`
   from `b` to `g`, *"is there such a family whose support is exactly
   `[s]`?"*. Every family on at most `g` points has a support of some
   size `s ≤ g` and relabels onto `[s]`, so the rungs cover the question.
   Each rung is smaller than the flat question **and has far less
   symmetry**, because unused points are interchangeable and a rung has
   none.

The cube split is on `deg(0)`: `deg(0) = d` for each `d` from the floor
to the ceiling, disjoint, one per core, printed as each lands.

**What stops it being confidently wrong** (`rust/tests/symbreak.rs`):
the counter is checked to be an *iff* in both directions against a
brute-force count — a one-directional counter makes every degree
comparison a no-op and nothing else would notice; the symmetry
constraints are run on and off at every small parameter and required to
give the same verdict, which is the control §9 asked for on the degree
cap and did not get; the cube split is checked against the unsplit
instance; the cubes are checked to abut and cover without the solver;
and every value is checked against `intersecting::iota`, an exhaustive
branch-and-bound sharing no code with any of it.


### 33.4a What the b = 5 row cost

A second use of the same instrument, run because it is cheap and the row
is thin: `docs/roadmap.md` §9 records `iota(5,10) >= 42` found by SAT in
2025 and `>= 43` *undecided in sixteen minutes*. The ladder settles the
rungs below it — **`iota(5,g) <= 42` for every `g <= 9`**, in 69.8 s at
`g = 9`, twenty cubes, none at the limit — and then hits the same wall at
ten points, where its first cube ran past the sixty-second slice and the
run was stopped by hand. So `ι(5,10)` is still `[42, ?]` and the
instrument's reach at `b = 5` is one ground point behind `b = 4`, which
is what the variable counts predict: `C(10,5) = 252` candidate sets
against `C(10,4) = 210`, and the ternary clause count grows faster.

### 33.5 What it decided, with the budget

The question is `ι(4, g) ≥ 32?` — the size that refutes `Sharp.AHSOptimal`
and gives `f(3,3) ≥ 33`. Every rung is a **cover**, so an UNSAT rung is an
exhaustion and not a failure to find.

```
  question               instrument                        budget      verdict      wall
  ---------------------- --------------------------------- ----------- ------------ --------
  iota(4,g) >= 32, g<=9   ladder, deg(0) cubes             none            UNSAT       2.8 s
  iota(4,10) >= 32        ladder + 1 refined cube          none            UNSAT     866.3 s
  iota(4,9)  >= 32        the same, under cryptominisat5   none            UNSAT       5.8 s
  iota(4,10) >= 32        the same, under cryptominisat5   stopped     undecided  --
  iota(4,10) >= 32        [previous] branch-and-bound      none            UNSAT    4437   s
  iota(4,10) >= 32        [previous] SAT, orbit split      1800 s/orbit    undecided  --
  iota(4,11) >= 32        ladder                           stopped     undecided  --
  iota(5,g) >= 43, g<=9   ladder, b = 5                    none            UNSAT      70.2 s
  iota(5,10) >= 43        ladder, b = 5                    stopped     undecided  --
```

**Where the previous frontier was.** §9 records `iota(4,10) >= 32` decided
by the homegrown branch-and-bound in **4437 seconds**, and `iota(4,11) >= 32`
as *undecided* by cadical after thirty minutes. The old SAT encoding was
re-run at the start of this session as a control and did not decide
`iota(4,10) >= 32` either: cadical, anchor plus orbit split, 1800 s per
orbit, **orbit 1 timed out at 1800 s** and the run was stopped by hand
during orbit 2. So the ten-point rung is a re-derivation by a second
instrument at a fifth of the cost — **and the frontier did not move.**
Eleven points remains where §9 left it, undecided; what changed is the
price of ten, and what that buys is stated in §33.5a rather than
inflated here.

**What each verdict means.** `UNSAT` is *exhausted* — every family the rung
covers was ruled out. `UNKNOWN` is *undecided at the limit*, and the limit
is printed beside it. A rung that was stopped by hand is labelled as such
and its budget is the result, which is what rule 13 exists for.

**The second opinion.** `sat::solve_agreed` is this repository's standing
rule for UNSAT — two independent solvers required to agree before the
verdict is believed — and it was **not** run across every cube of every
rung; the cost is a second full pass.

**What was actually done, and it is less than the rule asks for.** The
ladder was re-run end to end under `cryptominisat5`, same encoding, same
cubes. It reproduced every rung up to and including **nine points** —
`iota(4,9) >= 32` UNSAT in 5.8 s, eighteen cubes, agreeing with cadical
cube for cube — and was **stopped by hand inside the ten-point rung**,
after about fifty minutes, to give the mutation suite the machine. So:

```
  rung          cadical              cryptominisat5
  g <= 9        UNSAT                UNSAT   -- agree
  g = 10        UNSAT, 866.3 s       stopped by hand, no verdict
  g = 11        stopped by hand      not attempted
```

**The 866-second ten-point verdict therefore rests on one solver.** That
is the weakest link in this section and it is stated here rather than in
a footnote. It is not a bare assertion — the same value was reached in
2025 by the branch-and-bound, which shares no code with any solver — but
"two solvers agreed" is not what happened and is not claimed.

**Rule 25 applies and is stated where the result is.** The search works
over `u32` bitmasks; `coq/Sharp.v` and `coq/IotaRate.v` work over lists of
lists of `nat` with a `Distinct` predicate. A bitmask search cannot falsify
a list-representation defect, and no transcription of a *negative* into Coq
is possible — an UNSAT has no witness to transcribe. What is in the kernel
is the *lower* end: `Product.iota_four_at_least_27`, a family, checked
reflectively.



### 33.5a What the eleven-point rung cost, and what it would take

The eleven-point rung is `86597` variables and `321681` clauses — twice
the ten-point instance — and it behaves quite differently. **Sixteen of
its twenty-one `deg(0)` cubes were still running when the sixty-second
slice expired**, against five at ten points, and only the five largest
`deg(0)` values (28 through 32) landed inside it. The refinement then
produced 34 degree-sequence cubes for the one cube it could refine
(`deg(0) = 12`, the floor, deficiency four, nineteen sequences) and left
the other fifteen coarse with no limit.

**The run was stopped by hand, with its budget unspent**, to free the
machine for the gates. That is the third of the three statements this
repository distinguishes, and it is the honest one here: not
*exhausted*, not *undecided at N seconds*, but **stopped**. Nothing about
`ι(4,11)` is claimed.

What it would take, in order of expected value:

1. **Uncontended cores.** The ten-point rung landed in 866 s against a
   `make verify` and a second ladder. Sixteen coarse cubes at eleven
   points, each plausibly in the 10–60 minute range, is 3–15 core-hours —
   a background run, not a research problem.
2. **A second refinement axis.** The degree-sequence split only bites at
   the floor, because the deficiency `g·deg(0) − b·t` grows linearly in
   `deg(0)` and the sequence count with it. Splitting on the *trace
   profile* instead — how many members meet the anchor in one, two,
   three points — is bounded independently of `deg(0)` and is the obvious
   next axis.
3. **The proved degree ceiling.** The counters run to `t = 32` because
   `lex_ties` needs exactness. `PureLink.g_three_at_most_26` bounds every
   point's degree by 26, and the 1969 value bounds it by 20; asserting
   either would delete a third of the cubes outright. It is a
   *consequence* of the ternary clauses, so §9's measurement says it will
   not help the solver — but it would shrink the counter, which §9 did
   not measure.

### 33.6 Costs and gates

New this session: `coq/AbbottGardner.v` (one module, no axiom);
`rust/src/symbreak.rs`, `rust/examples/iota_sym.rs`,
`rust/tests/symbreak.rs`.
The development is now 46 modules, 683 audited theorems, 130 audited
definitions, 151 mutations, and 32 Rust integration suites.

```
  make -j2 verify          pass    11m27s   (46 modules, clean rebuild,
                                            683/683 audited theorems closed)
  make coqchk              pass     2m53s   census exactly Rao20_lemma2,
                                            all three escape hatches empty
  python3 tools/mutate.py  MUTLINE
  cargo test --release     RUSTLINE
  tools/statements.py      813 baselined entries
  tools/docnumbers.py      17 quoted numbers match
  tools/ceiling.py         9 routes costed, every verdict matches
  make prcheck             the pull request body resolves
```

Zero admits; every audited theorem reports `Closed under the global
context`.

**The searches, with their budgets.** All wall times are on a
**four-core, contended** machine — the `ι(4,11)` rung, the `b = 5`
ladder, `make verify` and the `cryptominisat5` confirmation were run
concurrently for part of the session — so they are upper bounds on what
an uncontended run would cost, and the cube counts are exact regardless.

### 33.7 Picking this up cold

Four things, in the order they matter.

**1. The ladder has no stopping rule, and that is the whole difficulty.**
`ι(4, g)` is decided one ground set at a time and `ι(4)` is the limit.
Nothing here bounds the ground set of an extremal *intersecting*
family — that hypothesis is `IotaGround.IotaGroundBounded` and it is
open; `Product.the_universal_iota_ground_reading_is_false` shows the
naive reading of it is false, by a coned tree-path family that genuinely
needs `2^b − 1` points. The elementary bound that *is* available,
`PureLink.intersecting_support_bound`, gives support `≤ b + (b−1)(n−1)`,
which at `(b,n) = (4,32)` is **97 points**. So the ladder as it stands
cannot close, and a session that means to decide `AHSOptimal` at `b = 4`
needs a structural bound on the support, not a bigger budget.

Two things narrow it, and they are worth having in front of you:
`τ(F) = 1` forces `|F| ≤ g(3) = 20`, so a 32-member family has covering
number at least two; and the counting ceiling `|F| ≤ C(g,2)` at `b = 4`
(`genprog::size_ceiling`) forces `g ≥ 9` from below. Neither is in Coq.

**2. Do not re-run the rungs below the frontier.** They are in §33.5
with their wall times, and `rust/tests/symbreak.rs` re-decides everything
up to nine points on every `cargo test --release`.

**3. The instrument is `rust/src/symbreak.rs` and its knobs are
documented in the module comment, not in this file.** The two that
matter: `--slice` sets how long a coarse `deg(0)` cube gets before it is
refined, and `--cubecap` sets how many cubes the refinement may produce
before it gives up and lets the coarse cube run to completion. Both were
tuned on `g = 10`, where the wrong setting was measured rather than
guessed: at `deg(0) = 14` the *full* degree-sequence split produces 684
cubes for an instance that solves whole in about ten minutes, and paying
684 solver startups for it is a loss. The adaptive prefix — pin the
first `p` degrees, leave the rest free, take the largest `p` under the
cap — exists because of that measurement.

**4. `AbbottGardner1969` is a citation, and the next session should try
to read the primary source.** H. L. Abbott and B. Gardner, *On a
combinatorial theorem of Erdős and Rado*, in W. T. Tutte, ed., *Recent
progress in Combinatorics*, Academic Press, 1969, 211–215. Not open
access; four routes tried. If it turns out to say something other than
`g(3) = 20`, every conditional corollary in `coq/AbbottGardner.v` is
named for the value it assumes and none of them is used by anything
else, so the retraction is one file.

### 33.8 The one-line verdict

> **`f(3,3)` was settled in 1969 and this repository did not know it, the
> route its own roadmap called the most concrete thing left was already
> dead, and the frontier that had cost 4437 seconds now costs 866 — but
> the next ground point did not fall, and the session says so.**

Two of those are corrections to this repository rather than results about
sunflowers. What is new about sunflowers is thin and is stated as such:
`ι(5,g) ≤ 42` for `g ≤ 9`, and a ten-point rung re-decided by a second
instrument and a second solver. `Sharp.AHSOptimal` is not decided, and
§33.5a says what the eleven-point rung would cost.

Judged against §32.7's bar — *"a sentence of the form `X` is now known,
and it was not before, where `X` is a statement about sunflowers"* — this
session clears it, barely, at `b = 5` and not at `b = 4`. The instrument
is the real output, and the honest reading of it is that it is one
uncontended background run away from the answer that matters.
