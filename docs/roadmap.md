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

## 1. Discharging the axiom: Rao's Lemma 2

The one axiom is `ALWZ.Rao20_lemma2`. Everything downstream of it is
already proved, so discharging it is the single highest-value target,
and the interface is fixed: prove `SpreadYieldsDisjoint n k r` for
`r ≳ k log(nk)` and the file closes with no other changes.

Rao's proof is elementary — injections between finite sets and
binomial estimates, no measure theory — which is what makes it a
realistic target at all. Re-read the paper before writing a line. That
discipline is what caught the fractional-vs-absolute error.

### Stage A — the counting layer

**The technical choice that decides feasibility.** The covering step
is usually stated for a uniformly random subset of *fixed size*, which
drags in binomial coefficients and their estimates. Stated instead for
the **product measure** — each element included independently with
probability 1/2 — "probability" becomes plain cardinality over the
powerset, and `Spread.subsets` is already exactly that enumeration.

Build:

* `count : (list nat -> bool) -> list (list nat) -> nat`;
* injection-implies-`≤`;
* additivity over disjoint predicates;
* `length (subsets U) = 2 ^ length U`.

Self-contained, independently testable, reusable. Likely one session.

### Stage B — the encoding

The mathematical core: the map from "sets `W` containing no member of
`F`" to compressed encodings, and its injectivity. This is where a
session's budget should go, and where the stall risk is.

### Stage C — the arithmetic

Where the explicit constant lives.

**Scoping decision — do not chase the constant.** The axiom is
existentially quantified over `α`, so *any* explicit constant
discharges it: `α = 2²⁰` closes the file exactly as well as `α = 64`.
Chasing sharpness is where this campaign dies.

### What the testbed now buys here

Each stage's statements can be checked before they are proved. A
counting lemma is a Rust one-liner to falsify; an encoding is a map to
run over the exhaustive enumeration in `rust/src/testbed.rs` and check
injective. Use it — the cost of finding out a lemma is false after
half a session of proof is the main way this campaign goes wrong.

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

* **Generate the mutations instead of hand-writing them.** For every
  `≤` in a `Definition`, emit a `<`; for every `NoDup X ->`, emit a
  drop. Then report which definitions no mutation covers. That turns
  mutation testing from 35 anecdotes into a coverage metric over the
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

### The next target: the substitution recursion

Abbott, Hanson and Sauer (*Intersection theorems for systems of sets*,
JCTA 12 (1972) 381–389) reach `f(n,3) >= 10^(n/2 - c log n)` — a rate of
`10^(1/2) = 3.162...` per point against the direct sum's
`6^(1/2) = 2.449...`. The mechanism is **not** the direct sum. It is a
*substitution* recursion

```
g(ab) >= g(a) * g(b)^a
```

— the direct sum only gives `g(ab) >= g(b)^a`, so the extra factor
`g(a)` is the whole difference. Iterating it from a base at uniformity
`a` drives the per-point rate to the fixed point of
`c = c(a)^(1/b) * c(b)`, which at `a = b = 3` is `g(3)^(3/2)`; with
`g(3) = 10` that is exactly `10^(1/2)`. The published rate and the
published recursion agree, which is the check that says the recursion
was transcribed correctly.

Formalising it is the natural successor to `DirectSum.v` and reuses its
whole apparatus (relabelling, the split-at-the-boundary argument). The
construction is a blow-up: replace each point of a member of the
`a`-uniform family by a copy of the `b`-uniform family. **What has not
been checked is which side condition makes it sunflower-free** — the
naive version is false, because two petals can meet inside a block
without meeting outside it, so the projection to the `a`-uniform family
is not a `Δ`-system. An intersecting inner family is the obvious repair
and was not verified against the source. Settle that *computationally
first*, the way `rust/tests/link_characterisation.rs` settled the link
characterisation, before writing any Coq.

Two caveats on the citation, both load-bearing:

* the paper was **not read** — this is from secondary sources. The rate
  and the recursion corroborate each other, the base case does not:
  a "3-uniform family of size 10" is reported as the seed, but the
  direct sum already gives `g(3,3) >= 12` (`two_triangles` summed with
  two singletons, brute-force checked in
  `rust/tests/direct_sum.rs`). So either the reported seed is at a
  different uniformity, or it is for a different function. Read the
  paper before building on the number `10`;
* the correction `10^(-c log n)` is **not a constant** — it is
  `n^(-2.303c)` for natural log — so "AHS beats `3^n` from about `n = 30`"
  is wrong. The crossover solves `0.0527 n > 2.303 c ln n`, and with `c`
  unquoted the honest answer is "somewhere in the hundreds at least".

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
