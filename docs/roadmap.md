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
  mutation testing from 53 anecdotes into a coverage metric over the
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
  5   >=42 (ground 10)   >=2.5457
```

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
sunflower-free family can. It is exactly the property a ground-set bound
needs and exactly the property the general problem lacks.

`coq/IotaGround.v` composes the two:

```
IotaGroundBounded c  +  [NaSa17]  ==>  sunflower_conjecture_k_3
```

with the same explicit constant, through the same arithmetic — which is
now factored out of `bounded_ground_set_settles_k3` as
`SliceRank.ns_bound_to_exponential` so neither theorem owns it.
`Audit.the_two_ground_hypotheses_are_both_sufficient` puts the two
side by side. Neither implies the other; what separates them is that one
has a measurement behind it.

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
  f'(k,s)  =  C(k+s-2, k) + 1
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

### Why it fails, exactly

`LinkCharacterisation.sunflower_iff_link_matching` says a family is
sunflower-free exactly when **every** link has matching number `<= 2`.
Measured over every counterexample in range, and on `two_triangles`
specifically:

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

### Bounded items, with one reordering

The uniformity-2 campaign (§3a) may have the wrong citation attached. See
`docs/references.md`: the exact values `f(2,k)` appear to be due to
[AHS72] in 1972 rather than [CH76] in 1976, since [Kup25] quotes an
[AHS72] formula that equals `CH(s,s)` at every `s` this repository can
compute. Only the *diagonal* `CH(D,D)` is ever needed here, and if
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
