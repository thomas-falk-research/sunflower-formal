# Per-Theorem Proof Status

Run `make verify` for the live audit. Below is the static state of
the development. Definition-level testing — the checks the kernel
cannot make — is described in [`docs/testing.md`](docs/testing.md);
what to work on next is in [`docs/roadmap.md`](docs/roadmap.md).

## Closed (machine-checked, zero admits, zero axioms used)

Every theorem in this table compiles with Coq 8.18 and reports
`Closed under the global context` under `Print Assumptions`.

| Theorem | File | Statement |
|---------|------|-----------|
| `erdos_rado_upper_bound` | `coq/ErdosRado.v` | `f(n, k) ≤ (k-1)^n · n! + 1` (Erdős–Rado 1960) |
| `erdos_rado_contrapositive` | `coq/ErdosRado_Greedy.v` | Contrapositive form of the upper bound |
| `erdos_rado_via_greedy` | `coq/ErdosRado_Greedy.v` | "Existence of sunflower" form |
| `erdos_rado_counted` | `coq/ErdosRado_Greedy.v` | Function-form `UpperBound n k (er_upper_bound n k)` |
| `lower_bound_trivial` | `coq/LowerBound.v` | `f(n, k) ≥ k` via the `k-1` disjoint blocks construction |
| `lower_bound_exponential` | `coq/ProductLowerBound.v` | `f(n, k) ≥ (k-1)^n + 1` via the product-family construction (Erdős–Rado 1960) |
| `prod_family_no_literal_sunflower` | `coq/ProductLowerBound.v` | The `(k-1)`-ary product family contains no `k`-sunflower (pigeonhole + canonical-representation induction) |
| `no_k_sunflower_short_family` | `coq/LowerBound.v` | A family of size `< k` contains no `k`-sunflower |
| `SubFamilySetEq_length` | `coq/LowerBound.v` | SetNoDup S + SubFamilySetEq S F → length S ≤ length F |
| `f_n_2_eq_2` | `coq/SmallCases.v` | `f(n, 2) = 2` for all `n ≥ 1` |
| `f_1_k_eq_k` | `coq/SmallCases.v` | `f(1, k) = k` for all `k ≥ 2` |
| `f_2_3_eq_7` | `coq/F23.v` | **`f(2, 3) = 7`** — the first nontrivial exact value for `k = 3` (`UpperBound 2 3 7` by a degree/matching double-counting argument; `~ UpperBound 2 3 6` by the two-disjoint-triangles family, checked reflectively) |
| `f_2_3_lower` | `coq/F23.v` | `LowerBound 2 3 6`: the two-triangles family of six 2-sets contains no 3-sunflower |
| `hall_abstract` | `coq/HallCore.v` | Hall's marriage theorem in abstract list form (Halmos–Vaughan induction): a `NoDup`-subset Hall condition yields a pairing saturating the left part |
| `hall_marriage_theorem` | `coq/KoenigHall.v` | Hall's theorem in graph form over the `Graph`/`Matching` framework |
| `koenig_theorem` | `coq/KoenigHall.v` | König's minimax theorem: maximum matching and minimum vertex cover exist with equal size in any simple bipartite graph (via the deficiency form of Hall) |
| `pigeonhole_family` | `coq/Pigeonhole.v` | Counting lemma: if every set in `F` meets `X` and `|F| > |X|·K` then some `x ∈ X` is in `> K` sets |
| `sunflower_lift` | `coq/Sunflower.v` | A `k`-sunflower in `{A\{x}}` lifts to `{A}` with adjusted core |
| `spread_reduction` | `coq/SpreadReduction.v` | **The ALWZ §4 / Rao reduction**: if every distinct family of more than `r^m` sets of size `m` (`1 ≤ m ≤ n`) that is `r`-spread has `k` pairwise disjoint members, then `f(m,k) ≤ r^m + 1` for all `m ≤ n` |
| `elementary_spread_disjoint` | `coq/SpreadReduction.v` | The spread lemma at the elementary parameter `r = n(k-1)+1`, proved outright: maximal disjoint cover + pigeonhole |
| `spread_erdos_rado` | `coq/SpreadReduction.v` | **`f(n,k) ≤ (n(k-1)+1)^n + 1`** — an Erdős–Rado-quality bound obtained through the spread framework, with no axioms |
| `sunflower_lift_set` | `coq/Spread.v` | Set-indexed generalisation of `sunflower_lift`: a sunflower avoiding `T` lifts to one with `T` merged into the core |
| `link_sunflower_lift` | `coq/Spread.v` | A `k`-sunflower in the link `{A \ T : T ⊆ A ∈ F}` lifts to a `k`-sunflower in `F` |
| `w_spread_legacy_degenerate` | `coq/Spread.v` | Refutation of this repository's *earlier* definition of spreadness: quantifying over lists with repeats forces every member of a `w`-spread family (`w ≥ 2`) to be empty |
| `RaoSpread_Spread` | `coq/Spread.v` | Rao's absolute spread condition, plus his size hypothesis `r^m < \|F\|`, implies the fractional (ALWZ / FKNP) one — so the axiom's hypothesis is the stronger of the two |
| `spread_conjecture_suffices` | `coq/Conjecture.v` | **The conjecture restated without sunflowers**: a spread lemma with an `n`-independent threshold implies `sunflower_conjecture` |
| `spread_singletons`, `elementary_applies_to_singletons` | `coq/ALWZ.v` | Reflective non-vacuity witnesses: a concrete spread family, and a concrete instance run through every hypothesis of the axiom's shape to its conclusion |
| `threshold_is_inside_the_gap`, `axiom_hypotheses_satisfiable_in_the_gap` | `coq/ALWZ.v` | **Non-vacuity where the axiom is actually doing work.** At `n = 20`, `k = 3` the axiom's threshold is 18 while the elementary lemma needs `r > 40`, so `SpreadYieldsDisjoint 20 3 18` is an instance this development cannot prove. The circulant graph `C₃₇(1..9)` — 18-regular, 333 edges > 18² — satisfies every hypothesis of it, and the conclusion it predicts is confirmed without the axiom |
| `k_pairwise_disjoint_sunflower` | `coq/Sunflower.v` | `k` pairwise-disjoint nonempty sets are a `k`-sunflower with empty core |
| `max_disjoint_cover` | `coq/ErdosRado.v` | Greedy construction of a maximal-disjoint covering subfamily |
| `spread_disjoint_above_elementary` | `coq/SpreadReduction.v` | The elementary spread lemma for *every* `r > n(k-1)`, not just `r = n(k-1)+1` — the upper half of the axiom's truth sandwich |
| `rao_spreadb_correct`, `rao_witness_agrees`, `rao_witness_complete` | `coq/Reflect.v` | A second decision procedure for `RaoSpread`, searching the subsets of an explicit ground set, proved to return the same verdict as `Spread.rao_witness` on every input — a differential test between two independent searches, discharged by the kernel |
| `lower_bound_excludes_upper`, `lower_lt_upper` | `coq/Audit.v` | **`UpperBound` and `LowerBound` are complementary**, and every lower bound lies strictly below every upper bound |
| `no_upper_bound_below_exponential` | `coq/Audit.v` | `~ UpperBound n k m` for every `m ≤ (k-1)^n` — the first quantified refutation of `UpperBound` in the development |
| `LowerBound_antitone`, `LowerBound_ge_equiv` | `coq/Audit.v` | `LowerBound` is downward closed, and the `= m` and `≥ m` forms of it define the same predicate |
| `ContainsKSunflower_equiv`, `ContainsKSunflower_perm` | `coq/Audit.v` | Containing a sunflower is a property of the family *of sets*: invariant under permuting the family and under set-equal replacement of members |
| `sunflower_core_unique` | `coq/Audit.v` | A sunflower with at least two petals determines its core up to `SetEq` |
| `distinct_strictly_stronger` | `coq/Audit.v` | `[[0;1];[1;0]]` is `NoDup` and not `Distinct` — the design choice is not cosmetic |
| `pairwise_disjoint_ground_bound` | `coq/Audit.v` | `k` pairwise disjoint `m`-sets need `km` ground elements |
| `no_k_disjoint_of_no_sunflower` | `coq/Audit.v` | A sunflower-free family has no `k` pairwise disjoint members — the bridge that makes every sunflower-free family in the repository a candidate counterexample to the spread hypothesis |
| `spread_yields_disjoint_below_threshold`, `spread_yields_disjoint_needs_r` | `coq/Audit.v` | **The axiom's shape is false** whenever `r^m < k-1`; at `m = 1`, whenever `r < k-1` |
| `spread_yields_disjoint_sandwich` | `coq/Audit.v` | **False below `k-1`, true above `n(k-1)`** — the axiom asserts something about the gap, and is neither vacuous nor already proved |
| `no_spread_yields_disjoint_2_3_2`, `..._alt` | `coq/Audit.v` | `~ SpreadYieldsDisjoint 2 3 2`, proved twice by disjoint arguments: the five-cycle via the ground-set bound, and `two_triangles` via the reflective 3-sunflower detector |
| `bounds_coherent_er`, `bounds_coherent_spread`, `bounds_coherent_f_2_3` | `coq/Audit.v` | The development's own lower and upper bounds fit in one order — *derived* from the formal statements, so a contradictory pair would make these proofs of `False` |

## Stated as a named axiom with literature citation (not used by any closed theorem)

| Statement | File | Citation |
|-----------|------|----------|
| `Rao20_lemma2` | `coq/ALWZ.v` | **Rao 2020 (Discrete Analysis 2020:2), Lemma 2**, verbatim: "if a sequence of more than `r(p,k)^k` sets of size `k` is `r(p,k)`-spread, then the sequence must contain `p` disjoint sets", with `r(p,k) = α·p·log(pk)` and `r`-spread in Rao's absolute sense (every nonempty `Z` lies in at most `r^(k-|Z|)` members). Originally Alweiss–Lovett–Wu–Zhang 2020 (STOC 2020); refined by FKNP19 / BCW21. |

### Derived from that axiom (and from nothing else)

| Theorem | File | Statement |
|---------|------|-----------|
| `sunflower_bound_from_spread_lemma` | `coq/ALWZ.v` | `f(n,k) ≤ (α·k·log₂(kn+1))^n + 1` (Rao's Theorem 1) — the modern bound. `Print Assumptions` reports exactly `Rao20_lemma2`, and the `make verify` audit checks that it lists exactly one name. |

### What changed, and why it matters

Previously the axiom **was** the modern bound: the conclusion of the
2020 papers was assumed wholesale. It is now the *spread lemma* — a
self-contained statement about finite families that mentions neither
sunflowers nor bounds — and the step from it to the bound (the ALWZ §4 /
Rao reduction) is machine-checked in `coq/SpreadReduction.v`. This
strictly shrinks the trusted core, and it makes the interface for a
future proof exactly Rao's Lemma 2.

The statement was checked against the source rather than reconstructed:
Rao's spread condition is *absolute* (`deg Z ≤ r^(k-|Z|)` for nonempty
`Z`) and comes with the size hypothesis `|F| > r^k`. Together these are
strictly stronger than the fractional condition used elsewhere in the
literature — `Spread.RaoSpread_Spread` proves the implication — so
stating the axiom this way assumes strictly less. Two further
deliberate weakenings: the axiom covers only families of sets of one
fixed size (the source allows "at most"), and `Nat.log2_up (S (k*n))`
over-estimates `log(kn)`, so more is demanded of `r`.

The same reduction, instantiated with an elementary spread lemma that
*is* proved here, yields the axiom-free `spread_erdos_rado` above — so
the framework is known to prove something, not merely to typecheck. And
`ALWZ.elementary_applies_to_singletons` runs a concrete family through
every hypothesis of the axiom's shape to its conclusion.

A defect in the previous file was found in the process and is recorded
as a theorem rather than a comment: the old `w_spread` definition
quantified over lists with repeated entries and is degenerate
(`w_spread_legacy_degenerate` proves it forces every member to be
empty). The corrected definitions quantify over `NoDup` lists, and
`ALWZ.spread_singletons` certifies by `vm_compute` that a concrete
spread family exists.

## Stated in `coq/Conjecture.v` but **open since 1960**

| Statement | File | Status |
|-----------|------|--------|
| **Sunflower Conjecture**: `∃ c : nat → nat, ∀ n k ≥ 2, UpperBound n k ((c k)^n + 1)` | `coq/Conjecture.v` `sunflower_conjecture` | **Open**. Erdős's $1000 prize remains unclaimed. |
| **k = 3 special case** | `coq/Conjecture.v` `sunflower_conjecture_k_3` | **Open**. The case Erdős singled out as containing "the whole difficulty". |
| **Spread restatement**: `∃ c, ∀ n k, SpreadYieldsDisjoint n k (c k)` | `coq/Conjecture.v` `spread_conjecture` | **Open**, and *sufficient*: `spread_conjecture_suffices` proves it implies the conjecture. An equivalent question with no sunflower in it. |

## Not formalized; proved in docs / verified computationally

| Statement | Doc | Verification |
|-----------|-----|--------------|
| `f(n, k) ≥ (k-1)^n + 1` (standard exponential lower bound) | `docs/problem.md` | **Now fully formalized** in `coq/ProductLowerBound.v` (`lower_bound_exponential`, closed under the global context) — see the "Closed" table above. The Rust brute-force checks in `rust/tests/small_cases.rs` remain as an independent computational cross-check. |
| `f(n, k) = o(n!)` (Kostochka 1997 refinement) | `docs/proof_strategies.md` | Not verified here. |
| The **spread lemma** at the 2020 parameter `r = Θ(k log(nk))` (ALWZ–Rao–FKNP–BCW) | `coq/ALWZ.v` named axiom + `docs/spread_framework.md` | Not proved in Coq. Rao's encoding proof is elementary (injections + binomial counting, no measure theory) and is the natural next target; everything downstream of it is already proved. |

## Axiom and admit audit

The `make verify` target runs `Print Assumptions` on every closed
theorem above. The expected output is:

```
Closed under the global context.
```

for every theorem in the "Closed" table (51 of them). The current
state of the codebase satisfies this; the only `Axiom` in the entire
Coq development is `ALWZ.Rao20_lemma2`, and it is *not used* by
any closed theorem (confirmed by `Print Assumptions`).

`make verify` additionally runs an `axiom-audit` step that prints the
full assumption set of `ALWZ.sunflower_bound_from_spread_lemma` — the
one theorem that does use the axiom — so the exact statement being
trusted is visible in the build log rather than buried in a source
file. CI gates on both: 51 `Closed under the global context` lines, no
closed theorem listing `Axioms:`, and exactly one axiom name under the
modern bound.

To verify directly:

```bash
echo 'From Sunflower Require Import ErdosRado ErdosRado_Greedy LowerBound ProductLowerBound SmallCases Pigeonhole SpreadReduction ALWZ Reflect Audit.
Print Assumptions ErdosRado.erdos_rado_upper_bound.
Print Assumptions ErdosRado_Greedy.erdos_rado_via_greedy.
Print Assumptions LowerBound.lower_bound_trivial.
Print Assumptions ProductLowerBound.lower_bound_exponential.
Print Assumptions SmallCases.f_n_2_eq_2.
Print Assumptions SmallCases.f_1_k_eq_k.
Print Assumptions Pigeonhole.pigeonhole_family.
Print Assumptions SpreadReduction.spread_reduction.
Print Assumptions SpreadReduction.spread_erdos_rado.
Print Assumptions ALWZ.sunflower_bound_from_spread_lemma.
Print Assumptions Audit.spread_yields_disjoint_sandwich.
Print Assumptions Reflect.rao_witness_agrees.' | coqtop -Q coq Sunflower 2>&1 | grep -B 1 "Closed\|Axioms"
```

The Rust companion in `rust/` is an *independent* computational
cross-check; see `rust/tests/small_cases.rs` for the brute-force
assertions tying the formal bounds to concrete instances, and
`rust/tests/spread_axiom.rs` for the falsification testbed.

## Definition-level testing

`Print Assumptions` says nothing about whether a definition means what
its name claims, which is the failure mode this development has
produced twice. Three further checks target it; the methodology, and
what it does and does not cover, is in [`docs/testing.md`](docs/testing.md).

| Check | Command | What it would catch |
|---|---|---|
| Independent re-check | `make coqchk` | An `Admitted` or a second `Axiom` **anywhere** in the 19 modules, not just among the audited names; reliance on type-in-type, unsafe fixpoints, or assumed positivity |
| Coherence theorems | part of `make verify` | Two definitions that contradict each other; a bound predicate that is not what its name says; an axiom shape that is vacuously true |
| Exhaustive falsification | `make testbed` | A spread hypothesis that is false at small parameters — i.e. stated weaker than the source states it |
| Mutation testing | `make mutants` | A hypothesis in a definition that no theorem is sensitive to |

Current mutation results: 24 mutations, all matching the outcome
declared in `tools/mutations.toml` — 22 killed outright, one
(`lowerbound-at-least`) killed only at the level of tactic scripts,
which the harness establishes by applying declared repairs that touch
no statement, and which `Audit.LowerBound_ge_equiv` explains as a
theorem, and one positive control (`canary-alpha-rename`, an
alpha-rename that must survive, so the `survived` path is exercised on
every run). No genuine survivors.

`make coqchk` re-verifies all 19 modules with Coq's separate kernel
checker and reports the assumptions of the whole library:

```
* Axioms:
    Sunflower.ALWZ.Rao20_lemma2
* Constants/Inductives relying on type-in-type: <none>
* Constants/Inductives relying on unsafe (co)fixpoints: <none>
* Inductives whose positivity is assumed: <none>
```

CI gates on all four lines. This is what makes "zero admits" a claim
about the development rather than about the 51 theorem names the
`Print Assumptions` audit enumerates — an `Admitted` lemma outside
that list passes the audit and fails this census.

The empirical spread thresholds from `make testbed`, all of them at or
below the value proved sufficient by
`SpreadReduction.spread_disjoint_above_elementary`, and exactly `k-1`
at uniformity 1:

```
  ground  m   k   empirical r*   proved sufficient   refuted r
       6  1   3              2                   3   1
       8  1   4              3                   4   1,2
       8  1   5              4                   5   1,2,3
       5  2   3              3                   5   1,2
       8  2   3              3                   5   1,2
       8  2   4              4                   7   1,2,3
       7  3   3              3                   7   1,2
```
