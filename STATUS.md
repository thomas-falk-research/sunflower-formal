# Per-Theorem Proof Status

Run `make verify` for the live audit. Below is the static state of
the development.

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
| `k_pairwise_disjoint_sunflower` | `coq/Sunflower.v` | `k` pairwise-disjoint nonempty sets are a `k`-sunflower with empty core |
| `max_disjoint_cover` | `coq/ErdosRado.v` | Greedy construction of a maximal-disjoint covering subfamily |

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

for every theorem in the "Closed" table (26 of them). The current
state of the codebase satisfies this; the only `Axiom` in the entire
Coq development is `ALWZ.Rao20_lemma2`, and it is *not used* by
any closed theorem (confirmed by `Print Assumptions`).

`make verify` additionally runs an `axiom-audit` step that prints the
full assumption set of `ALWZ.sunflower_bound_from_spread_lemma` — the
one theorem that does use the axiom — so the exact statement being
trusted is visible in the build log rather than buried in a source
file. CI gates on both: 22 `Closed under the global context` lines, no
closed theorem listing `Axioms:`, and exactly one axiom name under the
modern bound.

To verify directly:

```bash
echo 'From Sunflower Require Import ErdosRado ErdosRado_Greedy LowerBound ProductLowerBound SmallCases Pigeonhole SpreadReduction ALWZ.
Print Assumptions ErdosRado.erdos_rado_upper_bound.
Print Assumptions ErdosRado_Greedy.erdos_rado_via_greedy.
Print Assumptions LowerBound.lower_bound_trivial.
Print Assumptions ProductLowerBound.lower_bound_exponential.
Print Assumptions SmallCases.f_n_2_eq_2.
Print Assumptions SmallCases.f_1_k_eq_k.
Print Assumptions Pigeonhole.pigeonhole_family.
Print Assumptions SpreadReduction.spread_reduction.
Print Assumptions SpreadReduction.spread_erdos_rado.
Print Assumptions ALWZ.sunflower_bound_from_spread_lemma.' | coqtop -Q coq Sunflower 2>&1 | grep -B 1 "Closed\|Axioms"
```

The Rust companion in `rust/` is an *independent* computational
cross-check; see `rust/tests/small_cases.rs` for the 22 brute-force
assertions tying the formal bounds to concrete instances.
