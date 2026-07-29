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
| `k_pairwise_disjoint_sunflower`, `SetNoDup_of_pairwise_disjoint` | `coq/Sunflower.v` | `k` pairwise-disjoint sets are a `k`-sunflower with empty core. No nonemptiness hypothesis: two literally distinct members that were set-equal would be disjoint from each other, hence both `[]`, hence literally equal. Dropping it is what lets a family contain a set equal to the core of a sunflower it belongs to — the case `LinkCharacterisation.v` needs |
| `max_disjoint_cover` | `coq/ErdosRado.v` | Greedy construction of a maximal-disjoint covering subfamily |
| `spread_disjoint_above_elementary` | `coq/SpreadReduction.v` | The elementary spread lemma for *every* `r > n(k-1)`, not just `r = n(k-1)+1` — the upper half of the axiom's truth sandwich |
| `rao_spreadb_correct`, `rao_witness_agrees`, `rao_witness_complete` | `coq/Reflect.v` | A second decision procedure for `RaoSpread`, searching the subsets of an explicit ground set, proved to return the same verdict as `Spread.rao_witness` on every input — a differential test between two independent searches, discharged by the kernel |
| `lower_bound_excludes_upper`, `lower_lt_upper` | `coq/Audit.v` | **`UpperBound` and `LowerBound` are complementary**, and every lower bound lies strictly below every upper bound |
| `no_upper_bound_below_exponential` | `coq/Audit.v` | `~ UpperBound n k m` for every `m ≤ (k-1)^n` — the first quantified refutation of `UpperBound` in the development |
| `LowerBound_antitone`, `LowerBound_ge_equiv` | `coq/Audit.v` | `LowerBound` is downward closed, and the `= m` and `≥ m` forms of it define the same predicate |
| `ContainsKSunflower_equiv`, `ContainsKSunflower_perm` | `coq/Audit.v` | Containing a sunflower is a property of the family *of sets*: invariant under permuting the family and under set-equal replacement of members |
| `sunflower_core_unique` | `coq/Audit.v` | A sunflower with at least two petals determines its core up to `SetEq` |
| `distinct_strictly_stronger` | `coq/Audit.v` | `[[0;1];[1;0]]` is `NoDup` and not `Distinct` — the design choice is not cosmetic |
| `pairwise_disjoint_ground_bound` | `coq/LowerBound.v` | `k` pairwise disjoint `m`-sets need `km` ground elements |
| `no_k_disjoint_of_no_sunflower` | `coq/Audit.v` | A sunflower-free family has no `k` pairwise disjoint members — the bridge that makes every sunflower-free family in the repository a candidate counterexample to the spread hypothesis |
| `spread_yields_disjoint_below_threshold`, `spread_yields_disjoint_needs_r` | `coq/Audit.v` | **The axiom's shape is false** whenever `r^m < k-1`; at `m = 1`, whenever `r < k-1` |
| `spread_yields_disjoint_sandwich` | `coq/Audit.v` | **False below `k-1`, true above `n(k-1)`** — the axiom asserts something about the gap, and is neither vacuous nor already proved |
| `no_spread_yields_disjoint_2_3_2`, `..._alt` | `coq/Audit.v` | `~ SpreadYieldsDisjoint 2 3 2`, proved twice by disjoint arguments: the five-cycle via the ground-set bound, and `two_triangles` via the reflective 3-sunflower detector |
| `sunflower_shape` | `coq/TwoUniform.v` | Every sunflower on `≥ 2` members is pairwise disjoint or passes through a common point — the core is empty or it is not. No uniformity hypothesis |
| `star_sunflower` | `coq/TwoUniform.v` | The converse at uniformity 2: distinct 2-sets through a common point *are* a sunflower with that point as core. False at uniformity 3 (`Audit.star_needs_uniformity_two`) |
| `two_uniform_sunflower_iff`, `two_uniform_sunflower_free_iff` | `coq/TwoUniform.v` | **A distinct 2-uniform family has no `k`-sunflower exactly when its matching number and its maximum degree are both `≤ k-1`.** So `f(2,k)` *is* the Chvátal–Hanson extremal problem at `D = ν = k-1`, not merely bounded by it. The extremal function itself is cited ([Chvátal–Hanson 1976](docs/references.md)) and not formalised; no theorem here depends on it |
| `rao_spread_two_iff_degree` | `coq/TwoUniform.v` | At uniformity 2 the spread condition is a maximum-degree bound: `RaoSpread 2 F r ↔ ∀ v, deg [v] F ≤ r`. The `\|T\| = 2` clause asks `deg T F ≤ r⁰ = 1`, which `Distinct` already gives |
| `spread_yields_disjoint_two_is_a_graph_statement` | `coq/TwoUniform.v` | **The spread hypothesis at uniformity 2 is the same extremal problem**: a graph with maximum degree `≤ r` and more than `r²` edges has `k` disjoint edges |
| `sunflower_iff_link_matching` | `coq/LinkCharacterisation.v` | **A `k`-sunflower is exactly `k` pairwise disjoint members of some link**: `ContainsKSunflower k F ↔ ∃ Y, HasKDisjoint k (link Y F)`. At every uniformity, with no hypotheses at all — not uniformity, not `Distinct`, not `2 ≤ k`. Falsified by exhaustive enumeration before it was proved (`rust/tests/link_characterisation.rs`) |
| `sunflower_gives_link_matching`, `link_matching_gives_sunflower` | `coq/LinkCharacterisation.v` | The two directions. The asymmetry is the content: the link-to-sunflower direction needs nothing (it is `link_sunflower_lift` applied to the empty core), the sunflower-to-link direction needs `2 ≤ k` to know the core lies inside every member — and `sunflower_core_lies_in_a_member` records that it therefore lies inside a member of `F`, which bounds the cores worth searching |
| `two_uniform_sunflower_iff_via_link` | `coq/LinkCharacterisation.v` | `TwoUniform.two_uniform_sunflower_iff` **re-derived from the general characterisation**, mentioning neither `sunflower_shape` nor `star_sunflower`. Two independent routes to one statement; `Audit.the_shape_route_proves_it` and `Audit.the_link_route_proves_it` check both against one named specification |
| `two_uniform_only_small_cores`, `two_common_points_force_a_big_core` | `coq/LinkCharacterisation.v` | **Why uniformity 2 is a graph problem and higher uniformity is not.** At uniformity 2 every core carrying a `k ≥ 2` matching has at most one point, so the search over `Y` collapses to `∅` and the vertices. A family whose members share two distinct points admits *no* such core — `Audit.core_of_size_two_is_needed` is the smallest 3-uniform instance |
| `link_setEq` | `coq/LinkCharacterisation.v` | The link depends on its core only through the underlying set, and literally so — without this the `∃ Y` would be quantifying over list representations rather than over sets |
| `two_cliques_no_sunflower`, `two_cliques_lower_bound` | `coq/CliqueLowerBound.v` | **`f(2,k) ≥ k(k-1) + 1` for every odd `k`** — two disjoint copies of `K_k`, an infinite family of exact sunflower lower bounds generalising `two_triangles`. Degree bound is local; matching bound is a parity argument, and `Audit.oddness_is_needed` shows the parity hypothesis is load-bearing |
| `no_upper_bound_at_ch` | `coq/CliqueLowerBound.v` | `~ UpperBound 2 k (k(k-1))` for odd `k` |
| `lower_bound_2_3_from_cliques` | `coq/CliqueLowerBound.v` | `LowerBound 2 3 6` re-derived from the general construction, sharing no step with `F23.f_2_3_lower`: that one evaluates a reflective detector on a literal family, this one counts degrees and matchings in a symbolic one |
| `star_needs_uniformity_two`, `two_triangles_saturates_both_parameters`, `both_sunflower_shapes_occur` | `coq/Audit.v` | The uniformity-2 hypothesis is load-bearing; `two_triangles` is tight for *both* parameters at once, so it attains `CH(2,2)`; both branches of the shape lemma are realised |
| `a_member_may_equal_the_core`, `core_of_size_two_is_needed` | `coq/Audit.v` | The two readings of the link characterisation that no uniform family distinguishes, pinned in the kernel: `{1}, {1,2}, {1,3}` is a 3-sunflower whose core is also a member, so the *empty* petal must count; `{0,1,2}, {0,1,3}, {0,1,4}` is one whose every working core has two distinct points, so cores of size `≤ 1` do not suffice above uniformity 2 |
| `bounds_coherent_clique`, `clique_construction_is_two_triangles_reordered`, `oddness_is_needed` | `coq/Audit.v` | The clique bound contradicts no proved upper bound; at `k = 3` it is `two_triangles` reordered; at even `k` the same construction *does* contain a `k`-sunflower |
| `sum_family_no_sunflower` | `coq/DirectSum.v` | **The direct sum of two sunflower-free families is sunflower-free.** Given `Uniform a F1` and `CrossDisjoint F1 F2`, with neither family containing a `k`-sunflower, `{A ++ B}` contains none either. The argument splits every candidate petal at the ground-set boundary; the halves have constant pairwise intersections, so either the first halves are a sunflower in `F1`, or two coincide — and then uniformity forces *all* of them to coincide, making the second halves a sunflower in `F2`. Only the *first* family need be uniform, and neither need be `Distinct`: those three hypotheses were in the statement until `make mutants` reported that no proof was sensitive to them |
| `lower_bound_sum`, `lower_bound_power` | `coq/DirectSum.v` | **`g(a+b,k) >= g(a,k)·g(b,k)`** for `g = f-1`, and its iterate `LowerBound (t*a) k (p^t)`. The two families come from `LowerBound`'s existential on unspecified ground sets, so one is relabelled by `x -> 2x` and the other by `x -> 2x+1` before summing |
| `relabel_preserves`, `rmapF_no_sunflower` | `coq/DirectSum.v` | Uniformity, distinctness, size and sunflower-freeness are invariant under any injective relabelling of the ground set given with an explicit left inverse. The transport of a sunflower *back* through the relabelling is the only direction needing an argument, and it goes through `contains_sunflower_literal` so every witness member is literally an image |
| `lower_bound_f_n_3`, `lower_bound_f_n_3_odd` | `coq/DirectSum.v` | **`f(n,3) >= 6^(n/2) + 1 = 2.449...^n`** — the exact value `f(2,3) = 7` raised to the `t`-th power. Strictly better than `ProductLowerBound`'s `2^n + 1` |
| `lower_bound_cliques_power`, `lower_bound_cliques_power_odd` | `coq/DirectSum.v` | **`f(n,k) >= (k(k-1))^(n/2) + 1` at every odd `k`** — the same, seeded by `two_cliques_lower_bound` |
| `cliques_beat_product`, `six_beats_four` | `coq/DirectSum.v` | `(k-1)^(2t) < (k(k-1))^t` for `t >= 1`: the improvement is a factor `(k/(k-1))^t`, geometric in the uniformity rather than a constant. At `t = 0` it is `1 < 1` and false, which is why `1 <= t` is a hypothesis |
| `lower_bound_exponential_via_direct_sum` | `coq/DirectSum.v` | `f(n,k) >= (k-1)^n + 1` re-derived as the `n`-fold direct sum of the trivial `(k-1)`-point family, sharing no step with `ProductLowerBound.lower_bound_exponential`. `Audit.the_product_route_proves_it` and `Audit.the_direct_sum_route_proves_it` check both against one named specification |
| `bounds_coherent_direct_sum`, `direct_sum_strictly_beyond_the_product` | `coq/Audit.v` | The new bound contradicts neither upper bound, and it refutes `UpperBound (2t) 3 m` at an `m` strictly above `no_upper_bound_below_exponential`'s ceiling — so it is a statement the rest of the development cannot prove |
| `uniformity_is_needed_in_the_direct_sum` | `coq/Audit.v` | **The uniformity hypothesis is the theorem.** `{0}, {0,1}` and `{2}, {2,3}` have two members each, so neither contains a 3-sunflower; their ground sets are disjoint; and their direct sum contains one, with core `{0,2}`. The mechanism is exactly the step uniformity licenses — without it `{0}` sits inside `{0,1}` without equalling it |
| `sum_family_no_sunflower_right`, `sum_family_comm_equiv` | `coq/Audit.v` | The asymmetry in `sum_family_no_sunflower` is about the proof, not the construction: the two sums are the same family with the halves swapped, so *either* side's uniformity suffices. Needs `ContainsKSunflower_equiv`, which is why it lives here |
| `f_4_3_at_least_37` | `coq/Audit.v` | The general theorems evaluated: `f(4,3) >= 37` where the development previously reached `f(4,3) >= 17` |
| `doubling_lower_bound`, `double_no_sunflower` | `coq/Intersecting.v` | **`g(b) ≥ 2·ι(b)`** where `ι(b)` is the largest *intersecting* 3-sunflower-free `b`-uniform family. Two disjoint copies of an intersecting sunflower-free family are sunflower-free: any three members put two in the same copy, and those two meet, while a member of the other copy is disjoint from both — a sunflower cannot have one pairwise intersection empty and another not. Generalises `two_triangles`, which is the `b = 2` case |
| `lower_bound_3_3_20`, `lower_bound_f_n_3_sharp` | `coq/Intersecting.v` | **`f(3,3) ≥ 21`** and **`f(n,3) ≥ 20^(n/3) + 1 = 2.714...^n`**. Exhaustive search gives `ι(3) = 10` on six points; doubling it gives twenty 3-sets on twelve. Beats the previous headline `6^(n/2) = 2.449...^n`, and `twenty_beats_six` proves the gap compounds (`400^t` against `216^t` at uniformity `6t`) |
| `intersecting_link_bound`, `iota_three_at_most_eighteen` | `coq/Intersecting.v` | **`ι(b) ≤ b·g(b-1)`** — the one thing proved about `ι` in the upward direction, everything else about it being measured. Every member of an intersecting family meets a fixed member, which has only `b` points, so some point lies in at least `|F|/b` members; the link there is sunflower-free of uniformity `b-1`. With the proved `g(2) = 6` this gives `ι(3) ≤ 18` against the measured 10 — loose, and recorded as loose, but it is what makes the search's answers checkable rather than merely reported |
| `intersecting_is_needed_in_the_doubling` | `coq/Audit.v` | **The hypothesis is the theorem.** `{0}, {1}` is sunflower-free because it has two members, is not intersecting, and its doubling is four singletons — any three pairwise disjoint, so a 3-sunflower |
| `lower_bound_3_3_14`, `no_upper_bound_3_3_14` | `coq/SliceRank.v` | **`f(3,3) ≥ 15`** — a 14-member 3-uniform family on nine points, the exhaustive maximum `N(3,9)` found by `rust/examples/ground_scan.rs` and re-checked here by the reflective detector, so the Coq side takes nothing from the search. Beats the direct sum's 13 at the same uniformity. It does *not* improve the rate: `14^(1/3) = 2.41` is below `6^(1/2) = 2.449` |
| `every_uniform_family_is_a_link`, `link_restriction_is_vacuous` | `coq/SpreadRestrictions.v` | **The class of iterated links is every uniform family.** For any uniform distinct `G` and any `d`, glueing `d` fresh points onto every member gives a uniform distinct `F` of uniformity `d + j` with `link Y F = G` *literally*. So a spread lemma restricted to the families the recursion produces implies the unrestricted one — the restriction restricts nothing, and the "characterise the class of iterated links" direction is closed with a theorem |
| `every_sunflower_free_family_is_a_link` | `coq/SpreadRestrictions.v` | The same inside the sunflower-free world, so the recursion cannot be fed a narrower class by insisting its inputs be sunflower-free either |
| `sunflower_free_bounded`, `syd_implies_sunflower_free_bound` | `coq/SpreadRestrictions.v` | **The reduction needs strictly less than it assumes.** Run contrapositively, every family reaching the spread lemma is sunflower-free, so `SpreadBoundsSunflowerFree` — "a sunflower-free `r`-spread `m`-uniform family has at most `r^m` members" — suffices, and it is implied by `SpreadYieldsDisjoint`. That is the weaker interface for a future proof of Rao's Lemma 2. Cost, recorded: it yields the bound rather than the sunflower, so the `UpperBound` form would need decidability of `ContainsKSunflower`, which is not proved here |
| `no_lower_bound_above` | `coq/SpreadRestrictions.v` | The same conclusion in the `LowerBound`-complement form, which is constructive |
| `sunflower_iff_no_point_in_exactly_two` | `coq/SliceRank.v` | **Three sets are a sunflower exactly when no point lies in exactly two of them.** Unconditional, both directions, no hypotheses. This is the form the slice-rank method consumes, and why it reaches `{0,1}^n` at all — the condition is per-coordinate |
| `bounded_ground_set_settles_k3` | `coq/SliceRank.v` | **What the polynomial method is missing, named.** Naslund–Sawin bound a sunflower-free family of subsets of `[n]` by `3(n+1)C^n`, `C < 1.89` — a `constant^n` bound in the **ground set**, where the conjecture needs one in the **uniformity**. Assuming that bound and `GroundBounded c` (extremal `m`-uniform families live on `c·m` points) gives `f(m,3) ≤ (27^(c+1))^m + 1`: the conjecture at `k = 3`. Both are `Prop`s carried as hypotheses, **not axioms**, so the trusted core is unchanged |
| `ns_exponential_is_load_bearing`, `ground_bounded_at_m_2` | `coq/Audit.v` | The cited bound's exponential is not decoration — the linear-in-ground-set form is false, witnessed by `prod_family 2 6` (64 sunflower-free 6-sets on 12 points against 39). And `GroundBounded` is realised at the one exact value known here: `two_triangles` attains `f(2,3) - 1 = 6` on `6 = 3m` points |
| `two_triangles_is_a_link`, `no_spread_bounds_sunflower_free_2_3_2` | `coq/Audit.v` | The link construction evaluated on a family with nothing link-like about it; and the restricted spread hypothesis refuted at `(2,3,2)` by the five-cycle, so weakening it did not make it vacuous |
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
| `f(n, 3) ≳ 10^(n/2) = 3.162...^n` (Abbott–Hanson–Sauer 1972) | `docs/roadmap.md` §5 | **Not proved here.** `coq/DirectSum.v` reaches `6^(n/2) = 2.449...^n` by the direct sum; AHS reach `10^(1/2)` per point by a *substitution* recursion `g(ab) ≥ g(a)·g(b)^a`, which is strictly stronger and is the next target on the lower-bound side. The rate was checked against the recursion (its fixed point is `g(3)^(3/2) = 10^(1/2)` exactly); the base case was not read from the source. |
| `f(n, k) = o(n!)` (Kostochka 1997 refinement) | `docs/proof_strategies.md` | Not verified here. |
| The **spread lemma** at the 2020 parameter `r = Θ(k log(nk))` (ALWZ–Rao–FKNP–BCW) | `coq/ALWZ.v` named axiom + `docs/spread_framework.md` | Not proved in Coq. Rao's encoding proof is elementary (injections + binomial counting, no measure theory) and is the natural next target; everything downstream of it is already proved. |

## Axiom and admit audit

The `make verify` target runs `Print Assumptions` on every closed
theorem above. The expected output is:

```
Closed under the global context.
```

for every theorem in the "Closed" table (157 of them). The current
state of the codebase satisfies this; the only `Axiom` in the entire
Coq development is `ALWZ.Rao20_lemma2`, and it is *not used* by
any closed theorem (confirmed by `Print Assumptions`).

`make verify` additionally runs an `axiom-audit` step that prints the
full assumption set of `ALWZ.sunflower_bound_from_spread_lemma` — the
one theorem that does use the axiom — so the exact statement being
trusted is visible in the build log rather than buried in a source
file. CI gates on both: as many `Closed under the global context`
lines as there are audited theorems — a count the audit list reports
itself, rather than a number duplicated in the workflow — no closed
theorem listing `Axioms:`, and exactly one axiom name under the modern
bound.

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
produced twice. Five further checks target it; the methodology, and
what it does and does not cover, is in [`docs/testing.md`](docs/testing.md).

| Check | Command | What it would catch |
|---|---|---|
| Independent re-check | `make coqchk` | An `Admitted` or a second `Axiom` **anywhere** in the 26 modules, not just among the audited names; reliance on type-in-type, unsafe fixpoints, or assumed positivity |
| Coherence theorems | part of `make verify` | Two definitions that contradict each other; a bound predicate that is not what its name says; an axiom shape that is vacuously true |
| Exhaustive falsification | `make testbed` | A spread hypothesis that is false at small parameters — i.e. stated weaker than the source states it; a link characterisation that disagrees with a brute-force sunflower detector |
| Mutation testing | `make mutants` | A hypothesis in a definition that no theorem is sensitive to |
| Statement baselines | `make statements` | A *statement* that changed — which nothing else here can see, since a weakened theorem still compiles, still reports closed, and still re-typechecks |
| Documentation numbers | `make docnumbers` | A count quoted in `README.md` or `STATUS.md` that no longer matches the list it counts — the same drift one level up. Three were already wrong when the gate was added |

Current mutation results: 42 mutations, all matching the outcome
declared in `tools/mutations.toml` — 40 killed outright, one genuine
survivor (`lowerbound-at-least`: `LowerBound`'s `length F = m` is
documentation, not a constraint, which `Audit.LowerBound_ge_equiv`
proves as a theorem), and one positive control (`canary-alpha-rename`,
an alpha-rename that must survive, so the `survived` path is exercised
on every run whatever the development does).

`make coqchk` re-verifies all 26 modules with Coq's separate kernel
checker and reports the assumptions of the whole library:

```
* Axioms:
    Sunflower.ALWZ.Rao20_lemma2
* Constants/Inductives relying on type-in-type: <none>
* Constants/Inductives relying on unsafe (co)fixpoints: <none>
* Inductives whose positivity is assumed: <none>
```

CI gates on all four lines. This is what makes "zero admits" a claim
about the development rather than about the theorem names the
`Print Assumptions` audit enumerates — an `Admitted` lemma outside
that list passes the audit and fails this census.

### What the thresholds say about the axiom

The empirical spread thresholds from `make testbed`, all of them at or
below the value proved sufficient by
`SpreadReduction.spread_disjoint_above_elementary`, and exactly `k-1`
at uniformity 1. Two properties are asserted as tests rather than only
printed: the refuted `r` form a *prefix* at every grid point
(`the_refuted_set_of_r_is_a_prefix` — nothing forces this, since raising
`r` weakens the spread hypothesis and raises the size threshold at the
same time), and the `k = 2` row at uniformity 3 is decided by the **Fano
plane** missing the size hypothesis by exactly one member
(`the_fano_plane_misses_the_size_hypothesis_by_one`).

Measured off-grid at uniformity 3: `r*(3,3) = 3` for ground sets up to
9, the same as `r*(2,3) = 3`, against an axiom threshold of
`α·k·log₂(km+1)` which is 9 at `(m,k) = (2,3)` and 12 at `(3,3)` even at
`α = 1`. So the growth in `m` that the published `log` predicts is not
visible between uniformity 2 and 3 at `k = 3` — see
[`docs/roadmap.md`](docs/roadmap.md) §3.6 for what that does and does
not establish.

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
