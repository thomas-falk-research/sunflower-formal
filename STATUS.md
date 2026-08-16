# Per-Theorem Proof Status

Run `make verify` for the live audit. Below is the static state of
the development. Definition-level testing — the checks the kernel
cannot make — is described in [`docs/testing.md`](docs/testing.md);
what to work on next is in [`docs/roadmap.md`](docs/roadmap.md), whose
**§32 is the current handover** and the right place to start cold.

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
| `pigeonhole_family` | `coq/Pigeonhole.v` | Counting lemma: if every set in `F` meets `X` and `\|F\| > \|X\|·K` then some `x ∈ X` is in `> K` sets |
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
| `intersecting_link_bound`, `iota_three_at_most_eighteen` | `coq/Intersecting.v` | **`ι(b) ≤ b·g(b-1)`** — the one thing proved about `ι` in the upward direction, everything else about it being measured. Every member of an intersecting family meets a fixed member, which has only `b` points, so some point lies in at least `\|F\|/b` members; the link there is sunflower-free of uniformity `b-1`. With the proved `g(2) = 6` this gives `ι(3) ≤ 18` against the measured 10 — loose, and recorded as loose, but it is what makes the search's answers checkable rather than merely reported |
| `intersecting_is_needed_in_the_doubling` | `coq/Audit.v` | **The hypothesis is the theorem.** `{0}, {1}` is sunflower-free because it has two members, is not intersecting, and its doubling is four singletons — any three pairwise disjoint, so a 3-sunflower |
| `sunflower_free_star_bound` | `coq/Intersecting.v` | **`g(b) ≤ 2b·ι(b)`** — the converse of the doubling. A sunflower-free family has no three pairwise disjoint members, so a *maximal* disjoint subfamily has at most two and spans at most `2b` points; maximality makes that set meet every member; pigeonhole gives a point in at least `\|F\|/(2b)` of them; and the star at that point is `b`-uniform, distinct, sunflower-free and — for the silliest reason, every member contains the point — **intersecting**. So it is an `ι` witness |
| `star_Intersecting`, `star_no_sunflower` | `coq/Intersecting.v` | The two properties of the star the bound rests on. Intersecting-ness needs no hypothesis at all; sunflower-freeness is inherited from any superfamily |
| `sunflower3b_complete`, `contains_3_sunflower_dec` | `coq/F23.v` | **`ContainsKSunflower 3` is decidable.** Not obvious from the definition, which quantifies over *arbitrary* lists of sets that happen to be set-equal to members — an infinite search space. `sunflower3b_sound` (already proved) collapses it via `contains_sunflower_literal`; the converse here is immediate, and together they decide. `upper_bound_of_sunflower_free_bound` is what consumes it: any bound on sunflower-free families becomes an `UpperBound`. This closes the cost recorded in `SpreadRestrictions.v` at `k = 3` |
| `iota_le_g`, `g_le_iota_scaled`, `iota_g_sandwich` | `coq/IotaRate.v` | **`2·ι(b) ≤ g(b) ≤ 2b·ι(b)`.** The two extremal quantities are within a factor `b` of each other. `IotaAtMost b N` reads "ι(b) ≤ N" and `GAtMost b M` reads "g(b) ≤ M"; neither `g` nor `ι` is a function here, since neither is known |
| `every_construction_is_within_2b_of_iota` | `coq/IotaRate.v` | Any sunflower-free family at uniformity `b`, **however built**, has at most `2b·ι(b)` members. So the Abbott–Hanson–Sauer substitution is not competing with other constructions — it is within a subexponential factor of the extremal function itself, and no variant of it beats computing `ι` for larger `b` |
| `two_b_le_pow_two`, `scaled_power_absorbs` | `coq/IotaRate.v` | `2b ≤ 2^b` and hence `2b·C^b ≤ (2C)^b` — the step where the sandwich's factor disappears into the base, which is the whole reason it says anything about rates |
| `iota_exponential_iff` | `coq/IotaRate.v` | **`ι` and `g` have the same exponential rate**: `∃C ∀b, ι(b) ≤ C^b` iff `∃c ∀b, g(b) ≤ c^b`, with `c = 2C`. Finitistic — no limit is taken, and none is needed |
| `conjecture_k_3_iff_iota_exponential` | `coq/IotaRate.v` | **The sunflower conjecture at `k = 3` is *equivalent* to `ι(b) ≤ C^b`.** An equivalence, not a sufficient condition: Erdős's $1000 case is exactly an exponential bound on *intersecting* sunflower-free families. Unconditional — the direction back to `UpperBound` uses `contains_3_sunflower_dec` |
| `conjecture_k_3_iff_g_exponential`, `iota_bound_settles_k_3` | `coq/IotaRate.v` | The same through `g`, and the forward direction with the constant visible: `ι(b) ≤ C^b` settles `k = 3` with `c(3) = 2C` |
| `g_three_at_most_108`, `iota_three_sandwich` | `coq/IotaRate.v` | The sandwich at the one uniformity where both ends are known: `20 ≤ g(3) ≤ 108` with what is proved, `≤ 60` with the measured `ι(3) = 10`. **Neither improves on Erdős–Rado's 48** — recorded as such. The content is structural, not numerical |
| `star_correct`, `star_and_link_agree` | `coq/Audit.v` | `star x F` is the members through `x`, and it has the same size as `link [x] F`. The two bounds on `ι` go opposite ways and count opposite devices — the upper one counts links, the lower one stars — so if the counts disagreed one theorem would be about a quantity nobody named |
| `the_factor_two_b_is_attained`, `iota_one_is_one` | `coq/Audit.v` | **The factor `2b` is not slack.** At `b = 1`, `g(1) = 2` and `ι(1) = 1`, so the bound holds with equality and `GAtMost 1 1` is refuted. Above `b = 1` it is loose: the exhaustive sample in `rust/tests/iota_sandwich.rs` reaches 3 of the available 4 at `b = 2` and 2.75 of 6 at `b = 3` |
| `positive_uniformity_is_needed_in_the_star_bound`, `iota_zero_is_zero` | `coq/Audit.v` | **`1 ≤ b` is the theorem.** At `b = 0` the family `{∅}` is 0-uniform, distinct and sunflower-free with one member, while *no* 0-uniform family is intersecting — `∅` is disjoint from itself — so `ι(0) = 0` and the bound would read `1 ≤ 0`. The mechanism is exactly the step the hypothesis licenses: the greedy disjoint cover never starts |
| `iota_three_between_ten_and_eighteen` | `coq/Audit.v` | `~ IotaAtMost 3 9` and `IotaAtMost 3 18`: the truth boundary is trapped in `[10, 18]` by the kernel, and the measured value 10 sits at its lower end. A definition that was accidentally vacuous would fail the first half |
| `bounds_coherent_star_bound`, `the_detector_decides` | `coq/Audit.v` | The new upper bound applied to every lower bound the development proves at uniformity 3, so a contradictory pair would be a proof of `False`; and the decision procedure evaluated on a family with a sunflower and on `two_triangles`, which must not have one |
| `lower_bound_3_3_14`, `no_upper_bound_3_3_14` | `coq/SliceRank.v` | **`f(3,3) ≥ 15`** — a 14-member 3-uniform family on nine points, the exhaustive maximum `N(3,9)` found by `rust/examples/ground_scan.rs` and re-checked here by the reflective detector, so the Coq side takes nothing from the search. Beats the direct sum's 13 at the same uniformity. It does *not* improve the rate: `14^(1/3) = 2.41` is below `6^(1/2) = 2.449` |
| `every_uniform_family_is_a_link`, `link_restriction_is_vacuous` | `coq/SpreadRestrictions.v` | **The class of iterated links is every uniform family.** For any uniform distinct `G` and any `d`, glueing `d` fresh points onto every member gives a uniform distinct `F` of uniformity `d + j` with `link Y F = G` *literally*. So a spread lemma restricted to the families the recursion produces implies the unrestricted one — the restriction restricts nothing, and the "characterise the class of iterated links" direction is closed with a theorem |
| `every_sunflower_free_family_is_a_link` | `coq/SpreadRestrictions.v` | The same inside the sunflower-free world, so the recursion cannot be fed a narrower class by insisting its inputs be sunflower-free either |
| `sunflower_free_bounded`, `syd_implies_sunflower_free_bound` | `coq/SpreadRestrictions.v` | **The reduction needs strictly less than it assumes.** Run contrapositively, every family reaching the spread lemma is sunflower-free, so `SpreadBoundsSunflowerFree` — "a sunflower-free `r`-spread `m`-uniform family has at most `r^m` members" — suffices, and it is implied by `SpreadYieldsDisjoint`. That is the weaker interface for a future proof of Rao's Lemma 2. Cost, recorded: it yields the bound rather than the sunflower, so the `UpperBound` form would need decidability of `ContainsKSunflower`, which is not proved here |
| `no_lower_bound_above` | `coq/SpreadRestrictions.v` | The same conclusion in the `LowerBound`-complement form, which is constructive |
| `sunflower_iff_no_point_in_exactly_two` | `coq/SliceRank.v` | **Three sets are a sunflower exactly when no point lies in exactly two of them.** Unconditional, both directions, no hypotheses. This is the form the slice-rank method consumes, and why it reaches `{0,1}^n` at all — the condition is per-coordinate |
| `bounded_ground_set_settles_k3` | `coq/SliceRank.v` | **What the polynomial method is missing, named.** Naslund–Sawin bound a sunflower-free family of subsets of `[n]` by `3(n+1)C^n`, `C < 1.89` — a `constant^n` bound in the **ground set**, where the conjecture needs one in the **uniformity**. Assuming that bound and `GroundBounded c` (extremal `m`-uniform families live on `c·m` points) gives `f(m,3) ≤ (27^(c+1))^m + 1`: the conjecture at `k = 3`. Both are `Prop`s carried as hypotheses, **not axioms**, so the trusted core is unchanged |
| `ns_exponential_is_load_bearing`, `ground_bounded_at_m_2` | `coq/Audit.v` | The cited bound's exponential is not decoration — the linear-in-ground-set form is false, witnessed by `prod_family 2 6` (64 sunflower-free 6-sets on 12 points against 39). And `GroundBounded` is realised at the one exact value known here: `two_triangles` attains `f(2,3) - 1 = 6` on `6 = 3m` points |
| `ns_bound_to_exponential` | `coq/SliceRank.v` | The arithmetic on its own: a sunflower-free family on at most `c·m` points has at most `(27^(c+1))^m` members. Extracted because two different ground-set hypotheses feed the same computation |
| `degsum_eq_sizesum`, `sizesum_uniform`, `degsum_le` | `coq/IotaGround.v` | Double counting the incidences between a ground set and a family — down the columns (degrees) and along the rows (sizes). The identity itself has **no hypotheses**; they enter only when the two sides are evaluated |
| `link_degree_ground_bound` | `coq/IotaGround.v` | **`b·\|F\| ≤ \|U\|·N(b-1,\|U\|-1)`** for every sunflower-free `b`-uniform family on `U` — no intersecting hypothesis, no positivity hypothesis. Each point's column is a link, hence a smaller sunflower-free family. Complements `intersecting_link_bound`, which counts over *one member's* `b` points and needs intersecting-ness to know every member is there; this one counts over the whole ground set and says something when that set is small. Met with **equality** at `(b,g) = (2,3), (3,6), (4,8), (4,9)`, which forces those extremal families to be regular — and they are (`rust/tests/iota_ground.rs`) |
| `three_uniform_ground_bound`, `n_three_ten_at_most_twenty` | `coq/IotaGround.v` | Unconditionally, with the proved `g(2) = 6`: **`N(3,g) ≤ 2g`**, so `N(3,10) ≤ 20` — the first proved cap on the row `SliceRank.v` names as the one that matters, against `C(10,3) = 120` and Erdős–Rado's 48. It does not decide whether the row plateaus |
| `iota_ground_bounded_settles_k3` | `coq/IotaGround.v` | **`IotaGroundBounded c` + Naslund–Sawin ⟹ the sunflower conjecture at `k = 3`.** The same shape as `bounded_ground_set_settles_k3`, with the ground-set hypothesis pointed at *intersecting* families — which by `IotaRate` is an equivalent problem, and where the measurement is not ambiguous: `N(3,g)` climbs 10, 12, 12, 14 while `ι(3,g)` is flat at 10 from six points to fourteen, every entry exhaustive |
| `iota_ground_bounded_gives_exponential`, `iota_ground_bounded_excludes_lower_bounds` | `coq/IotaGround.v` | The intermediate form (`IotaAtMost b ((27^(c+1))^b)`) and the `LowerBound`-complement form, which is what a search would contradict |
| `ground10_max_no_sunflower`, `n_three_ten_between_sixteen_and_twenty`, `the_general_row_climbs_from_nine_to_ten` | `coq/IotaGround.v` | **`16 ≤ N(3,10) ≤ 20`, both ends proved.** The value `SliceRank.v` names as the one the general row turns on, which the branch-and-bound never decided. The lower end is a sixteen-member family on ten points found by the SAT encoding in `rust/src/sat.rs` in 0.02 seconds and re-verified independently before it was written down; the upper end is `n_three_ten_at_most_twenty`. Its shape reads: all four triples of `{0,1,2,3}` — which is exactly `Compression.compressed_bound`'s extremal family at `m = 3` — plus the pairs from `{0,1}` on a triangle over `{4,5,6}` and the pairs from `{2,3}` on a triangle over `{7,8,9}`. So the general row is **still climbing at ten points**: 14 at nine, at least 16 at ten |
| `grounded_family_at_most_two_to_the_ground`, `ground_bounded_settles_k3_by_counting`, `iota_ground_bounded_settles_k3_without_the_axiom` | `coq/IotaGround.v` | **The polynomial method was never the load-bearing part.** `SliceRank.bounded_ground_set_settles_k3` derives the conjecture from `GroundBounded c` *plus* `NaslundSawinBound`; the axiom is not needed. A family of distinct subsets of a `g`-point set has at most `2^g` members by counting (via `HallCore.sublists`, already in the repo), so a ground set of size `c·m` gives `(2^c)^m` — smaller than the `(27^(c+1))^m` the Naslund–Sawin route gives, for every `c`, and closed under the global context. What [NaSa17] contributes is the constant, `1.89^g` against `2^g`. Found by chasing Hunter's equivalence in [FPPTZ24] |
| `tree_paths_three_needs_fourteen`, `the_universal_ground_reading_is_false` | `coq/IotaGround.v` | **How `GroundBounded` must be read.** [FPPTZ24] gives `g_v(k) ≥ 2^k − 1` — root-to-leaf paths of a depth-`k` binary tree, as edge sets, are `k`-uniform, `2^k` in number and sunflower-free — so the *universal* reading, "every sunflower-free `m`-uniform family lives on `O(m)` points", is false for every `c`. Only the existence reading the definition actually has survives. The `k = 3` instance is eight triples that genuinely need fourteen points against `4·3 = 12`; `rust/tests/ground_set.rs` checks the construction to `k = 6`. It does not conflict with the `N(m,g)` table, which measures the largest family *on* `g` points |
| `ground_bounded_needs_c_at_least_four`, `ground_bounded_three_is_false` | `coq/IotaGround.v` | **The constant in `GroundBounded` is at least 4, proved.** The development knows a twenty-member 3-uniform sunflower-free family (`Intersecting.lower_bound_3_3_20`) and knows `N(3,g) ≤ 2g` outright, so twenty members on `3c` points forces `20 ≤ 6c`. §7's measurement that the `m = 3` row is "still climbing at `g = 3m`" with the search taken out of it — and stronger, because the search never decided `N(3,10)`. It does not refute the hypothesis: `c = 4` is untouched and still settles `k = 3`. What it removes is the reading of the two plateaus at `2m` and `3m` as evidence for a small `c` |
| `both_ground_hypotheses_settle_k3` | `coq/IotaGround.v` | The two hypotheses side by side. Neither implies the other; what separates them is that one has a measurement behind it |
| `the_double_count_is_the_incidence_count`, `the_ground_bound_is_attained` | `coq/Audit.v` | Both sums evaluated on `two_triangles`, where the incidences can be counted by hand (12 each way), and the bound shown to hold *with equality* there — so it is an identity at uniformity 2, not a lazy estimate |
| `the_two_ground_hypotheses_are_both_sufficient`, `the_ground_cap_beats_erdos_rado_at_ten` | `coq/Audit.v` | The pair of sufficient conditions recorded against a named specification, and the new cap checked to be below the bound it is meant to improve |
| `two_triangles_is_a_link`, `no_spread_bounds_sunflower_free_2_3_2` | `coq/Audit.v` | The link construction evaluated on a family with nothing link-like about it; and the restricted spread hypothesis refuted at `(2,3,2)` by the five-cycle, so weakening it did not make it vacuous |
| `compress_to_chain` | `coq/Compression.v` | A left-compressed family contains the whole chain below any member: from `A ∈ F` and `t ∈ A` with `t ≥ m-1`, compression produces `{0,...,m-2} ∪ {t}`. Induction on `Σ x` over the members, which is the potential that makes the compression terminate in the first place |
| `three_chains_are_a_sunflower` | `coq/Compression.v` | Three sets `{0,...,m-2} ∪ {t}` with distinct `t ≥ m-1` are a 3-sunflower with core `{0,...,m-2}`. The obstruction, in one lemma |
| `shift_preserves_no_k_disjoint`, `link_nil`, `shift_preserves_the_empty_core` | `coq/Compression.v` | **Shifting does not increase the matching number** — the classical fact, proved here because it is the *positive* half of the diagnosis and nothing in the development had it. The repair: at most one member of a pairwise-disjoint family can acquire `i`, so at most one moved; send it back to its preimage, and if some other member carries `j`, send that one forward to the image the shift's guard promised was already present. With `link [] F = F` this says compression preserves the **empty-core** instance of `LinkCharacterisation.sunflower_iff_link_matching` |
| `intersecting_is_the_empty_core_at_two`, `shifting_breaks_a_non_empty_core`, `only_the_empty_core_survives_compression` | `coq/Compression.v` | **The diagnosis, as a theorem.** Sunflower-freeness is one condition per core. Compression commutes with the one at the empty core; Erdős–Ko–Rado's hypothesis *is* that condition at `k = 2`; and at a non-empty core it fails — the three-member witness shifts to a family that has a 3-sunflower and **no** three pairwise disjoint members, so what it acquired has a non-empty core. `compressed_bound` prices the rest. That is why the instrument works for EKR and cannot work here, and why a *canonical-form* symmetry break is unavailable while an *orbit* one is not |
| `chain_step`, `chain_down`, `chains_length`, `chains_sunflower` | `coq/Compression.v` | The chain machinery at every sunflower size: a compressed family that contains `{0,…,m-2} ∪ {t}` contains the whole chain below it, and `k` of those are a `k`-sunflower with core `{0,…,m-2}` |
| `compressed_lives_on_m_plus_k_minus_two_points`, `compressed_ground_at_three` | `coq/Compression.v` | **Nothing about the compression bound is special to 3.** A left-compressed `k`-sunflower-free `m`-uniform family is supported on `m + k - 2` points, hence has at most `C(m+k-2, m)` members — **polynomial in `m` of degree `k-2`** — and all `m`-subsets of an `(m+k-2)`-set attain it. Against [Mis26] (arXiv:2606.02667, June 2026), which proves the Erdős–Rado conjecture for shifted families with the *exponential* `s^(2s-2)·2^k` and no lower bound: the shifted sunflower number is `f'(k,s) = C(k+s-2,k)`, exactly. The ground-set half is the theorem; the count and attainment are exhaustive over 62 parameter points in `rust/tests/shifting.rs`. The `k = 3` case is checked to agree with the specialised statement rather than asserted to |
| `compressed_lives_on_m_plus_one_points` | `coq/Compression.v` | **A left-compressed 3-sunflower-free `m`-uniform family is supported on `{0,...,m}`.** Not `c·m` points for some constant — `m+1` points, exactly, and with no dependence on the ground set it started on |
| `compressed_bound`, `compressed_bound_is_attained` | `coq/Compression.v` | **Hence it has at most `m+1` members, and `m+1` is attained.** Against `g(b) ≥ 2·ι(b)`, which is exponential: compression does not cost a constant here, it collapses the problem from exponential to linear. Every member is an `m`-subset of an `(m+1)`-set, so it is determined by the one point it omits, and that map is injective on a `Distinct` family |
| `compression_would_give_ground_bounded`, `compression_would_settle_k3` | `coq/Compression.v` | **What the shifting method would have bought.** If compression preserved sunflower-freeness, `SliceRank.GroundBounded 2` would follow — on `m+1` points rather than `2m` — and with Naslund–Sawin, the conjecture at `k = 3` with constant `27³`. The implication holds. It is the hypothesis that fails |
| `compression_does_not_preserve_sunflower_freeness`, `compression_would_overfill_the_ground_set` | `coq/Compression.v` | **And it fails, twice over.** `F23.f_2_3_lower` exhibits six 2-uniform sunflower-free sets where compression permits three; and the same refutation drawn through the ground-set half instead, so neither half is carrying the other |
| `shift_family_length`, `shift_family_uniform`, `the_shift_is_the_star`, `shift_may_create_a_sunflower` | `coq/Compression.v` | The controls and the counterexample. The shift keeps the size of the family and of every member — so a shift that lost members would not be what breaks things — and `{0,1}, {0,2}, {1,3}` is sunflower-free while its `(0,1)`-shift is the star `{0,1}, {0,2}, {0,3}`. **Three members**, which with `two_members_cannot_acquire_a_sunflower` is the least a counterexample can have: shifting fails at the first opportunity it is given |
| `compressed_iff_the_shift_does_not_move_it` | `coq/Audit.v` | `LeftCompressed` is stated as a closure property and `shift_family` is the operation; nothing in the kernel forces them to be about the same thing, and the file turns on their agreeing. They do, in both directions, for `i < j` and no wider — an *upward* shift really can move a compressed family |
| `two_triangles_is_not_compressed`, `the_shift_really_moves_two_triangles` | `coq/Audit.v` | The negative statement with a positive witness behind it: `two_triangles` attains `f(2,3)-1 = 6` so `compressed_bound` says it cannot be compressed, and the `(0,3)`-shift that moves it is exhibited |
| `the_chain_obstruction_is_real`, `compression_collapses_the_problem` | `coq/Audit.v` | The abstract obstruction evaluated — at `m = 3` it is `{0,1,2}, {0,1,3}, {0,1,4}`, and the reflective detector agrees — and the collapse in numbers: 3 against 6 at uniformity 2, 4 against 20 at uniformity 3 |
| `iota_supermultiplicative`, `sum_family_Intersecting` | `coq/Product.v` | **`ι(a+b) ≥ ι(a)·ι(b)`.** The direct sum of two intersecting families on disjoint ground sets is intersecting — two members meet in their first halves — so `DirectSum.sum_family_no_sunflower` applies unchanged. Only the *first* family need be intersecting, for the same reason only the first need be uniform there. By Fekete this makes `ι(b)^(1/b)` increase to `L = sup_b ι(b)^(1/b)`, and **the conjecture at `k = 3` is exactly `L < ∞`** |
| `IotaAtLeast_antitone`, `iota_at_least_le_at_most` | `coq/Product.v` | `IotaAtLeast` is `IotaRate.IotaAtMost`'s complement, and is downward closed: from a family of exactly `N` members, its first `N'` are one of exactly `N'`, because uniformity, distinctness, **intersecting-ness** and sunflower-freeness all pass to subfamilies. That is what lets every proof here *trim* a family rather than assume one |
| `IotaSubMultiplicative`, `IotaStepBounded`, `step_bounded_settles_k3`, `submultiplicative_settles_k3` | `coq/Product.v` | **Two sufficient conditions for Erdős's \$1000 case, each with an explicit constant.** `ι(a+b) ≤ D·ι(a)·ι(b)` implies `ι(b+1) ≤ D·ι(b)` (take `a = 1`, where `iota_one_at_most_one` gives `ι(1) = 1`), which implies `ι(b) ≤ D^(b-1)` and hence the conjecture with `c(3) = 2(D+1)`. **The second is one bounded ratio**: the whole of `k = 3` follows from `ι(b+1)/ι(b)` being bounded |
| `step_bounded_needs_D_at_least_three`, `iota_two_at_most_four`, `g_one_at_most_two` | `coq/Product.v` | **The constant is at least 3, proved.** `f(1,3) = 3` gives `g(1) = 2`, hence `ι(2) ≤ 4` through `intersecting_link_bound`; against the witnessed `ι(3) ≥ 10` that forces `10 ≤ 4D`. The same shape as `IotaGround.ground_bounded_needs_c_at_least_four`: the hypothesis is not vacuous and the data already moves its constant |
| `cone_Uniform`, `cone_Distinct`, `cone_Intersecting`, `cone_no_sunflower`, `iota_at_least_g_pred` | `coq/Product.v` | **`g(b-1) ≤ ι(b)`** — the cone. Add one fresh point to every member: three members `A_i ∪ {p}` have pairwise intersections `(A_i ∩ A_j) ∪ {p}`, all equal exactly when the `A_i ∩ A_j` are. Intersecting-ness comes with **no hypothesis at all**. Against `Intersecting.intersecting_link_bound`'s `ι(b) ≤ b·g(b-1)` this is a second sandwich, in the uniformity rather than the size (`iota_g_sandwich_shifted`). Elementary and surely folklore; what is new is what follows |
| `iota_bound_bounds_g`, `iota_four_at_most_27_would_beat_erdos_rado` | `coq/Product.v` | **An upper bound on `ι` is an upper bound on `g` one uniformity down**, and hence a *hardness* statement about the `docs/roadmap.md` §7 ladder: a proof of `ι(4) ≤ 27` gives `f(3,3) ≤ 28`, where Erdős–Rado gives 49 and the best lower bound here is 21. Two independent searches failed to decide `ι(4,10)`; this says why, and that a bigger budget is the wrong response |
| `ground_bounded_implies_iota_ground_bounded`, `iota_ground_bounded_bounds_the_general_row`, `the_two_ground_hypotheses_are_not_independent` | `coq/Product.v` | **`IotaGround.both_ground_hypotheses_settle_k3`'s "neither implies the other" is wrong, and withdrawn.** One direction is immediate — `IotaGroundBounded`'s existential does not ask its witness to be intersecting or even uniform. The cone gives the other with the uniformity shifted by one, so `IotaGroundBounded c` alone bounds the *general* row by `(2^c)^(m+1)` by counting. The flat `ι(3,g)` row and the still-climbing `N(3,g)` row are the same question at two uniformities |
| `the_universal_iota_ground_reading_is_false` | `coq/Product.v` | **And the universal reading of `IotaGroundBounded` is false too.** `coq/IotaGround.v` said "the data says the extremal intersecting sunflower-free family literally lives on `O(b)` points"; coning [FPPTZ24]'s tree-path family — the apex is the stem edge above the root, which is exactly what paths through different children were missing — gives an intersecting `b`-uniform sunflower-free family with `2^(b-1)` members on `2^b − 1` points, all used. The `b = 4` instance is eight 4-sets that genuinely need fifteen points; `rust/tests/iota_structure.rs` checks the construction to `b = 7` |
| `pure_link_intersecting`, `cover_recursion` | `coq/PureLink.v` | **The pure link is intersecting.** In Erdős–Rado's step, the members meeting the maximal-matching cover `T` at exactly one point `x` — with `x` removed — pairwise intersect: two disjoint ones plus the matching member through `x` would be three pairwise disjoint sets in the link at `x`, a sunflower with core `{x}`. Double counting over all of `T` rather than at one pigeonhole point gives `2\|F\| ≤ \|T\|·(g(b-1) + ι(b-1))` |
| `g_recursion`, `iota_recursion`, `g_two_at_most_six`, `iota_two_at_most_three` | `coq/PureLink.v` | `g(b) ≤ b(g(b-1)+ι(b-1))` and `2ι(b) ≤ b(g(b-1)+ι(b-1))`, against Erdős–Rado's `g(b) ≤ 2b·g(b-1)`. It **reproduces both values known exactly** — `g(2) = 6` and `ι(2) = 3` — from `g(1) = 2`, `ι(1) = 1`, which is the only check available on it |
| `g_three_at_most_27`, `f_3_3_at_most_28`, `iota_three_at_most_thirteen` | `coq/PureLink.v` | **`f(3,3) ≤ 28`**, unconditionally, where Erdős–Rado gives 49 and `Sharp.sharp_beats_erdos_rado_at_three` reaches 32 only from a hypothesis about uniformity 4. With `Intersecting.lower_bound_3_3_20` the first unknown sunflower number is now `21 ≤ f(3,3) ≤ 28`. The asymptotic content is subsumed by Spencer 1977 (`docs/roadmap.md` §20.3); the finite values are not |
| `g_three_at_most_26`, `f_3_3_at_most_27`, `cover_recursion_sharp` | `coq/PureLink.v` | **`f(3,3) ≤ 27`.** The matching members lie *inside* the cover, so each meets it in all `b` of its points while `cover_recursion` charges it 2 — a surplus of `b-2` apiece, giving `2\|F\| + (b-2)\|M\| ≤ \|T\|·(g(b-1) + ι(b-1))`. Worth one member of `g(3)`, six of `g(4)`, and exactly zero at `b = 2`, where the recursion is already exact — which is the only check available on it. Both ladders are kept rather than one edited |
| `trace_class_intersecting` | `coq/PureLink.v` | `pure_link_intersecting` with the point replaced by a set, **plus the hypothesis its derivation omitted**: the matching member `A0` must *contain* the trace `S`, not merely fail to be contained in it, because all three sets of the sunflower have to live in `link S F`. Automatic at `\|S\| = 1`, false at `\|S\| ≥ 2` for a trace class straddling two matching members. `docs/roadmap.md` §21.4 |
| `alwz42_chain_step`, `link_of_intersecting_not_intersecting`, `chain_never_beats_erdos_rado` | `coq/IntersectingSpread.v` | **What [ALWZ20] Theorem 4.2 buys at `k = 3`: nothing.** Its witness `t` is existential, so a bound must survive `t = 1`; and the link of an intersecting family is not intersecting — the triangle's link at a vertex is two disjoint singletons — so every level re-intersects at a cost of `2(b-t)`, giving `b!(C log b)^b`, *worse* than Erdős–Rado. Independently, 4.2's own proof (p. 13) is a two-line corollary of Theorem 2.5, the spread lemma, so formalising it would consume `Rao20_lemma2` rather than demote it. The 4.2 hypothesis is carried as a premise, so the file adds no axiom. `docs/roadmap.md` §21 |
| `iota_four_at_most_80`, `g_four_at_most_160` | `coq/PureLink.v` | One rung further, where `Audit.the_sharp_bound_narrows_iota_four` had `ι(4) ∈ [27, 192]`. Still short of the `ι(4) ≤ 31` that `Sharp.AHSOptimal` would need |
| `rust/src/symbreak.rs`, `rust/tests/symbreak.rs` | (search, not Coq) | **The `ι(4)` ladder, and §9's named next step built.** Degree-ordered symmetry breaking — the maximum-degree point forced into the anchor at position 0, both blocks sorted by degree, a lexicographic tie-break inside equal-degree runs, exactly `t` members rather than at least, and the sharper floor `deg(0) ≥ max(⌈t/b⌉, ⌈b·t/g⌉)` — plus a ladder in the *support size* and a two-phase cube split that refines a stalled `deg(0)` cube into its exact degree sequences. `iota(4,10) ≥ 32` is UNSAT in **866 s** where the branch-and-bound needed **4437 s** and the previous SAT encoding did not decide it at all. `docs/roadmap.md` §33.4, §33.5 |
| `AbbottGardner1969`, `f_3_3_is_exactly_21`, `gardner_value_is_not_vacuous` | `coq/AbbottGardner.v` | **`f(3,3)` is not an unknown sunflower number, and this repository's own lower bound is the exact answer.** Kostochka's Δ-system survey, p. 4, rendered: *"Abbott and B. Gardner [2] proved in 1969 that `f(3,3) = 20`"* — his `f` is the largest family, so it is this development's `g(3) = 20` and `f(3,3) = 21`. Carried as a `Prop`, not an axiom, exactly as `SliceRank.NaslundSawinBound` is. Two things the kernel checks about it: `~ GAtMost 3 19` (the twenty-member family of `Intersecting.lower_bound_3_3_20` refutes any lower value, so the transcription is pinned from below) and that it is weaker than the proved `g_three_at_most_26`. `docs/reading.md` A9 |
| `iota_four_at_most_65`, `iota_four_at_most_59_if_iota_three_is_ten`, `g_four_at_most_130` | `coq/AbbottGardner.v` | What the 1969 value buys one rung up, through `PureLink.iota_recursion_sharp`: `ι(4) ≤ 65` against the proved 77, and `ι(4) ≤ 59` with the exhaustive `ι(3) = 10`. The conditional interval is `ι(4) ∈ [27, 59]` and **the 31/32 boundary that decides `Sharp.AHSOptimal` is still inside it** |
| `no_three_uniform_sunflower_free_family_has_thirty_two_members`, `the_cone_route_to_iota_four_thirty_two_is_closed` | `coq/AbbottGardner.v` | **`docs/roadmap.md` §13.4's "most concrete thing left on the list" was already dead when it was written.** That route needs a 3-uniform sunflower-free family of 32 members and `PureLink.g_three_at_most_26` says the largest has at most 26 — six short, unconditionally, on every ground set. The 601-second SAT run §13.4 records at `N(3,16) ≥ 30` was asking a question the kernel in the same tree already answers, and with the 1969 value the margin is twelve rather than six |
| `intersecting_support_bound` | `coq/PureLink.v` | **`IotaAtMost` is decided by one finite search.** Every member of an intersecting family meets a fixed member, so contributes at most `b-1` new points: an `n`-member intersecting `b`-uniform family has support `≤ b + (b-1)(n-1)`. At `b = 3`, `n = 11` that is 23 points; `rust/src/wide.rs` finds none there, so **`ι(3) = 10`** where this development had `[10, 18]`. The relabelling onto an initial segment is not formalised and the file says so |
| `link_of_cone`, `only_the_empty_core_is_cheap` | `coq/Product.v` | **The mirror image of `Compression.only_the_empty_core_survives_compression`.** `link [p] (cone p F) = F` **literally**, so the cone *imposes* the `Y = ∅` clause of `LinkCharacterisation.sunflower_iff_link_matching` for free and is the identity on every other clause; shifting preserves that clause and destroys every other. Two unrelated operations, one clause each, and it is the same clause — the one Erdős–Ko–Rado lives at |
| `the_split_fibres_are_not_intersecting`, `the_fibre_bound_is_g_not_iota` | `coq/Product.v` | **Why a splitting argument cannot use the intersecting hypothesis.** The route to submultiplicativity buckets members by their trace on a ground-set part and bounds each fibre. The fibre of a cone over its own trace is the original family: a *general* sunflower-free family of the largest possible size. The smallest instance has fibre `F23.two_triangles`, attaining `g(2) = 6` against `ι(2) = 3`. So the fibres are bounded by `g`, the best a split gives is `ι(b) ≤ (#traces)·g(b−1)`, and that is Erdős–Rado's rate |
| `iota_four_at_least_27`, `lower_bound_4_3_54`, `f_4_3_at_least_55_beats_37` | `coq/Product.v` | **`f(4,3) ≥ 55`**, where `Audit.f_4_3_at_least_37` reached 37. The exhaustive `ι(4,9) = 27` witness transcribed and re-derived by the reflective detector, then doubled. It does **not** improve the rate — `the_rate_at_four_does_not_beat_the_rate_at_three` proves `54^(1/4) < 20^(1/3)` — and `IotaRate.every_construction_is_within_2b_of_iota` is why nothing at a fixed uniformity can. Structurally the witness **is** the Abbott–Hanson–Sauer substitution of the triangle into itself: `\|Aut\| = 1296 = 6·6³` is exactly `Sym(3)` on three triples times `Sym(3)` inside each, cross-checked against `nauty` |
| `not_iota_four_at_most_26`, `iota_four_between_27_and_192` | `coq/Product.v`, `coq/Audit.v` | The truth boundary for `ι(4)` trapped in the kernel, one uniformity above `Audit.iota_three_between_ten_and_eighteen`. The lower end is the witness; the upper end is `intersecting_link_bound` fed Erdős–Rado's `g(3) ≤ 48`. The gap is 27 to 192, and that is the honest state of knowledge |
| `substitution_is_maximal`, `iota3_squared_is_maximal` | `coq/Substitution.v` | **The one piece `docs/roadmap.md` §13.1 named as missing, supplied.** §13.1 measured three independent ways that the pure substitution families admit no extension, and gave the mechanism — the covering number is multiplicative — but only `b = 4` was formalised, by a `2^9` trace certificate. The general theorem: if both seeds are maximal and both have covering number equal to their uniformity, so is the substituted family. `b = 6` (`2^18` sublists) and `b = 9` (`2^36`) are now kernel-checked, in a second, along with every higher level of the tower. **Not** evidence for `Sharp.AHSOptimal`: `maximality_is_not_an_upper_bound` carries the Fano plane beside it |
| `twenty_seven_four_sets_have_no_common_point` | `coq/Support.v` | **The covering number of an extremal `ι(4)` family is at least two, unconditionally.** A family every member of which contains a fixed point *is* its own link at that point, so `PureLink.g_three_at_most_26` caps it at 26 — and 27 is exactly the known lower bound for `ι(4)`, so the statement bites on the extremal object itself. No appeal to the 1969 value; with that value the threshold drops to 21. `rust/tests/support.rs` checks the 27-member witness directly |
| `link_at_pair_bounded`, `pair_counting_ceiling`, `thirty_two_four_sets_need_nine_points` | `coq/Support.v` | **The ground set of a 32-member counterexample has at least nine points, proved rather than searched.** The pair link is `(b−2)`-uniform and sunflower-free, so `deg [x;y] F ≤ g(b−2) = 6`; counting incidences `(A,Q)` with `\|Q\| = 2` in both orders gives `\|F\|·C(b,2) ≤ C(g,2)·g(b−2)`, and at `b = 4` the two sixes cancel. `C(8,2) = 28 < 32 ≤ 36 = C(9,2)`. Two rungs behind the ladder, which refuted `g ≤ 10` — and that gap is asserted in the file. `genprog::least_ground(4,32)` computes the same 9 |
| `two_cover_degree_sum`, `two_cover_of_thirty_two_has_a_star_of_sixteen` | `coq/Support.v` | **What is left of the `ι(4,11)` ladder, made precise.** If two points meet every member then every member lies in one of their two stars, so the degrees sum to at least `\|F\|` — pigeonhole, and the one step of `docs/roadmap.md` §37.5 that was being made in prose. At the ladder's `\|F\| = 32` it forces a star of 16; the ladder has decided every `deg(0)` cube from 15 up UNSAT and `PureLink.link_at_point_bounded` with `g_three_at_most_26` makes 27 and above impossible, so **covering number two is refuted for that rung** and only `τ ≥ 3` survives. That is why `deg(0) = 13` and `14` are the whole of the remaining question. `TwoCover.v` proves far sharper things about `τ ≤ 2`; this is not a competitor to them |
| `anchored_support_bound`, `thirty_two_four_sets_need_at_most_77_points` | `coq/Support.v` | **The standing support bound improved by a fifth: 97 → 77 at `(b,n) = (4,32)`, and 23 → 20 at `(3,11)`.** Two anchors meeting in one point charge each member `b−2` new points instead of `b−1`; the members through the shared point are covered by two members of its link, because three pairwise disjoint ones would be a sunflower. **Not uniformly better** — the difference is `n − (4b−4)`, so below the crossover the single-anchor bound wins, and `below_the_crossover_the_single_anchor_is_better` records a case. `rust/tests/support.rs` rebuilds the core over an exhaustive sweep of 127 466 families and asserts both branches of the case split are exercised. `docs/roadmap.md` §34.4, and §34.5 for what it does **not** buy |
| `palvolgyi_implies_abbott_gardner`, `palvolgyi_at_four_if_iota_four_is_27`, `palvolgyi_refuted_by_one_family` | `coq/Palvolgyi.v` | **The doubling lemma this development proved was stated on a blog in December 2015, and the conjecture beside it was not known here at all.** Dömötör Pálvölgyi, Polymath10 comment 23193 (23 Dec 2015), verbatim: *"If we denote the size of the largest k-uniform intersecting family without an r-sunflower by `f^{int}(k,r)`, then we have `(r-1)·f^{int}(k,r) ≤ f(k,r)`"* — at `r = 3` that is `Intersecting.doubling_lower_bound`. He continues that equality may hold, *"though unlikely"*. Carried as a `Prop`, never an axiom. Three things the kernel checks: it **implies Abbott–Gardner 1969** given the exhaustive `ι(3) = 10`, so it is at least as strong as a theorem; it is pinned from below by an object (`~ GAtMost 3 19`) rather than by a citation; and if the `ι(4)` ladder closes at 27 it says `g(4) = 54` exactly, which is the size of `Product.lower_bound_4_3_54`. A refutation needs `ι(b) ≤ N` and a family of `2N+1` — closed at both decided rungs. `docs/reading.md` A17–A17b, `docs/roadmap.md` §36.4 |
| `cone_needs_freshness`, `bounds_coherent_cone`, `the_cone_route_beats_the_direct_sum_at_four`, `the_ground_hypotheses_are_not_independent_after_all` | `coq/Audit.v` | The coherence theorems for the new definitions: freshness is load-bearing (the triangle coned at one of its own points is not 3-uniform), the new lower bound sits under Erdős–Rado at uniformity 4 so a contradictory pair would be a proof of `False`, 54 beats the direct sum's 36, and the retraction above is recorded against a named specification rather than as an edited comment |
| `iota_exponential_shifted_iff`, `conjecture_k_3_iff_iota_shifted` | `coq/Sharp.v` | **The sunflower conjecture at `k = 3` is exactly `ι(b) ≤ C^(b-1)`.** The exponent `1/(b-1)`, not `1/b`, is the one the Abbott–Hanson–Sauer substitution extracts — the 1972 constant `10^(1/2)` *is* `ι(3)^(1/(3-1))` — so this is the normalisation in which `L = sup_b ι(b)^(1/(b-1))` is the constant of the problem. Both directions are arithmetic on `IotaRate.conjecture_k_3_iff_iota_exponential`, moving the constant by a square one way and by one the other; the only non-arithmetic ingredient is `Product.iota_one_at_most_one`, which is what makes the `b = 1` instance `ι(1) ≤ C⁰ = 1` true. The substitution is **not** needed for the equivalence |
| `AHSOptimal`, `sharp_bounds_iota`, `sharp_gives_base_four` | `coq/Sharp.v` | **The sharp conjecture, named**: `ι(b)² ≤ 10^(b-1)` for every `b ≥ 1` — squared so nothing leaves `nat`. Equivalently `ι(b) ≤ 10^((b-1)/2)`; equivalently Abbott–Hanson–Sauer is optimal and `L = √10`. It gives `ι(b) ≤ 4^(b-1)`, and base 4 rather than 3 is forced: `√10 = 3.162... > 3`, checked in `rust/tests/sharp_conjecture.rs` |
| `sharp_settles_k3`, `sharp_gives_the_constant` | `coq/Sharp.v` | **It implies Erdős's \$1000 case, with `c(3) = 8`.** The real-valued constant the sharp bound gives is `2√10 = 6.32...`; 8 is the price of staying in `nat`, and no attempt is made to sharpen it |
| `sharp_forces_iota_four_at_most_31`, `sharp_beats_erdos_rado_at_three` | `coq/Sharp.v` | **`f(3,3) ≤ 32`**, against Erdős–Rado's 49 and this development's `f(3,3) ≥ 21` — a new bound on the *first unknown sunflower number*, from a hypothesis about uniformity 4. Read as hardness that is why `iota(4,10)` resisted two independent searches; read as a target it says one uniformity is worth a new sunflower number |
| `sharp_forces_iota_three_exactly_ten`, `the_sharp_bound_is_attained_at_three` | `coq/Sharp.v` | The sharp bound pins `ι(3) = 10` exactly, where `Audit.iota_three_between_ten_and_eighteen` has only `[10,18]` — and it is **met with equality there**: `10² = 100 = 10²`. `b = 3` is the only decided uniformity with no slack at all, which is what fixes the constant at `√10` and why one more member there would refute the whole thing |
| `refutation_threshold`, `iota_four_at_least_32_refutes`, `iota_six_at_least_317_refutes` | `coq/Sharp.v` | **One family refutes it**, and the threshold at every uniformity is an integer: 32 at `b = 4`, 317 at `b = 6`. The rungs of the table in `docs/roadmap.md` §12, as corollaries rather than as prose |
| `the_tower_misses_by_exactly_one`, `iota_nine_at_least_10001_refutes` | `coq/Sharp.v` | **The odd tower sits exactly on the bound.** At `b = 2j+1` the sharp bound reads `ι(b) ≤ 10^j` — a round number, and exactly what the substitution delivers when iterated on `ι(3) = 10`. So at `b = 3, 5, 7, 9, …` the record falls at *one more set*, and `b = 9` needs 10001 against the 10,000 the substitution builds. Stated for all `j` rather than at `j = 4` because `nat` is unary and `10001` is past the point where Coq treats a numeral as an ordinary term |
| `the_shifted_bound_at_three_is_false`, `bounds_coherent_sharp`, `the_sharp_bound_narrows_iota_four` | `coq/Audit.v` | **The shift is not a reindexing**: the base-3 shifted bound is refuted outright by the witnessed `ι(3) ≥ 10` against `3² = 9`, while the *unshifted* base-3 bound is not refuted by that family at all (`10 ≤ 27`). So any admissible base in the shifted form is at least 4 — the finitistic content of "`L > 3`". Plus: the sharp bound's `f(3,3) ≤ 32` fed to `lower_lt_upper` against the proved `f(3,3) ≥ 21`, so a contradictory pair would be a proof of `False`; and it narrows `ι(4)` from `[27,192]` to `[27,31]`, so it says strictly more than the kernel already knows |
| `MaximalIntersecting`, `maximal_of_trace_certificate` | `coq/Maximal.v` | **"Can one more set be added?" is a finite question, on every ground set at once.** A candidate interacts with a family only through its *trace* on the support — a point in no member contributes to no intersection — so a `forallb` over `HallCore.sublists U` implies a statement quantified over **every list `A`**, with no ground-set hypothesis in it. Both hypotheses are load-bearing and have mutations: without `Grounded F U` the certificate is about the wrong points, and without the intersecting clause there is no common point to put in the trace |
| `iota4_is_maximal_intersecting`, `iota4_covering_number_is_four` | `coq/Maximal.v` | **The Abbott–Hanson–Sauer family at `b = 4` cannot be extended** — on any ground set, and *without using sunflower-freeness at all*: `τ(ι(4,9)) = 4`, and the only 4-sets meeting every member are the 27 members. Measured first by three independent methods that agree (minimal hitting sets, brute force over every trace, SAT with two solvers required to agree on UNSAT), at `b = 4, 6, 9` and on both cone rows; `b = 9` is the one that matters, where 10,000 members are built and 10,001 would beat 1972. The mechanism is that the covering number is *multiplicative* under the substitution, so maximality is too, and the whole 3-adic tower inherits it |
| `fano_is_maximal_intersecting`, `maximality_is_not_a_size_bound` | `coq/Maximal.v` | **Maximal is not maximum**, and this is the guard against over-reading the row above. The Fano plane is a maximal intersecting 3-uniform family with **seven** members — every 3-set meeting all seven lines *is* a line — while `Intersecting.iota3` has **ten**. So a family nothing can be added to may be strictly smaller than one that exists |
| `regular_intersecting_ground_bound` | `coq/Maximal.v` | **A regular intersecting `b`-uniform family lives on at most `b²` points.** Pigeonhole over one member's `b` points plus the incidence count. It is why prescribing a *transitive* group is hopeless above `g = b²` — every orbit of a transitive group is point-regular — which is the structural reason the Kramer–Mesner instrument does not transfer to a ternary negative condition. It also sharpens `Product.the_universal_iota_ground_reading_is_false`: the coned tree-path family needs `2^b − 1` points, so it **must** be irregular, and it is |
| `star_defect_bound`, `maxdeg_over` | `coq/StarDefect.v` | **Erdős–Rado's first step, with the point named.** `Intersecting.sunflower_free_star_bound` proves it and immediately consumes it; this stops one line earlier and says every sunflower-free `b`-uniform family *has* a point of degree at least `\|F\|/(2b)`. Naming the maximiser is what lets the recursion be run parametrically, and it needs a fold over the cover's points because `pigeonhole_family` produces a point above a given degree rather than the best one |
| `StarBounded`, `star_step`, `star_bounded_gives_explicit_bound` | `coq/StarDefect.v` | **The ratio `ρ(F) = \|F\|/maxdeg(F)` is what the recursion pays**, and the chain telescopes: `\|F\| = ρ₀·ρ₁·…·ρ_{b−1}` *exactly*. So the conjecture at `k = 3` is that the product is `C^b`, and a constant bound on one factor gives `g(b) ≤ c·g(b−1)` hence `g(b) ≤ 2c^(b−1)` |
| `star_bounded_settles_k3`, `star_bounded_gives_the_constant` | `coq/StarDefect.v` | **One inequality with one number in it settles Erdős's \$1000 case**, with `c(3) = 2c`. That is the whole reason the quantity is worth naming |
| `star_defect_is_the_singleton_spread_clause`, `star_bounded_refutes_spread`, `the_two_branches_of_the_dichotomy` | `coq/StarDefect.v` | **The correction, as a theorem.** `ρ` is *not* an unnamed quantity: `Spread.Spread F r` is `∀T, NoDup T → r^\|T\|·deg T F ≤ \|F\|`, and at `T = [x]` that is exactly `ρ(F) ≥ r`. So `ρ` is the singleton clause of **spreadness** — `κ` in [ALWZ20] Def 1.10, which notes it was called *regularity* earlier, and Def 2.5 of [Lovett]'s PCMI notes, both read from rendered pages. Consequences: `star_defect_bound` is the "structured" branch of the classical Erdős–Rado dichotomy ([Lovett] Lemma 2.2, constant `(r−1)n` = `2b` at `r = 3`), and the *other* branch, `SpreadReduction.elementary_spread_disjoint`, was already here at `2b+1` — `the_two_branches_of_the_dichotomy` puts them side by side. `StarBounded c` says no sunflower-free family is `(c+1)`-spread *at singletons*, a non-existence statement where the spread lemma is a size bound, which is why it is so much stronger and why it is false. `docs/roadmap.md` §14.5 withdraws the novelty claim in full |
| `star_bounded_needs_c_at_least_five`, `the_ratio_at_four_is_between_the_witness_and_the_ceiling` | `coq/StarDefect.v` | **And it is not a constant.** `ρ` is exactly multiplicative under the Abbott–Hanson–Sauer substitution — the `\|H\|^(a−1)` in `maxdeg` cancels — so iterating on `ι(3)` gives `ρ = 2^k` at `b = 3^k`, i.e. `ρ = b^{log₃2} = b^{0.63}`, verified directly at `b = 9` where 10,000 members have maximum degree 2500. The measured row 2, 3, 2.75 looked flat only because it stopped at `b = 3`. Formalising the refutation needs `substitute` in Coq; what is proved is that the doubling of `ι(4,9)` forces `c ≥ 5` against the proved ceiling `2b = 8`. What survives is the *geometric mean*, which tends to `√10` while the maximum diverges — so no proof of the conjecture can be a per-level estimate |
| `bounds_coherent_er`, `bounds_coherent_spread`, `bounds_coherent_f_2_3` | `coq/Audit.v` | The development's own lower and upper bounds fit in one order — *derived* from the formal statements, so a contradictory pair would make these proofs of `False` |

### Discharging that axiom: Stage A is done

`docs/roadmap.md` §1 stages the discharge through the *counting* proof
([ALWZ20] §2 as streamlined by Park–Pham, written out in Lovett's PCMI
notes §3) in three stages. **Stage A — the counting layer — is
formalised**, axiom-free, in `coq/Counting.v`: the size-`j` layer of the
powerset with `|subsets_of_size j l| = C(|l|, j)`, a counting operator
with "an injection implies an inequality" and additivity over disjoint
predicates, `C(n,j) <= 2^n`, and the single binomial estimate the proof
needs. `rust/tests/counting.rs` checks every claim against an independent
implementation (the multiplicative formula against Pascal's recursion,
bitmask enumeration against the filtered powerset).

**Stage B's set-theoretic half is formalised too** (`coq/Fragment.v`):
Definition 3.2 with ties broken by position, all three observations,
both parts of Claim 3.3, the encoding `φ(S,V) = (Z,S',M,S\M)` of Claim
3.4, its decoder, and the injectivity the count consumes — plus the two
junctions that make Stage A usable, `|Z| = |V| + |M|` (which is why step
1 of the count is `Counting.binom_ratio`) and `S\M ∈ F_M` (the only
place spreadness enters). `rust/tests/fragment.rs` checked all of it
over 32968 exhaustive `(F,S,V)` triples *before* it was proved. The
count itself is not done — §31.5 names what is missing.

**Claim 3.4 is closed.** `Fragment.claim_3_4_per_m` is the count at a
fixed fragment size — `k^m · |L| ≤ C(N,j+m) · C(n,m) · |F|`, the rendered
page's four steps — and `Fragment.claim_3_4_summed` is the whole of it,
`(ck)^t · Σ|L_m| ≤ 2 · (4d)^t · C(N,j) · |F|`, which read back is
Lovett's `Pr ≤ 100^{-n}` with `q = c/d` and `t = ⌈n/2⌉`. Nothing leaves
`nat`. Getting there needed the canonicalisation layer `Counting.norm`
(§31.9) — built once, as rule 26 asks, after the same obstacle had been
paid for twice at the point of use.

**What remains is Stage C**, untouched: Claim 3.5 (Markov plus the two
spreadness-preservation lemmas), Claim 3.6, and Lemma 3.1's `log n`
iteration. The axiom is still an axiom.

Stage B produced its own correction: **the decode `ψ(φ(S,V)) = (S,V)` is
not an equation.** Its `V` half is literal; its `S` half is only up to
permutation, and closing it needs `Distinct F`, a hypothesis §1's
staging note does not record because at the level of sets it does not
exist. See §31.3.

One correction came out of it: the estimate holds under `c*N <= d*(j+1)`,
one notch weaker than the `c*N <= d*j` that Lovett's `j = qN` supplies,
and `c*N <= d*(j+2)` is **false** — witness `N=1, j=0, c=2, d=1, m=1`.
See §30.2. Stages B (the encoding) and C (the iteration) are untouched;
§1 names Stage B as the stall risk and Stage A did not change that.

## Stated as a named axiom with literature citation (not used by any closed theorem)

| Statement | File | Citation |
|-----------|------|----------|
| `Rao20_lemma2` | `coq/ALWZ.v` | **Rao 2020 (Discrete Analysis 2020:2), Lemma 2**, verbatim from the rendered page 2: *"If a sequence of more than `r(p,k)^k` sets of size `k` is `r(p,k)`-spread, then the sequence must contain `p` disjoint sets"*, with `r(p,k) = α·p·log(pk)` and `r`-spread in Rao's absolute sense (*"for every non-empty set `Z ⊂ [n]`, the number of elements of the sequence that contain `Z` is at most `r^{k−\|Z\|}`"*). Originally Alweiss–Lovett–Wu–Zhang 2020 (Annals 194(3), 2021); refined by FKNP21 / BCW21. |

**The paper was read in full in July 2026** and the axiom was checked
symbol by symbol against it (`docs/reading.md`, register row A1). The
statement is faithful. Two things the header said about the *gap* were
not:

* it claimed the axiom is weaker because *"the source allows sets of size
  at most `m`"*. Rao says "of size `k`" — the "at most" convention is
  [ALWZ20]'s. **Withdrawn.**
* it did not record that the axiom quantifies over **every** `r` above
  the threshold, while Rao fixes one. `SpreadYieldsDisjoint` is not
  monotone in `r` on general grounds, so that was a real extension of the
  published sentence. It is now **derived rather than assumed**:
  `ALWZ.fractional_form_gives_the_axiom_shape` obtains the whole
  quantified family from the *fractional* single-threshold statement
  (Lovett's Lemma 2.9), through `Spread.RaoSpread_Spread` and
  `Spread.Spread_mono`.


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
| `f(n, 3) ≳ 10^(n/2) = 3.162...^n` (Abbott–Hanson–Sauer 1972) | `docs/roadmap.md` §5 | **Not proved here.** `coq/DirectSum.v` reaches `6^(n/2) = 2.449...^n` by the direct sum; AHS reach `10^(1/2)` per point by a *substitution* recursion `g(ab) ≥ g(a)·ι(b)^a`, which is strictly stronger and is the remaining target on the lower-bound side. The recursion and its seed (a 3-uniform family of size 10 with no 3-sunflower) are now **corroborated verbatim against a second source**, Kupavskii's 2025 Δ-system survey — see `docs/references.md` [AHS72]/[Kup25]. The source paper is still unread, and the survey does not state the side condition this repository found by computation: the *inner* family must be intersecting. What `coq/IotaRate.v` now proves is that formalising the substitution cannot improve the rate — `every_construction_is_within_2b_of_iota` caps every construction at `2b·ι(b)` — so it is a completeness target, not a route to a better bound. |
| The rate `ι(b)^(1/(b-1))` is flat: `3.000, 3.162, 3.000, <3.142` | `docs/roadmap.md` §5 | Measured, not proved. `ι(2)=3`, `ι(3)=10`, `ι(4,9)=27`, `ι(4,10)<32`, all exhaustive. By `IotaRate.iota_exponential_iff` this *is* the rate of the problem at `k = 3`, so a flat row is mild evidence for the conjecture there with `c(3)` near 3.2. Four values, two at the same `b`, and no monotonicity is known — weak evidence, and recorded as such. Pinned in `rust/tests/iota_sandwich.rs`. |
| `f(n, k) = o(n!)` (Kostochka 1997 refinement) | `docs/proof_strategies.md` | Not verified here. |
| The **spread lemma** at the 2020 parameter `r = Θ(k log(nk))` (ALWZ–Rao–FKNP–BCW) | `coq/ALWZ.v` named axiom + `docs/spread_framework.md` | Not proved in Coq. Rao's encoding proof is elementary (injections + binomial counting, no measure theory) and is the natural next target; everything downstream of it is already proved. |

## Axiom and admit audit

The `make verify` target runs `Print Assumptions` on every closed
theorem above. The expected output is:

```
Closed under the global context.
```

for every theorem in the "Closed" table (735 of them). The current
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
| Independent re-check | `make coqchk` | An `Admitted` or a second `Axiom` **anywhere** in the 49 modules, not just among the audited names; reliance on type-in-type, unsafe fixpoints, or assumed positivity |
| Coherence theorems | part of `make verify` | Two definitions that contradict each other; a bound predicate that is not what its name says; an axiom shape that is vacuously true |
| Structure of the extremal families | part of `make testbed` | An automorphism group order, design parameter, per-core link matching number or degree sequence that drifted; a closed form for `ι` that the data already refutes being re-proposed; a construction in the extended `ι` table that stopped verifying |
| Exhaustive falsification | `make testbed` | A spread hypothesis that is false at small parameters — i.e. stated weaker than the source states it; a link characterisation that disagrees with a brute-force sunflower detector; a step of the `ι`/`g` sandwich that fails on some family the argument did not have in mind; a ground-set row that moves where the hypothesis needs it flat |
| Mutation testing | `make mutants` | A hypothesis in a definition that no theorem is sensitive to |
| Statement baselines | `make statements` | A *statement* that changed — which nothing else here can see, since a weakened theorem still compiles, still reports closed, and still re-typechecks |
| Documentation numbers | `make docnumbers` | A count quoted in `README.md` or `STATUS.md` that no longer matches the list it counts — the same drift one level up. Three were already wrong when the gate was added |
| Route ceilings | `make ceilings` | A reduction whose declared best case disagrees with its own arithmetic; a route being worked on whose best possible bound loses to Erdős–Rado 1960. Six of the nine routes here do |
| The pull request | `make prcheck` | A write-up whose counts have gone stale, whose cited theorem no longer exists under that name, or that calls a result new without a literature search. It found six unaudited theorems on its first run |

Current mutation results: 164 mutations, all matching the outcome
declared in `tools/mutations.toml` — 161 killed outright, two genuine
survivors (`lowerbound-at-least`: `LowerBound`'s `length F = m` is
documentation, not a constraint, which `Audit.LowerBound_ge_equiv`
proves as a theorem; and `iotaatleast-at-least`, the same question asked of
`Product.IotaAtLeast`, answered the same way by
`Product.IotaAtLeast_antitone`), and one positive control (`canary-alpha-rename`,
an alpha-rename that must survive, so the `survived` path is exercised
on every run whatever the development does).

`make coqchk` re-verifies all 49 modules with Coq's separate kernel
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
not establish. **It does not establish `r*(3,3) = 3`.**
`rstar::min_ground` computes the counting floor
`ceil(m(r^m+1)/r^(m-1))`, which at `(m,r) = (3,3)` is 10: no
counterexample fits on 9 points, so the rows above at grounds 7, 8 and 9
are arithmetic rather than search, and ground 10 — the first that could
hold one — is open. `docs/roadmap.md` §22.2 records this.

### Where a record could live: the counting ceiling

`LinkCharacterisation` says sunflower-free means every link has matching
number at most 2. At a `(b-1)`-set the link is 1-uniform, so its degree
is at most 2; at a `(b-2)`-set it is a graph with `Δ ≤ 2` and `ν ≤ 2`,
hence at most two disjoint triangles, so its degree is at most 6.
Counting members against the subsets they contain turns each into a bound
on `|F|`, and `genprog::size_ceiling` is the smaller:

```
  b = 4    n      8    9   10   11   12   13   14   15
  ceiling        28   36   45   55   66   78   91  105

  b = 5    n     10   11   12   13   14   15
  ceiling        72   99  132  171  218  273
```

So **`iota(5) ≥ 101` is impossible below twelve points** and
`iota(4) ≥ 51` is impossible below eleven — the first statement here
about *where* a record could be rather than how big it would be. It also
says §9's `b = 5` SAT row, run at ground 10 with a ceiling of 72, was
asked at a ground that could not have answered it. At `b = 3` the ceiling
is 10 at six points and `iota(3) = 10` attains it exactly; at `b = 4` the
ceiling is 28 at eight points and an exhaustive search finds nothing
there. See [`docs/roadmap.md`](docs/roadmap.md) §23.

### The threshold sequence `r*(m,3)`

`SpreadYieldsDisjoint n 3 r` is true above `r*(n,3)` and false below it,
`spread_reduction` turns a bound on `r*` into a bound on `f(m,3)`, and
whether the sequence is bounded in `m` **is** the sunflower conjecture at
`k = 3`. `coq/SpreadThreshold.v` proves two upper bounds on it, both
better than the `2n+1` of `elementary_spread_disjoint`, which was the
only one the development had.

| bound | Coq name | value at `n = 4` |
|---|---|---|
| `r*(n,3) ≤ 2n` | `cover_spread_disjoint` | 8 |
| `r*(n,3) ≤ 1 + √(3n²−4n+3)` | `quadratic_spread_disjoint` | **7** |

The second uses the fact that separates the spread route from every
restricted-class route: for `B` **any** member of a family with no three
pairwise disjoint members, `{C ∈ F : C ∩ B = ∅}` is intersecting. So
against a matching the family is two intersecting pieces plus a cross
piece, and the pieces that can be covered by *pairs* are smaller by a
factor of `r`, because a pair has degree `r^(m-2)` where a point has
`r^(m-1)`. Nothing is re-intersected, which is why this argument does not
pay the per-level toll §21.7 closed three other routes for.

```
  m     r*(m,3)          how the ends are known
  1     = 2   exact      r = 1 refuted / cover_spread_disjoint
  2     = 3   exact      r = 2 refuted (C5) / TwoCover.r_star_two_three_at_most_three
  3     in [3, 4]        r = 2 refuted / TauThree.r_star_three_three_at_most_four_unconditional
  4     in [3, 7]        r = 2 refuted / r_star_four_at_most_seven
                         ([3,5] on one constant: docs/roadmap.md §26.4,
                          CrossIntersecting.r_star_four_at_most_five_from_tau_three;
                          that constant is now known to lie in [65, 125] --
                          CrossRefined.tau_three_piece_at_least_sixty_five)
  5     in [3, 8]        r = 2 refuted / r_star_five_at_most_eight
  6     in [3, 10]       r = 2 refuted / r_star_six_at_most_ten
  9     >= 4  COND.     substitution_would_refute_the_flat_threshold_at_nine,
                         conditional on LowerBound 9 3 (3^9+317) -- the
                         Abbott-Hanson-Sauer substitution, not formalised
  10    in [3, 17]       r = 2 refuted / r_star_ten_at_most_seventeen
```

Every row is unconditional except `m = 9`, which is conditional on an
unformalised construction and is now marked so. The `m = 3` upper bound
is the only one that
does not come from a general threshold: it is `I(3,r) = r^2` for `r >= 4`
(`TauThree.three_uniform_star_extremal`, with `TauThree.star34` attaining
it), which is the `m = 3` row of the extremal problem `docs/roadmap.md`
§24.13 names and §25.3 closes. Whether the sequence is bounded is the
sunflower conjecture at `k = 3`, and — per §25.5 — is the open question
Rao states in [Ra20, p. 2]; the literature contains no lower bound on it
at all.

`rust/tests/spread_threshold.rs` pins every entry, including the
counterexample families themselves.

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

### What each route can reach: the ceiling table

Whether `r*(m,3)` is bounded is the conjecture; what a *bound* on it is
worth is arithmetic, and `tools/ceiling.py` does it for every reduction in
the development at once. `spread_reduction` turns `r*(n,3) ≤ h(n)` into
`f(n,3) ≤ h(n)^n + 1`, so every bound here has the shape `base(n)^n` and
the routes compare by their base.

```
  route                                     base(50) base(200)    g  verdict
  elementary cover, r = 2n+1                     101       401 0.99  linear: loses
  greedy cover, r = 2n                           100       400 1.00  linear: loses
  quadratic split, r = 1+sqrt(3n^2-4n+3)          87       347 0.99  linear: loses
  star extremality, pinned at r = n+1             51       201 0.99  linear: loses
  Erdos-Rado profile via the reduction            38       149 0.98  linear: equals
  spread lemma, r ~ 3 log2(3n)                    24        30 0.22  sublinear
  constant threshold (the conjecture)              8         8 0.00  constant
  ---
  Erdos-Rado 1960 (the bar)                       38       149 1.00
  BCW 2021 (the record)                           60        84 0.24
```

`g` is the measured exponent in `base(n) ~ n^g`. **A route needs a
sublinear base to be in the running at all**: `r*(n,3) ≤ c·n` beats
Erdős–Rado exactly when `c < 2/e = 0.7357…`, and every linear route above
has `c ≥ 1`. Each route declares the verdict it expects and a mismatch
fails `make verify`, so a reduction cannot be described as a path to a
record once its own ceiling says otherwise.

Two of those rows are theorems rather than arithmetic.
`Profile.greedy_forces_erdos_rado` proves that **any** profile the greedy
cover step closes satisfies `B m ≥ (k-1)^m·m!` — exactly Erdős–Rado's
bound, at every `k`, with no asymptotics — and
`Profile.erdos_rado_below_the_n_to_the_n_ceiling` proves
`2^n·n! ≤ (n+1)^n` at every `n`, which is the star-extremality route's
ceiling. See [`docs/roadmap.md`](docs/roadmap.md) §29.
