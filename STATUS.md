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
| `both_ground_hypotheses_settle_k3` | `coq/IotaGround.v` | The two hypotheses side by side. Neither implies the other; what separates them is that one has a measurement behind it |
| `the_double_count_is_the_incidence_count`, `the_ground_bound_is_attained` | `coq/Audit.v` | Both sums evaluated on `two_triangles`, where the incidences can be counted by hand (12 each way), and the bound shown to hold *with equality* there — so it is an identity at uniformity 2, not a lazy estimate |
| `the_two_ground_hypotheses_are_both_sufficient`, `the_ground_cap_beats_erdos_rado_at_ten` | `coq/Audit.v` | The pair of sufficient conditions recorded against a named specification, and the new cap checked to be below the bound it is meant to improve |
| `two_triangles_is_a_link`, `no_spread_bounds_sunflower_free_2_3_2` | `coq/Audit.v` | The link construction evaluated on a family with nothing link-like about it; and the restricted spread hypothesis refuted at `(2,3,2)` by the five-cycle, so weakening it did not make it vacuous |
| `compress_to_chain` | `coq/Compression.v` | A left-compressed family contains the whole chain below any member: from `A ∈ F` and `t ∈ A` with `t ≥ m-1`, compression produces `{0,...,m-2} ∪ {t}`. Induction on `Σ x` over the members, which is the potential that makes the compression terminate in the first place |
| `three_chains_are_a_sunflower` | `coq/Compression.v` | Three sets `{0,...,m-2} ∪ {t}` with distinct `t ≥ m-1` are a 3-sunflower with core `{0,...,m-2}`. The obstruction, in one lemma |
| `compressed_lives_on_m_plus_one_points` | `coq/Compression.v` | **A left-compressed 3-sunflower-free `m`-uniform family is supported on `{0,...,m}`.** Not `c·m` points for some constant — `m+1` points, exactly, and with no dependence on the ground set it started on |
| `compressed_bound`, `compressed_bound_is_attained` | `coq/Compression.v` | **Hence it has at most `m+1` members, and `m+1` is attained.** Against `g(b) ≥ 2·ι(b)`, which is exponential: compression does not cost a constant here, it collapses the problem from exponential to linear. Every member is an `m`-subset of an `(m+1)`-set, so it is determined by the one point it omits, and that map is injective on a `Distinct` family |
| `compression_would_give_ground_bounded`, `compression_would_settle_k3` | `coq/Compression.v` | **What the shifting method would have bought.** If compression preserved sunflower-freeness, `SliceRank.GroundBounded 2` would follow — on `m+1` points rather than `2m` — and with Naslund–Sawin, the conjecture at `k = 3` with constant `27³`. The implication holds. It is the hypothesis that fails |
| `compression_does_not_preserve_sunflower_freeness`, `compression_would_overfill_the_ground_set` | `coq/Compression.v` | **And it fails, twice over.** `F23.f_2_3_lower` exhibits six 2-uniform sunflower-free sets where compression permits three; and the same refutation drawn through the ground-set half instead, so neither half is carrying the other |
| `shift_family_length`, `shift_family_uniform`, `the_shift_is_the_star`, `shift_may_create_a_sunflower` | `coq/Compression.v` | The controls and the counterexample. The shift keeps the size of the family and of every member — so a shift that lost members would not be what breaks things — and `{0,1}, {0,2}, {1,3}` is sunflower-free while its `(0,1)`-shift is the star `{0,1}, {0,2}, {0,3}`. **Three members**, which with `two_members_cannot_acquire_a_sunflower` is the least a counterexample can have: shifting fails at the first opportunity it is given |
| `compressed_iff_the_shift_does_not_move_it` | `coq/Audit.v` | `LeftCompressed` is stated as a closure property and `shift_family` is the operation; nothing in the kernel forces them to be about the same thing, and the file turns on their agreeing. They do, in both directions, for `i < j` and no wider — an *upward* shift really can move a compressed family |
| `two_triangles_is_not_compressed`, `the_shift_really_moves_two_triangles` | `coq/Audit.v` | The negative statement with a positive witness behind it: `two_triangles` attains `f(2,3)-1 = 6` so `compressed_bound` says it cannot be compressed, and the `(0,3)`-shift that moves it is exhibited |
| `the_chain_obstruction_is_real`, `compression_collapses_the_problem` | `coq/Audit.v` | The abstract obstruction evaluated — at `m = 3` it is `{0,1,2}, {0,1,3}, {0,1,4}`, and the reflective detector agrees — and the collapse in numbers: 3 against 6 at uniformity 2, 4 against 20 at uniformity 3 |
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

for every theorem in the "Closed" table (225 of them). The current
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
| Independent re-check | `make coqchk` | An `Admitted` or a second `Axiom` **anywhere** in the 29 modules, not just among the audited names; reliance on type-in-type, unsafe fixpoints, or assumed positivity |
| Coherence theorems | part of `make verify` | Two definitions that contradict each other; a bound predicate that is not what its name says; an axiom shape that is vacuously true |
| Exhaustive falsification | `make testbed` | A spread hypothesis that is false at small parameters — i.e. stated weaker than the source states it; a link characterisation that disagrees with a brute-force sunflower detector; a step of the `ι`/`g` sandwich that fails on some family the argument did not have in mind; a ground-set row that moves where the hypothesis needs it flat |
| Mutation testing | `make mutants` | A hypothesis in a definition that no theorem is sensitive to |
| Statement baselines | `make statements` | A *statement* that changed — which nothing else here can see, since a weakened theorem still compiles, still reports closed, and still re-typechecks |
| Documentation numbers | `make docnumbers` | A count quoted in `README.md` or `STATUS.md` that no longer matches the list it counts — the same drift one level up. Three were already wrong when the gate was added |

Current mutation results: 53 mutations, all matching the outcome
declared in `tools/mutations.toml` — 51 killed outright, one genuine
survivor (`lowerbound-at-least`: `LowerBound`'s `length F = m` is
documentation, not a constraint, which `Audit.LowerBound_ge_equiv`
proves as a theorem), and one positive control (`canary-alpha-rename`,
an alpha-rename that must survive, so the `survived` path is exercised
on every run whatever the development does).

`make coqchk` re-verifies all 29 modules with Coq's separate kernel
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
