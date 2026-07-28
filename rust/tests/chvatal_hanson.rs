//! Falsification tests for the Chvátal–Hanson identification.
//!
//! `chvatal_hanson.rs` claims that one recalled formula governs two
//! things this repository cares about: the sharp spread threshold at
//! uniformity 2, and the exact sunflower numbers `f(2,k)`. The formula
//! is recalled from the literature and the identification is an
//! argument, so both are checked here the way this repository checks
//! everything it did not prove — by running them against exhaustive
//! enumeration and against numbers measured independently.
//!
//! Six things are checked, in dependency order:
//!
//! 1. **the identification itself** — that `RaoSpread 2 F r` is a
//!    maximum-degree bound. Everything else assumes it;
//! 2. **the upper bound** `CH(D,v)` — no graph over any ground set
//!    tried exceeds it. This is the half of Chvátal–Hanson that is
//!    hard to prove and the half worth falsifying;
//! 3. **the lower bound** — the explicit construction attains it, and
//!    exhaustive search finds nothing better once the ground set is
//!    large enough to hold it;
//! 4. **the spread threshold** `r*(2,k) = min{r : CH(r,k-1) <= r^2}`,
//!    against the thresholds `spread_axiom.rs` measures by search;
//! 5. **the sunflower number** `f(2,k) = CH(k-1,k-1)+1`, against
//!    exhaustive tabulation and against `F23.f_2_3_eq_7`;
//! 6. **the Coq lower bound** — that the two-clique family
//!    `CliqueLowerBound.two_cliques_lower_bound` proves sunflower-free
//!    really is, according to the sunflower detector, and that its
//!    oddness hypothesis is load-bearing.

use sunflower_formal::bounds::f_nk_exact;
use sunflower_formal::chvatal_hanson::{
    ch, extremal, extremal_vertices, f_2_k, max_degree, max_edges, r_star, report, verify_extremal,
};
use sunflower_formal::spread::{
    family_to_coq, is_distinct, is_rao_spread, is_uniform, matching_number, Mask,
};
use sunflower_formal::testbed::{empirical_threshold, for_each_family};

/// `(ground, d, v)` triples for the exhaustive searches. Every entry is
/// a complete search over all graphs on `ground` vertices with the two
/// constraints, so the grid is kept to what runs in seconds in release
/// mode.
const GRID: &[(u32, u64, u64)] = &[
    (6, 1, 1),
    (6, 1, 2),
    (6, 1, 3),
    (6, 2, 1),
    (6, 2, 2),
    (7, 2, 2),
    (8, 2, 2),
    (9, 2, 3),
    (6, 3, 1),
    (6, 3, 2),
    (7, 3, 2),
    (7, 3, 3),
    (8, 3, 3),
    (9, 3, 3),
    (6, 4, 1),
    (7, 4, 2),
    (8, 4, 2),
    (9, 4, 3),
    (7, 5, 2),
    (7, 5, 3),
    // Ground 10. The CH upper bound is the unproved half of the
    // identification, so it is the half most worth widening. Beyond
    // these the exhaustive search stops being affordable in CI: on this
    // machine (10, 4, 3) takes 63s, (11, 3, 3) 85s and (10, 3, 4) 498s,
    // against under a second for the whole grid below ground 9. All
    // three were run once and agree with `ch`; see docs/roadmap.md.
    (10, 2, 3),
    (10, 2, 4),
    (10, 3, 3),
];

// ---------------------------------------------------------------
// 1. The identification: spread at uniformity 2 is a degree bound
// ---------------------------------------------------------------

/// The claim the whole module rests on: for a distinct 2-uniform
/// family, `RaoSpread 2 F r` holds exactly when every vertex has degree
/// at most `r`. The `|T| = 2` clause of the spread condition asks
/// `deg T F <= r^0 = 1`, which distinctness already gives, so nothing
/// but the degree bound survives.
///
/// Checked against `is_rao_spread`, which is the independent Rust
/// reading of `coq/Spread.v` — not against a restatement of the claim.
#[test]
fn rao_spread_at_uniformity_two_is_a_degree_bound() {
    for ground in [4u32, 5, 6] {
        for r in 0..=4u64 {
            for_each_family(ground, 2, |f| {
                // `for_each_family` enumerates subsets of the distinct
                // 2-sets, so uniformity and distinctness are automatic.
                assert!(is_uniform(2, f) && is_distinct(f));
                assert_eq!(
                    is_rao_spread(2, f, r, ground),
                    max_degree(f, ground) as u64 <= r,
                    "spread and degree bound disagree at r = {r} on {}",
                    family_to_coq(f)
                );
            });
        }
    }
}

// ---------------------------------------------------------------
// 2. The upper bound
// ---------------------------------------------------------------

/// No graph on any ground set tried has more than `CH(d, v)` edges.
/// This is the half of Chvátal–Hanson that needs its own campaign to
/// prove, so it is the half most worth trying to break.
#[test]
fn no_graph_exceeds_ch() {
    for &(ground, d, v) in GRID {
        let f = max_edges(ground, d, v);
        assert!(
            f.len() as u64 <= ch(d, v),
            "found {} edges with max degree <= {d} and matching number <= {v} on {ground} \
             vertices, but CH({d}, {v}) = {}: {}",
            f.len(),
            ch(d, v),
            family_to_coq(&f)
        );
    }
}

/// The same bound checked against *every* graph on a small ground set,
/// not only against the maxima the pruned search reports. A search bug
/// that lost branches would hide a violation from the test above.
#[test]
fn no_graph_exceeds_ch_by_brute_force() {
    for ground in [4u32, 5, 6] {
        for_each_family(ground, 2, |f| {
            let d = max_degree(f, ground) as u64;
            let v = matching_number(f) as u64;
            assert!(
                f.len() as u64 <= ch(d, v),
                "{} has {} edges, max degree {d}, matching number {v}, but CH({d}, {v}) = {}",
                family_to_coq(f),
                f.len(),
                ch(d, v)
            );
        });
    }
}

// ---------------------------------------------------------------
// 3. The lower bound
// ---------------------------------------------------------------

/// The construction satisfies both constraints and has exactly
/// `CH(d, v)` edges.
#[test]
fn construction_attains_ch() {
    for d in 1..=7u64 {
        for v in 1..=7u64 {
            if extremal_vertices(d, v) > 32 {
                continue;
            }
            let f = extremal(d, v);
            verify_extremal(&f, d, v)
                .unwrap_or_else(|e| panic!("extremal(d = {d}, v = {v}) is wrong: {e}"));
        }
    }
}

/// Where the ground set is large enough to hold the construction,
/// exhaustive search finds nothing better — so `CH(d, v)` is exact
/// there, not merely an upper bound that happens to hold.
#[test]
fn ch_is_attained_where_the_ground_set_allows_it() {
    let mut checked = 0;
    for &(ground, d, v) in GRID {
        if extremal_vertices(d, v) > ground as u64 {
            continue;
        }
        let f = max_edges(ground, d, v);
        assert_eq!(
            f.len() as u64,
            ch(d, v),
            "exhaustive maximum on {ground} vertices is {} but CH({d}, {v}) = {}",
            f.len(),
            ch(d, v)
        );
        checked += 1;
    }
    assert!(checked >= 10, "only {checked} grid points were conclusive");
}

// ---------------------------------------------------------------
// 4. The spread threshold
// ---------------------------------------------------------------

/// `r*(2,k) = min{r : CH(r, k-1) <= r^2}` against the thresholds
/// `spread_axiom.rs` measures by exhaustive search.
///
/// A ground-set-limited search can only *under*-report the threshold —
/// it may miss the extremal graph that refutes some `r` — so the
/// inequality holds everywhere and equality is asserted only where the
/// witness fits.
#[test]
fn predicted_spread_threshold_matches_the_measured_one() {
    let mut exact = 0;
    for k in 2..=4u64 {
        for ground in 4..=9u32 {
            let (measured, _) = empirical_threshold(ground, 2, k as usize);
            let predicted = r_star(k);
            assert!(
                measured <= predicted,
                "measured threshold {measured} exceeds the predicted {predicted} \
                 at k = {k}, ground = {ground}"
            );
            // Every `r` below the prediction is refuted by the extremal
            // graph at `(r, k-1)`; if all of those fit in the ground
            // set, the search must find them and agree exactly.
            let all_witnesses_fit = (1..predicted)
                .all(|r| extremal_vertices(r, k - 1) <= ground as u64);
            if all_witnesses_fit {
                assert_eq!(
                    measured, predicted,
                    "measured threshold {measured} but predicted {predicted} \
                     at k = {k}, ground = {ground}, where every witness fits"
                );
                exact += 1;
            }
        }
    }
    assert!(exact >= 5, "only {exact} grid points were conclusive");
}

/// The threshold has a closed form: `r*(2,k) = k` for every `k >= 3`.
///
/// Worth stating on its own. The elementary bound the repository does
/// prove — `SpreadReduction.spread_disjoint_above_elementary`, giving
/// `r > m(k-1)`, so `r >= 2k-1` at uniformity 2 — is off by a factor of
/// two from the truth, and no amount of tightening its counting
/// argument would close that gap.
#[test]
fn the_threshold_at_uniformity_two_is_k() {
    for k in 3..=200u64 {
        assert_eq!(r_star(k), k, "r*(2,{k}) is not {k}");
    }
    // `k = 2` is the degenerate case: two disjoint edges are forced as
    // soon as there are more than `r^2 = 1` of them.
    assert_eq!(r_star(2), 1);
}

/// The witness the prediction rests on: below `r*`, the extremal graph
/// at `(r, k-1)` really does satisfy every hypothesis of
/// `SpreadYieldsDisjoint 2 k r` and fail its conclusion.
#[test]
fn extremal_graphs_refute_below_the_threshold() {
    for k in 2..=6u64 {
        for r in 1..r_star(k) {
            if extremal_vertices(r, k - 1) > 32 {
                continue;
            }
            let f = extremal(r, k - 1);
            assert!(is_uniform(2, &f) && is_distinct(&f));
            assert!(
                is_rao_spread(2, &f, r, 32),
                "extremal({r}, {}) is not {r}-spread",
                k - 1
            );
            assert!(
                f.len() as u64 > r * r,
                "extremal({r}, {}) has {} edges, not more than r^2 = {}",
                k - 1,
                f.len(),
                r * r
            );
            assert_eq!(
                matching_number(&f) as u64,
                k - 1,
                "extremal({r}, {}) has the wrong matching number",
                k - 1
            );
        }
    }
}

/// `Audit.no_spread_yields_disjoint_2_3_2` is the case `k = 3, r = 2`,
/// where `CH(2,2) = 6 > 4`. The named Coq witness is the five-cycle;
/// the extremal graph is two triangles, `F23.two_triangles`, which
/// `Audit.no_spread_yields_disjoint_2_3_2_alt` also uses.
#[test]
fn the_coq_refutation_at_2_3_2_is_the_extremal_graph() {
    assert_eq!(ch(2, 2), 6);
    assert_eq!(r_star(3), 3);
    let f = extremal(2, 2);
    let two_triangles: Vec<Mask> = vec![
        0b000011, 0b000110, 0b000101, // {0,1} {1,2} {0,2}
        0b011000, 0b110000, 0b101000, // {3,4} {4,5} {3,5}
    ];
    let mut got = f.clone();
    let mut want = two_triangles;
    got.sort_unstable();
    want.sort_unstable();
    assert_eq!(got, want, "extremal(2,2) is not F23.two_triangles");
}

// ---------------------------------------------------------------
// 5. The sunflower number
// ---------------------------------------------------------------

/// `f(2,3) = 7` is `F23.f_2_3_eq_7`, the exact sunflower number the
/// repository proves. `CH(2,2) + 1 = 7`.
#[test]
fn f_2_3_agrees_with_the_coq_theorem() {
    assert_eq!(f_2_k(3), 7);
}

/// `f(2,k) = CH(k-1,k-1)+1` against exhaustive tabulation, which knows
/// nothing about degrees or matchings — it enumerates every family and
/// looks for sunflowers directly.
///
/// The tabulator is bounded by its universe, so it reports the largest
/// sunflower-free family *over that universe*; the extremal one has
/// `2k` vertices, so `k = 3` on six points is the largest case that
/// both fits and terminates.
#[test]
fn f_2_k_agrees_with_exhaustive_tabulation() {
    let (m, witness) = f_nk_exact(2, 3, 6);
    assert_eq!(m, f_2_k(3), "tabulated f(2,3) = {m}");
    assert_eq!(witness.len(), ch(2, 2) as usize);
}

/// The bridge from the extremal problem to sunflowers: a `k`-sunflower
/// in a graph is `k` disjoint edges or `k` edges through a point, so a
/// 2-uniform family is `k`-sunflower-free exactly when its matching
/// number and maximum degree are both at most `k-1`.
///
/// This is `coq/F23.v`'s `two_uniform_sunflower_shape` checked over
/// every graph on small ground sets. If it failed, `f(2,k)` and
/// `CH(k-1,k-1)` would be different problems.
#[test]
fn sunflower_freeness_is_the_two_constraints() {
    use sunflower_formal::spread::mask_to_set;
    use sunflower_formal::sunflower::find_k_sunflower;

    for ground in [4u32, 5, 6] {
        for k in 2..=4usize {
            for_each_family(ground, 2, |f| {
                let sets: Vec<Vec<u32>> = f.iter().map(|&a| mask_to_set(a)).collect();
                let has_sunflower = find_k_sunflower(&sets, k).is_some();
                let bounded = max_degree(f, ground) < k && matching_number(f) < k;
                assert_eq!(
                    !has_sunflower,
                    bounded,
                    "at k = {k}: sunflower-free = {} but (degree, matching) < k = {bounded} on {}",
                    !has_sunflower,
                    family_to_coq(f)
                );
            });
        }
    }
}

// ---------------------------------------------------------------
// The report that goes in the build log
// ---------------------------------------------------------------

#[test]
fn print_ch_table() {
    eprintln!();
    eprint!("{}", report(8));
    eprintln!(
        "\n  CH is Chvatal-Hanson, JCTB 20 (1976) 128-138. Both columns are\n  \
         consequences of it at uniformity 2; neither is proved in Coq yet.\n"
    );
}

// ---------------------------------------------------------------
// 6. The Coq lower bound
// ---------------------------------------------------------------

/// `CliqueLowerBound.two_cliques_lower_bound`: for odd `k`, two
/// disjoint copies of `K_k` have `k(k-1)` edges, maximum degree
/// `k-1`, matching number `k-1`, and hence no `k`-sunflower.
///
/// The first four claims are the two parameters the Coq proof bounds;
/// the last is checked with the sunflower detector, which knows
/// nothing about degrees or matchings. It is exponential in `k`, so it
/// runs only where it can — the point of the Coq proof is that it does
/// not have to.
#[test]
fn coq_clique_lower_bound_is_sunflower_free() {
    use sunflower_formal::spread::mask_to_set;
    use sunflower_formal::sunflower::find_k_sunflower;

    for k in [3u64, 5, 7, 9] {
        let f = extremal(k - 1, k - 1);
        assert_eq!(f.len() as u64, k * (k - 1), "edge count at k = {k}");
        assert_eq!(f.len() as u64 + 1, f_2_k(k), "f(2,{k})");
        assert_eq!(max_degree(&f, 32) as u64, k - 1, "max degree at k = {k}");
        assert_eq!(matching_number(&f) as u64, k - 1, "matching number at k = {k}");
    }
    for k in [3usize, 5] {
        let f = extremal(k as u64 - 1, k as u64 - 1);
        let sets: Vec<Vec<u32>> = f.iter().map(|&a| mask_to_set(a)).collect();
        assert!(
            find_k_sunflower(&sets, k).is_none(),
            "two copies of K_{k} contain a {k}-sunflower"
        );
    }
}

/// `CliqueLowerBound.clique_edges`, re-implemented and differenced
/// against the general extremal construction.
///
/// The two are built from different ideas. `clique_edges l` is Coq's:
/// every 2-subset of a vertex list, recursively. `extremal(d, v)` is
/// this crate's reading of the Chvátal–Hanson extremal graph: `v/⌈d/2⌉`
/// *odd near-regular* components — a complete graph on `2⌈d/2⌉+1`
/// vertices minus a minimum edge cover — plus stars for the remainder.
/// At `d = v = k-1` with `k` odd those two descriptions must coincide,
/// because a complete graph on `k` vertices is already `(k-1)`-regular
/// and has nothing to remove. If they did not, one of the two readings
/// of "the extremal graph at odd `k`" would be wrong, and the Coq
/// lower bound and the CH formula would be about different objects.
///
/// `Audit.clique_construction_is_two_triangles_reordered` makes the
/// same comparison inside the kernel, but only at `k = 3`, where the
/// answer is six edges and every construction agrees. This is `k = 5`
/// and `k = 7`, where they need not.
#[test]
fn coq_clique_edges_agrees_with_the_extremal_construction() {
    /// Coq's `CliqueLowerBound.clique_edges`, verbatim: every 2-subset
    /// of `l`, each written with its earlier endpoint first.
    fn clique_edges(l: &[u32]) -> Vec<Mask> {
        match l {
            [] => Vec::new(),
            [v, rest @ ..] => rest
                .iter()
                .map(|w| 1 << v | 1 << w)
                .chain(clique_edges(rest))
                .collect(),
        }
    }

    for k in [3u32, 5, 7] {
        let u0: Vec<u32> = (0..k).collect();
        let u1: Vec<u32> = (k..2 * k).collect();
        // Coq's `two_cliques U0 U1 = clique_edges U0 ++ clique_edges U1`.
        let mut coq: Vec<Mask> = clique_edges(&u0);
        coq.extend(clique_edges(&u1));
        let mut rust = extremal(k as u64 - 1, k as u64 - 1);

        assert_eq!(
            coq.len() as u64,
            k as u64 * (k as u64 - 1),
            "clique_edges has the wrong count at k = {k}"
        );
        // Equal as *families*: the two constructions emit the edges in
        // different orders, which is exactly what `FamilyEquiv` is for
        // on the Coq side.
        coq.sort_unstable();
        rust.sort_unstable();
        assert_eq!(
            coq,
            rust,
            "at k = {k} the Coq construction is {} and this crate's is {}",
            family_to_coq(&coq),
            family_to_coq(&rust)
        );
        // And it is extremal: two copies of K_k attain CH(k-1, k-1).
        verify_extremal(&coq, k as u64 - 1, k as u64 - 1)
            .unwrap_or_else(|e| panic!("two copies of K_{k} are not extremal: {e}"));
    }
}

/// `Audit.oddness_is_needed`: the oddness hypothesis is not an
/// artefact of the proof. At even `k` the same construction has a
/// perfect matching — `k` disjoint edges, hence a `k`-sunflower — so
/// the even case genuinely needs the other extremal graph.
#[test]
fn two_cliques_fail_at_even_k() {
    use sunflower_formal::spread::mask_to_set;
    use sunflower_formal::sunflower::find_k_sunflower;

    for k in [4usize, 6] {
        let mut f: Vec<Mask> = Vec::new();
        for base in [0u32, k as u32] {
            for i in 0..k as u32 {
                for j in (i + 1)..k as u32 {
                    f.push(1 << (base + i) | 1 << (base + j));
                }
            }
        }
        assert_eq!(max_degree(&f, 32), k - 1);
        assert_eq!(
            matching_number(&f),
            k,
            "two copies of K_{k} with k even have a perfect matching"
        );
        let sets: Vec<Vec<u32>> = f.iter().map(|&a| mask_to_set(a)).collect();
        assert!(
            find_k_sunflower(&sets, k).is_some(),
            "k disjoint edges but no {k}-sunflower"
        );
        // ... and the true extremal graph at even k is a different one,
        // with strictly more edges than two cliques would give.
        assert!(
            ch(k as u64 - 1, k as u64 - 1) > (k as u64 - 1) * (k as u64 - 1),
            "CH at even k should beat the two-clique count"
        );
    }
}
