//! `r*(m,3)`: the sharp spread threshold, measured.
//!
//! `SpreadReduction.SpreadYieldsDisjoint n 3 r` is true for every `r`
//! above `r*(n,3)` and false below it, and by `spread_reduction` a bound
//! on the sequence is a bound on `f(m,3)`. Whether it is bounded in `m`
//! *is* the sunflower conjecture at `k = 3`, so its terms are the object
//! this repository is built to compute (docs/roadmap.md §18.5, §22).
//!
//! Everything here is a certificate for one of three kinds of claim.
//!
//! * **`r` is refuted at uniformity `m`** — an explicit family, verified
//!   against every hypothesis by `rstar::verify`, which shares no code
//!   with the searches that produce it. This is a lower bound on `r*`.
//! * **`r` is not refuted on `[ground]`** — an exhaustive search, or an
//!   arithmetic precheck that makes the search unnecessary.
//! * **The Coq bounds evaluate to the numbers they are quoted at.**
//!   `SpreadThreshold.quadratic_spread_disjoint` is stated with an
//!   inequality on `(n, r)`; `rstar::quadratic_bound` solves it, and the
//!   solved values are what `docs/roadmap.md` §22 tabulates.

use sunflower_formal::rstar::{
    cover_bound, decide, degree_ceiling, dfs, min_ground, quadratic_bound, verify, Outcome,
    Question, Ternary,
};
use sunflower_formal::spread::{has_k_disjoint, is_rao_spread, matching_number, Mask};

/// The elementary bounds on `r*(m,3)`, as the Coq corollaries quote them.
///
/// `cover_bound` is `SpreadThreshold.cover_spread_disjoint` (`2m`);
/// `quadratic_bound` solves the condition of
/// `SpreadThreshold.quadratic_spread_disjoint`, `2r + 3m² + 2 ≤ r² + 4m`.
/// The previous best in the development was
/// `SpreadReduction.elementary_spread_disjoint`, `2m + 1`.
#[test]
fn threshold_upper_bounds_are_what_coq_proves() {
    // (m, elementary 2m+1, cover 2m, quadratic)
    let table = [
        (1u64, 3u64, 2u64, 3u64),
        (2, 5, 4, 4),
        (3, 7, 6, 6),
        (4, 9, 8, 7),
        (5, 11, 10, 9),
        (6, 13, 12, 11),
        (10, 21, 20, 18),
    ];
    for (m, elementary, cover, quadratic) in table {
        assert_eq!(cover_bound(m), cover, "cover bound at m = {m}");
        assert_eq!(quadratic_bound(m), quadratic, "quadratic bound at m = {m}");
        assert_eq!(2 * m + 1, elementary);
        assert!(cover <= elementary, "the cover bound never loses at m = {m}");
    }
    // The headline: r*(4,3) <= 7, two below the elementary bound, and the
    // Coq condition holds at exactly (4, 7) and fails at (4, 6).
    assert!(2 * 7 + 3 * 4 * 4 + 2 <= 7 * 7 + 4 * 4);
    assert!(2 * 6 + 3 * 4 * 4 + 2 > 6 * 6 + 4 * 4);
    assert_eq!(quadratic_bound(4), 7);
}

/// The quadratic bound is asymptotically `√3 · m`, so it is a genuine
/// constant-factor improvement on `2m` rather than an off-by-one.
#[test]
fn quadratic_bound_beats_the_cover_bound_from_four_on() {
    for m in 4u64..40 {
        assert!(
            quadratic_bound(m) < cover_bound(m),
            "quadratic bound should beat 2m at m = {m}"
        );
    }
    // 3 m^2 - 4 m + 3 under the root: r ~ 1 + 1.732 m.
    // At m = 100: 173^2 - 2*173 = 29583 < 29602, 174^2 - 2*174 = 29928 >= 29602.
    assert_eq!(quadratic_bound(100), 174);
}

/// The counting precheck. `m·|F| = Σ_x deg(x) ≤ ground · r^(m-1)`, so a
/// counterexample needs `ceil(m (r^m + 1) / r^(m-1))` points.
///
/// At `(m,r) = (3,3)` that is 10 — which is exactly the ground set where
/// §3.6's enumeration ran out of budget. Grounds 8 and 9 are decided by
/// arithmetic, with no search at all.
#[test]
fn counting_settles_the_small_ground_sets() {
    assert_eq!(min_ground(3, 3), 10);
    assert_eq!(degree_ceiling(3, 3, 9), 27); // < 28, no room
    assert_eq!(degree_ceiling(3, 3, 10), 30);
    for g in 6..=9 {
        let q = Question::new(3, 3, g);
        let rep = dfs(&q, 1);
        assert_eq!(rep.outcome, Outcome::None, "ground {g} is settled by counting");
        assert_eq!(rep.nodes, 0, "and settled without searching");
    }
    assert_eq!(min_ground(4, 3), 13);
    assert_eq!(min_ground(4, 4), 17);
    assert_eq!(min_ground(2, 3), 7);
}

/// Each of these is a verified counterexample: an `r`-spread `m`-uniform
/// family of more than `r^m` sets with no three pairwise disjoint
/// members. It refutes `SpreadYieldsDisjoint m 3 r`, hence `r*(m,3) > r`,
/// hence `r*(m,3) >= 3` at uniformities 2, 3 and 4.
///
/// The families are pinned rather than re-searched: they are the
/// certificates, and a certificate that has to be recomputed to be read
/// is not one. Each was produced by the SAT encoding and is re-checked
/// here against `Spread.RaoSpread`, the size hypothesis and the matching
/// number, by code that shares nothing with the search.
#[test]
fn r_star_is_at_least_three_at_uniformity_two_three_and_four() {
    // (m, r, ground, family)
    let witnesses: [(u32, u64, u32, &[Mask]); 3] = [
        (2, 2, 6, &[3, 5, 12, 18, 24]),
        (3, 2, 8, &[7, 11, 13, 14, 49, 56, 82, 84, 224]),
        (
            4,
            2,
            11,
            &[
                15, 23, 27, 29, 30, 99, 101, 102, 169, 170, 177, 204, 210, 240, 308, 456, 1856,
                1920,
            ],
        ),
    ];
    for (m, r, g, f) in witnesses {
        let q = Question::new(m, r, g);
        verify(f, &q).unwrap_or_else(|e| panic!("m={m} r={r}: {e}"));
        assert!(f.len() as u64 > r.pow(m), "size hypothesis at m={m} r={r}");
        assert!(is_rao_spread(m, f, r, g));
        assert!(!has_k_disjoint(f, 3));
        assert_eq!(matching_number(f), 2);
        assert!(f.iter().all(|a| a.count_ones() == m));
    }
}

/// The pinned witnesses are findable: the SAT encoding reproduces a
/// counterexample at each of their parameters. This is the search half
/// of the certificate — that the witnesses were not simply invented.
#[test]
fn the_witnesses_are_reachable_by_search() {
    for (m, r, g) in [(2u32, 2u64, 6u32), (3, 2, 8), (4, 2, 11)] {
        let q = Question::new(m, r, g);
        match decide(&q, 300).expect("solver").outcome {
            Outcome::Counterexample(f) => verify(&f, &q).unwrap(),
            other => panic!("m={m} r={r} ground={g}: {other:?}"),
        }
    }
}

/// `r = 1` is refuted at every uniformity by two disjoint sets: the
/// degree bound forces the family to be a matching, and two members
/// already beat `1^m = 1`.
#[test]
fn one_is_refuted_at_every_uniformity() {
    for m in 1u32..=5 {
        let q = Question::new(m, 1, 2 * m);
        match dfs(&q, u64::MAX).outcome {
            Outcome::Counterexample(f) => {
                verify(&f, &q).unwrap();
                assert_eq!(f.len(), 2);
            }
            other => panic!("m = {m}: {other:?}"),
        }
    }
}

/// The two searches are independent implementations — a SAT encoding
/// with lex-leader symmetry breaking, and a depth-first enumeration with
/// counting bounds. They must agree wherever both finish.
#[test]
fn sat_and_dfs_agree() {
    let cases = [(2u32, 2u64, 6u32), (2, 3, 7), (3, 2, 7), (3, 2, 8)];
    for (m, r, g) in cases {
        let mut q = Question::new(m, r, g);
        q.ternary = Ternary::Eager;
        let sat = decide(&q, 300).expect("solver");
        let brute = dfs(&q, u64::MAX);
        let sat_found = matches!(sat.outcome, Outcome::Counterexample(_));
        let dfs_found = matches!(brute.outcome, Outcome::Counterexample(_));
        assert!(
            !matches!(sat.outcome, Outcome::Unknown),
            "SAT gave up at m={m} r={r} g={g}"
        );
        assert_eq!(
            sat_found, dfs_found,
            "SAT and DFS disagree at m={m} r={r} ground={g}"
        );
        if let Outcome::Counterexample(f) = &sat.outcome {
            verify(f, &q).unwrap();
        }
    }
}

/// `r*(1,3) = 2`, the first exact term: `r = 1` is refuted by two
/// singletons, and `cover_spread_disjoint` at `n = 1` proves `r = 2`
/// works. A 1-uniform distinct family of more than two members is three
/// pairwise disjoint singletons.
#[test]
fn r_star_one_three_is_two() {
    let q = Question::new(1, 1, 2);
    match dfs(&q, u64::MAX).outcome {
        Outcome::Counterexample(f) => {
            verify(&f, &q).unwrap();
            assert_eq!(f, vec![1, 2]);
        }
        other => panic!("{other:?}"),
    }
    for g in 2u32..=8 {
        let q = Question::new(1, 2, g);
        assert_eq!(dfs(&q, u64::MAX).outcome, Outcome::None, "ground {g}");
    }
    assert_eq!(cover_bound(1), 2);
}

/// `r*(2,3) = 3`: `r = 2` is refuted by the five-cycle and `r = 3` is not
/// refuted on any ground set a counterexample could use.
///
/// The bound on the ground set is the same counting that
/// `counting_settles_the_small_ground_sets` uses, run the other way: at
/// `(m,r) = (2,3)` a counterexample has at most `2·2·3 = 12` members
/// (`SpreadThreshold.no_three_disjoint_cover_bound`), every member has at
/// most one point outside the 4-point cover, so its support is at most
/// `4 + 12 = 16`.
#[test]
fn r_star_two_three_is_three() {
    let refuted = {
        let q = Question::new(2, 2, 5);
        matches!(dfs(&q, u64::MAX).outcome, Outcome::Counterexample(_))
    };
    assert!(refuted, "the five-cycle refutes r = 2 at uniformity 2");
    // SpreadYieldsDisjoint 2 3 3 quantifies over m = 1 as well: four
    // distinct singletons are three pairwise disjoint members.
    for g in 2u32..=10 {
        for nu in [1usize, 2] {
            let mut q = Question::new(1, 3, g);
            q.nu = nu;
            assert_eq!(dfs(&q, u64::MAX).outcome, Outcome::None, "m=1 ground {g}");
        }
    }
    for g in min_ground(2, 3)..=16 {
        for nu in [1usize, 2] {
            let mut q = Question::new(2, 3, g);
            q.nu = nu;
            let rep = dfs(&q, u64::MAX);
            assert!(!rep.truncated, "ground {g} nu {nu} did not finish");
            assert_eq!(
                rep.outcome,
                Outcome::None,
                "unexpected counterexample at ground {g}, nu = {nu}"
            );
        }
    }
}

/// A counterexample really is what the Coq statement asks for: the
/// decoded family is checked against `Spread.RaoSpread`'s quantifier over
/// *every* nonempty subset of the ground set, not just the ones the
/// search tracked.
#[test]
fn counterexamples_satisfy_the_quantifier_over_all_subsets() {
    let q = Question::new(3, 2, 7);
    let f: Vec<Mask> = match dfs(&q, u64::MAX).outcome {
        Outcome::Counterexample(f) => f,
        other => panic!("{other:?}"),
    };
    for t in 1u32..(1u32 << 7) {
        let d = f.iter().filter(|&&a| a & t == t).count() as u64;
        let cap = 2u64.pow(3u32.saturating_sub(t.count_ones()));
        assert!(d <= cap, "subset {t:b} has degree {d} > {cap}");
    }
}
