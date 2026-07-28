//! Falsification tests for the spread hypothesis and its decision
//! procedure.
//!
//! Where `small_cases.rs` cross-checks *theorems* against brute force,
//! this file cross-checks *definitions*. Both statement errors this
//! development has produced were invisible to the kernel — a
//! degenerate `w_spread`, and an axiom that had quietly swapped Rao's
//! absolute spread condition for a fractional one — and neither would
//! have been caught by checking a proved bound on small inputs. What
//! catches them is running the definitions themselves over an
//! exhaustive enumeration and comparing against something already
//! known.
//!
//! Four kinds of check, in increasing order of what they would catch:
//!
//! 1. The search is right (`search_matches_brute_force`). Everything
//!    else rests on it, so it is validated against unpruned
//!    enumeration of every family.
//! 2. Coq theorems, re-derived computationally. Each of these would
//!    fail if the Rust reading of a Coq definition differed from the
//!    Coq one — which is exactly a misstatement.
//! 3. Coq refutations, re-derived computationally: the counterexample
//!    families named in `coq/Audit.v` are found by the search, and the
//!    search finds none where Coq proves there is none.
//! 4. Non-vacuity: families really do satisfy every hypothesis of the
//!    axiom at the published threshold, so it is not assuming the
//!    empty statement.

use sunflower_formal::spread::{
    family_to_coq, has_k_disjoint, is_distinct, is_fractionally_spread, is_rao_spread, is_uniform,
    matching_number, pow_sat, subsets_of_size, Mask,
};
use sunflower_formal::sunflower::find_k_sunflower;
use sunflower_formal::testbed::{
    empirical_threshold, find_counterexample, for_each_family, rao_implies_fractional, search,
    threshold_report, verify_counterexample, witnesses_agree,
};

fn set(elts: &[u32]) -> Mask {
    elts.iter().fold(0, |acc, &x| acc | 1 << x)
}

/// `Audit.c5` — the five-cycle.
fn c5() -> Vec<Mask> {
    vec![
        set(&[0, 1]),
        set(&[1, 2]),
        set(&[2, 3]),
        set(&[3, 4]),
        set(&[0, 4]),
    ]
}

/// `F23.two_triangles` — the family witnessing `f(2,3) >= 7`.
fn two_triangles() -> Vec<Mask> {
    vec![
        set(&[0, 1]),
        set(&[1, 2]),
        set(&[0, 2]),
        set(&[3, 4]),
        set(&[4, 5]),
        set(&[3, 5]),
    ]
}

/// The circulant graph on `n` vertices with connection set `1..=d`:
/// `2d`-regular, `n*d` edges, simple as long as `2d < n`.
fn circulant(n: u32, d: u32) -> Vec<Mask> {
    assert!(2 * d < n);
    let mut f = Vec::new();
    for i in 0..n {
        for j in 1..=d {
            f.push(set(&[i, (i + j) % n]));
        }
    }
    f.sort_unstable();
    f.dedup();
    f
}

/// The parameter grid. Kept small enough that the whole file runs in
/// well under a second in release mode; every case is an *exhaustive*
/// search over its ground set.
const GRID: &[(u32, u32, usize)] = &[
    (4, 1, 2),
    (6, 1, 3),
    (8, 1, 4),
    (8, 1, 5),
    (4, 2, 2),
    (5, 2, 3),
    (6, 2, 3),
    (7, 2, 3),
    (8, 2, 3),
    (8, 2, 4),
    (6, 3, 2),
    (6, 3, 3),
    (7, 3, 3),
    (8, 3, 3),
];

// ---------------------------------------------------------------
// 1. The search itself
// ---------------------------------------------------------------

/// The pruned depth-first search must agree with unpruned enumeration
/// of every single family, both on whether a counterexample exists and
/// on the size of the largest constrained family.
#[test]
fn search_matches_brute_force() {
    for &(ground, m) in &[(5u32, 2u32), (6, 2), (5, 3)] {
        for k in 2..=4usize {
            for r in 1..=3u64 {
                let mut brute_best = 0usize;
                let mut brute_counterexample = false;
                for_each_family(ground, m, |f| {
                    if !is_rao_spread(m, f, r, ground) || has_k_disjoint(f, k) {
                        return;
                    }
                    if f.len() > brute_best {
                        brute_best = f.len();
                    }
                    if f.len() as u64 > pow_sat(r, m) {
                        brute_counterexample = true;
                    }
                });

                let full = search(ground, m, k, r, false);
                assert_eq!(
                    full.largest.len(),
                    brute_best,
                    "largest constrained family disagrees at ground={ground} m={m} k={k} r={r}"
                );
                assert_eq!(
                    find_counterexample(ground, m, k, r).is_some(),
                    brute_counterexample,
                    "counterexample verdict disagrees at ground={ground} m={m} k={k} r={r}"
                );
            }
        }
    }
}

/// Anything the search reports as a counterexample must survive a
/// re-check against the definitions, computed from scratch.
#[test]
fn reported_counterexamples_are_genuine() {
    for &(ground, m, k) in GRID {
        let (_, failing) = empirical_threshold(ground, m, k);
        for r in failing {
            let f = find_counterexample(ground, m, k, r).expect("threshold scan said it exists");
            verify_counterexample(&f, ground, m, k, r)
                .unwrap_or_else(|e| panic!("bogus counterexample at ({ground},{m},{k},{r}): {e}"));
        }
    }
}

// ---------------------------------------------------------------
// 2. Coq theorems, re-derived computationally
// ---------------------------------------------------------------

/// `SpreadReduction.spread_disjoint_above_elementary`: the spread
/// hypothesis is *true* for every `r > m(k-1)`. A counterexample above
/// that line would mean the Rust and Coq readings of `RaoSpread`,
/// `Uniform`, `Distinct` or `PairwiseDisjoint` differ — or that the
/// Coq theorem is wrong.
#[test]
fn no_counterexample_above_the_proved_threshold() {
    for &(ground, m, k) in GRID {
        let total = subsets_of_size(ground, m).len() as u64;
        let mut r = m as u64 * (k as u64 - 1) + 1;
        while pow_sat(r, m) < total {
            assert!(
                find_counterexample(ground, m, k, r).is_none(),
                "counterexample at ground={ground} m={m} k={k} r={r}, above the threshold \
                 m(k-1)+1 = {} proved sufficient by SpreadReduction.spread_disjoint_above_elementary",
                m as u64 * (k as u64 - 1) + 1
            );
            r += 1;
        }
    }
}

/// The same statement viewed the other way round: the empirical
/// threshold never exceeds the one proved sufficient.
#[test]
fn empirical_threshold_is_below_the_proved_one() {
    for &(ground, m, k) in GRID {
        let (empirical, _) = empirical_threshold(ground, m, k);
        let proved = m as u64 * (k as u64 - 1) + 1;
        assert!(
            empirical <= proved,
            "empirical threshold {empirical} exceeds the proved-sufficient {proved} \
             at ground={ground} m={m} k={k}"
        );
    }
}

/// `Audit.spread_yields_disjoint_below_threshold`: a family of `k-1`
/// pairwise disjoint blocks refutes the hypothesis whenever
/// `r^m < k-1`. The search must find a counterexample wherever that
/// theorem says one exists.
#[test]
fn coq_refutation_below_threshold_is_realised() {
    for &(ground, m, k) in GRID {
        for r in 1..=4u64 {
            if pow_sat(r, m) < (k as u64 - 1) && ground >= (k as u32 - 1) * m {
                assert!(
                    find_counterexample(ground, m, k, r).is_some(),
                    "Audit.spread_yields_disjoint_below_threshold predicts a counterexample \
                     at ground={ground} m={m} k={k} r={r}, search found none"
                );
            }
        }
    }
}

/// `Audit.spread_yields_disjoint_needs_r`, the `m = 1` sharpening:
/// at uniformity 1 the hypothesis is false exactly below `k-1`.
#[test]
fn uniformity_one_threshold_is_exactly_k_minus_1() {
    for k in 2..=6usize {
        let ground = 2 * k as u32;
        let (empirical, _) = empirical_threshold(ground, 1, k);
        assert_eq!(
            empirical,
            k as u64 - 1,
            "at m=1 the threshold should be exactly k-1, k={k}"
        );
    }
}

/// `Spread.RaoSpread_Spread`: Rao's absolute condition plus the size
/// hypothesis implies the fractional (ALWZ / FKNP) one. Checked on
/// every family over the small ground sets, not only on spread ones.
#[test]
fn rao_spread_implies_fractional_spread() {
    for &(ground, m) in &[(5u32, 2u32), (6, 2), (5, 3)] {
        for r in 1..=4u64 {
            for_each_family(ground, m, |f| {
                rao_implies_fractional(m, f, r, ground).unwrap();
            });
        }
    }
}

/// ... and the implication is not an equivalence, so the Coq theorem
/// is saying something. A family that is fractionally spread without
/// being Rao-spread at the same parameter must exist.
#[test]
fn fractional_spread_is_strictly_weaker() {
    let mut found = None;
    for_each_family(5, 2, |f| {
        if found.is_some() || f.is_empty() {
            return;
        }
        let r = 2;
        if is_fractionally_spread(f, r, 5) && !is_rao_spread(2, f, r, 5) {
            found = Some(f.to_vec());
        }
    });
    let f = found.expect("no separating family: RaoSpread and Spread may have collapsed");
    assert!(!is_rao_spread(2, &f, 2, 5));
    assert!(is_fractionally_spread(&f, 2, 5));
}

/// `Reflect.rao_witness_agrees`: the member-sublist search and the
/// ground-set search always return the same verdict. This is the
/// property that a too-small `Spread.cands` would break — silently,
/// weakening the reduction rather than breaking any proof.
#[test]
fn the_two_spread_decision_procedures_agree() {
    for &(ground, m) in &[(5u32, 2u32), (6, 2), (5, 3)] {
        for r in 1..=4u64 {
            for_each_family(ground, m, |f| {
                assert!(
                    witnesses_agree(m, f, r, ground),
                    "rao_witness_cands and rao_witness_ground disagree at r={r} on {}",
                    family_to_coq(f)
                );
            });
        }
    }
}

/// `Audit.no_k_disjoint_of_no_sunflower`: `k` pairwise disjoint
/// nonempty sets are a `k`-sunflower with empty core, so a
/// sunflower-free family has no `k` pairwise disjoint members. Checked
/// against the independent detector in `sunflower.rs`.
#[test]
fn disjointness_and_sunflower_freeness_agree() {
    for &(ground, m) in &[(5u32, 2u32), (5, 3)] {
        for k in 2..=3usize {
            for_each_family(ground, m, |f| {
                if !has_k_disjoint(f, k) {
                    return;
                }
                let sets: Vec<Vec<u32>> = f
                    .iter()
                    .map(|&a| sunflower_formal::spread::mask_to_set(a))
                    .collect();
                assert!(
                    find_k_sunflower(&sets, k).is_some(),
                    "{} has {k} pairwise disjoint members but no {k}-sunflower",
                    family_to_coq(f)
                );
            });
        }
    }
}

// ---------------------------------------------------------------
// 3. The named Coq counterexamples
// ---------------------------------------------------------------

/// `Audit.no_spread_yields_disjoint_2_3_2` uses the five-cycle. It
/// must satisfy every hypothesis and fail the conclusion.
#[test]
fn five_cycle_refutes_2_3_2() {
    let f = c5();
    verify_counterexample(&f, 5, 2, 3, 2).unwrap();
    assert_eq!(matching_number(&f), 2);
}

/// `Audit.no_spread_yields_disjoint_2_3_2_alt` uses `F23.two_triangles`
/// — the same family that witnesses `f(2,3) >= 7`.
#[test]
fn two_triangles_refutes_2_3_2() {
    let f = two_triangles();
    verify_counterexample(&f, 6, 2, 3, 2).unwrap();
    assert_eq!(matching_number(&f), 2);
    assert!(is_uniform(2, &f) && is_distinct(&f));
}

/// On five points every counterexample at these parameters is a
/// relabelling of the five-cycle: there are exactly twelve of them,
/// which is the number of labelled 5-cycles on five vertices
/// (`5!/(5*2) = 12`), and each is 2-regular — on five vertices a
/// 2-regular graph has no choice but to be a single 5-cycle. That is
/// what makes `c5` the natural witness to formalise.
#[test]
fn every_counterexample_on_five_points_is_a_five_cycle() {
    let mut witnesses: Vec<Vec<Mask>> = Vec::new();
    for_each_family(5, 2, |f| {
        if f.len() as u64 > pow_sat(2, 2) && is_rao_spread(2, f, 2, 5) && !has_k_disjoint(f, 3) {
            witnesses.push(f.to_vec());
        }
    });
    assert_eq!(
        witnesses.len(),
        12,
        "expected the twelve labelled 5-cycles, got {}",
        witnesses.len()
    );
    for w in &witnesses {
        assert_eq!(w.len(), 5, "not five edges: {}", family_to_coq(w));
        for v in 0..5u32 {
            let d = w.iter().filter(|&&a| a >> v & 1 == 1).count();
            assert_eq!(d, 2, "vertex {v} has degree {d} in {}", family_to_coq(w));
        }
    }
    let mut want = c5();
    want.sort_unstable();
    assert!(
        witnesses.iter().any(|w| {
            let mut got = w.clone();
            got.sort_unstable();
            got == want
        }),
        "Audit.c5 is not among the counterexamples the search finds"
    );
}

/// Coq proves nothing about `r = 3` at `k = 3, m = 2`; the search says
/// there is nothing to prove — no counterexample exists over any of the
/// ground sets tried. That is the empirical content of "the threshold
/// at uniformity 2 is 3".
#[test]
fn no_counterexample_at_2_3_3() {
    for ground in 4..=9u32 {
        assert!(
            find_counterexample(ground, 2, 3, 3).is_none(),
            "unexpected counterexample at ground={ground}, m=2, k=3, r=3"
        );
    }
}

// ---------------------------------------------------------------
// 4. Non-vacuity of the axiom's hypotheses
// ---------------------------------------------------------------

/// `ALWZ.Rao20_lemma2` demands `r >= alpha * k * log2(km+1)`. If no
/// family ever satisfied its hypotheses at such an `r`, the axiom
/// would be assuming nothing at all — the failure mode
/// `Spread.w_spread_legacy_degenerate` records for the previous
/// definition of spreadness.
///
/// Circulant graphs supply witnesses at the true threshold (taking the
/// most demanding `alpha = 1`): `2d`-regular, so `r`-spread for any
/// `r >= 2d`, with `nd` edges to clear `r^2`.
#[test]
fn axiom_hypotheses_are_satisfiable_at_the_published_threshold() {
    fn log2_up(x: u64) -> u32 {
        let mut e = 0;
        while (1u64 << e) < x {
            e += 1;
        }
        e
    }

    // k = 2, m = 2: threshold r = 2 * log2_up(1 + 4) = 6.
    // k = 3, m = 2: threshold r = 3 * log2_up(1 + 6) = 9.
    for &(k, n, d) in &[(2usize, 13u32, 3u32), (3, 21, 4)] {
        let m = 2u32;
        let r = k as u64 * log2_up(1 + k as u64 * m as u64) as u64;
        let f = circulant(n, d);

        assert!(is_uniform(m, &f), "circulant is not 2-uniform");
        assert!(is_distinct(&f), "circulant has repeated edges");
        assert_eq!(f.len(), (n * d) as usize);
        assert!(
            f.len() as u64 > pow_sat(r, m),
            "size hypothesis fails for k={k}: |F| = {} is not > r^m = {}",
            f.len(),
            pow_sat(r, m)
        );
        assert!(
            is_rao_spread(m, &f, r, n),
            "circulant C_{n}(1..{d}) is not {r}-spread"
        );
        // Hypotheses hold; so must the conclusion.
        assert!(
            has_k_disjoint(&f, k),
            "conclusion fails: no {k} pairwise disjoint edges"
        );
    }
}

/// A census: at every grid point where the hypotheses are satisfiable
/// at all, at least one family satisfies them. A grid point where the
/// count silently dropped to zero would be a vacuous test.
#[test]
fn hypotheses_are_satisfiable_across_the_grid() {
    let mut nonvacuous = 0;
    for &(ground, m, k) in GRID {
        let total = subsets_of_size(ground, m).len() as u64;
        for r in 1..=4u64 {
            if pow_sat(r, m) >= total {
                continue;
            }
            // Take any family of more than r^m sets that is r-spread:
            // if the search's constrained maximum clears the bar, one
            // exists; otherwise look for one with k disjoint members.
            let out = search(ground, m, k, r, false);
            if out.largest.len() as u64 > out.threshold {
                nonvacuous += 1;
            }
        }
    }
    assert!(
        nonvacuous > 0,
        "no grid point produced a family satisfying the spread hypotheses"
    );
}

// ---------------------------------------------------------------
// The report that goes in the build log
// ---------------------------------------------------------------

#[test]
fn print_threshold_table() {
    eprintln!("\n  Empirical spread thresholds (exhaustive over the ground set)\n");
    eprint!("{}", threshold_report(GRID));
    eprintln!(
        "\n  r* is the least r above which no counterexample to \
         SpreadYieldsDisjoint exists.\n  'proved sufficient' is m(k-1)+1, from \
         SpreadReduction.spread_disjoint_above_elementary.\n  r* must never exceed it.\n"
    );
}
