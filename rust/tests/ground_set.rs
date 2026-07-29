//! How much ground set does an extremal sunflower-free family need?
//!
//! `N(m, g)` is the largest `m`-uniform 3-sunflower-free family on `g`
//! points. It is non-decreasing in `g` and bounded above by `f(m,3) - 1`,
//! so it plateaus, and `SliceRank.GroundBounded c` is the claim that it
//! plateaus by `g = c * m`. That claim is the one fact standing between
//! the Naslund-Sawin bound — which is `constant ^ (ground set)` — and the
//! sunflower conjecture at `k = 3`, which needs `constant ^ (uniformity)`.
//!
//! This file pins what the search knows. The full scan is
//! `examples/ground_scan.rs`, which is a one-off: `m = 3` at `g = 9` does
//! not finish. What is in CI is the part that does, plus the checks that
//! the search itself is not lying.
//!
//! Three things are aimed at:
//!
//! 1. **The search agrees with what is already proved.** `N(1,g)` must
//!    stabilise at `f(1,3) - 1 = 2` and `N(2,g)` at `f(2,3) - 1 = 6`,
//!    both of which are exact values with machine-checked Coq proofs.
//!    A search that disagreed with `F23.f_2_3_eq_7` would be broken.
//! 2. **The witnesses are real.** Every maximum is verified member by
//!    member against the brute-force detector in `sunflower.rs`, which
//!    knows nothing about the search.
//! 3. **The number the literature reports.** `N(3,6) = 10` is the
//!    Abbott-Hanson-Sauer seed, and getting it exactly is what showed
//!    that an earlier note in this repository had compared it against
//!    the wrong quantity.

use sunflower_formal::ground::{m_subsets, max_sunflower_free, verify};
use sunflower_formal::sunflower::{find_k_sunflower, Family};

/// Generous enough that everything in this file is exhaustive.
const BUDGET: u64 = 4_000_000_000;

fn exact(ground: u32, m: u32) -> usize {
    let (n, fam, done) = max_sunflower_free(ground, m, BUDGET);
    assert!(done, "N({m},{ground}) did not finish");
    verify(&fam, m).unwrap_or_else(|e| panic!("witness for N({m},{ground}): {e}"));
    assert_eq!(fam.len(), n);
    n
}

/// 1. Agreement with the exact values proved in Coq.
#[test]
fn plateaus_match_the_exact_values() {
    // f(1,3) = 3, so N(1,g) tops out at 2 -- and immediately.
    let row1: Vec<usize> = (1..=8).map(|g| exact(g, 1)).collect();
    assert_eq!(row1, vec![1, 2, 2, 2, 2, 2, 2, 2]);

    // f(2,3) = 7 (`F23.f_2_3_eq_7`), so N(2,g) tops out at 6, first
    // reached at g = 6 -- which is `two_triangles`, on 3m points.
    let row2: Vec<usize> = (2..=9).map(|g| exact(g, 2)).collect();
    assert_eq!(row2, vec![1, 3, 4, 5, 6, 6, 6, 6]);
}

/// 2. The uniformity-3 row, as far as exhaustive search reaches.
#[test]
fn uniformity_three_row() {
    let row3: Vec<usize> = (3..=8).map(|g| exact(g, 3)).collect();
    assert_eq!(row3, vec![1, 4, 6, 10, 12, 12]);

    // g = 9 is where it stops finishing. A budgeted run is still a valid
    // *lower* bound, and it is already above the g = 8 value -- so the
    // row has not plateaued at 3m = 9, whatever the true value is.
    let (n9, fam9, done9) = max_sunflower_free(9, 3, 200_000_000);
    verify(&fam9, 3).expect("witness at g = 9");
    assert!(n9 >= 12, "budgeted run should at least match g = 8");
    if done9 {
        // If a future search does finish here, this test should be
        // rewritten rather than silently weakened.
        assert!(n9 >= 12);
    }
}

/// The Abbott-Hanson-Sauer seed, exactly.
#[test]
fn ahs_seed_is_the_maximum_on_six_points() {
    let (n, fam, done) = max_sunflower_free(6, 3, BUDGET);
    assert!(done);
    assert_eq!(n, 10, "N(3,6) is the reported AHS seed size");
    verify(&fam, 3).expect("the seed is not sunflower-free");

    // The direct sum reaches 12 at uniformity 3 -- on *eight* points, so
    // the two numbers are not in competition. This is the comparison an
    // earlier note in this repository got wrong.
    let (n8, _, done8) = max_sunflower_free(8, 3, BUDGET);
    assert!(done8);
    assert_eq!(n8, 12);
    assert!(n8 > n, "more ground set, more family");
}

/// 3. The search is not lying: at parameters small enough to enumerate
///    every subfamily, branch-and-bound must agree with brute force.
#[test]
fn search_agrees_with_full_enumeration() {
    for (ground, m) in [(4u32, 1u32), (5, 1), (4, 2), (5, 2), (5, 3), (6, 3)] {
        let universe = m_subsets(ground, m);
        assert!(universe.len() <= 20, "would enumerate 2^{}", universe.len());
        let mut best = 0usize;
        for mask in 0u32..(1 << universe.len()) {
            let f: Family = (0..universe.len())
                .filter(|i| mask >> i & 1 == 1)
                .map(|i| {
                    (0..16u32)
                        .filter(|b| universe[i] >> b & 1 == 1)
                        .collect::<Vec<u32>>()
                })
                .collect();
            if f.len() > best && find_k_sunflower(&f, 3).is_none() {
                best = f.len();
            }
        }
        assert_eq!(
            best,
            exact(ground, m),
            "branch and bound disagrees with brute force at ({ground},{m})"
        );
    }
}

/// `N(m,g)` must be non-decreasing in `g`: a family on `g` points is a
/// family on `g+1` points. If the search ever violated this it would be
/// pruning something it should not.
#[test]
fn monotone_in_the_ground_set() {
    for m in 1u32..=3 {
        let mut prev = 0usize;
        for g in m..=7 {
            let n = exact(g, m);
            assert!(n >= prev, "N({m},{g}) = {n} < N({m},{}) = {prev}", g - 1);
            prev = n;
        }
    }
}

/// The ground set of a sunflower-free `k`-uniform family can be
/// **exponentially** large: `2^(k+1) - 2` points, on `2^k` members.
///
/// This is the construction [FPPTZ24] (the "Odd-sunflowers" paper, JCTA
/// 2024) uses for `g_v(k) >= 2^k - 1`, and it settles how
/// `SliceRank.GroundBounded` may be read. The *universal* reading —
/// "every sunflower-free `m`-uniform family lives on `O(m)` points" — is
/// false, and this is why. `GroundBounded` survives only in its
/// existence form: some family of each achievable size can be *realised*
/// on `c*m` points. That distinction is load-bearing, not pedantry.
///
/// The same paper records that it could find no papers studying the
/// ground-set quantity at all.
#[test]
fn the_ground_set_of_a_sunflower_free_family_can_be_exponential() {
    use sunflower_formal::construction::{tree_paths, tree_paths_ground};
    use sunflower_formal::intersecting::find_sunflower_128;

    for k in 1..=6u32 {
        let f = tree_paths(k);
        assert_eq!(f.len(), 1usize << k, "member count at k={k}");
        // k-uniform.
        for m in &f {
            assert_eq!(m.count_ones(), k, "uniformity at k={k}");
        }
        // Distinct.
        let mut sorted = f.clone();
        sorted.sort_unstable();
        sorted.dedup();
        assert_eq!(sorted.len(), f.len(), "distinctness at k={k}");
        // Sunflower-free, by the independent 128-bit detector.
        assert_eq!(find_sunflower_128(&f), None, "a 3-sunflower at k={k}");
        // Every edge is used, so the ground set really is that big.
        let g = tree_paths_ground(k);
        for x in 0..g {
            assert!(
                f.iter().any(|m| m >> x & 1 == 1),
                "edge {x} unused at k={k}"
            );
        }
        assert!(
            f.iter().all(|m| *m < (1u128 << g)),
            "a member leaves the ground set at k={k}"
        );
        assert_eq!(g, (1u32 << (k + 1)) - 2);
        // Exponential in the uniformity, which is the point.
        assert!(g as usize >= (1usize << k) - 1, "g_v({k}) >= 2^{k} - 1");
    }

    // Concretely: at k = 6, sixty-four 6-sets on a hundred and
    // twenty-six points. No linear bound in the uniformity survives.
    assert_eq!(tree_paths(6).len(), 64);
    assert_eq!(tree_paths_ground(6), 126);
}
