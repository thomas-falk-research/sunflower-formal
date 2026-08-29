//! Falsification for `coq/Support.v`.
//!
//! Three claims are proved there and every one of them is a claim about
//! *every* intersecting 3-sunflower-free family, so every one of them can
//! be falsified by exhibiting one family. This file enumerates families
//! exhaustively on small ground sets and tries.
//!
//! 1. **The two-anchor support bound**, `supp <= (4b-3) + (b-2)n`. The
//!    conclusion is checked directly, and so is the step the proof turns
//!    on — that the core the proof builds is met *twice* by every member
//!    — because a support bound that happened to hold for another reason
//!    would not tell us the proof was right. The core is rebuilt here
//!    from the family alone, sharing no code with the Coq development.
//!
//! 2. **The pair-degree bound**, `deg(Q) <= g(b-2)`, which at `b = 4` is
//!    six and at `b = 3` is two. Six is attained — two disjoint triangles
//!    — so the constant is not slack, and that is asserted rather than
//!    assumed.
//!
//! 3. **The counting ceiling**, `|F| <= C(g,2)` at `b = 4`, and the
//!    arithmetic that turns it into `g >= 9` for a 32-member family.
//!
//! And the honest bookkeeping: the new bound is *not* uniformly better
//! than `PureLink.intersecting_support_bound`. It wins exactly when
//! `n > 4b - 4`, and the crossover is asserted in both directions so a
//! future session cannot quote the new number where the old one is
//! smaller.
//!
//! Every enumeration reports the number of families it visited and
//! asserts it against a fixed count, so a silently truncated sweep is a
//! failing assertion rather than a weaker theorem.

use sunflower_formal::{genprog, ground, wide};

fn masks(sets: &[&[u32]]) -> Vec<u32> {
    sets.iter()
        .map(|s| s.iter().fold(0u32, |a, &x| a | 1 << x))
        .collect()
}

/// The 27-member witness for `iota(4) >= 27`, on nine points.
fn iota4() -> Vec<u32> {
    vec![
        15, 23, 27, 45, 46, 53, 54, 57, 58, 195, 204, 212, 216, 225, 226, 323, 332, 340, 344, 353,
        354, 387, 396, 404, 408, 417, 418,
    ]
}

fn support(f: &[u32]) -> u32 {
    f.iter().fold(0u32, |a, &x| a | x)
}

fn intersecting(f: &[u32]) -> bool {
    (0..f.len()).all(|i| ((i + 1)..f.len()).all(|j| f[i] & f[j] != 0))
}

/// A 3-sunflower is three members whose three pairwise intersections
/// coincide. Written out rather than called, so this file agrees with
/// `coq/Sunflower.v` independently of `sunflower::find_k_sunflower`.
fn sunflower_free(f: &[u32]) -> bool {
    for i in 0..f.len() {
        for j in (i + 1)..f.len() {
            for k in (j + 1)..f.len() {
                let (a, b, c) = (f[i] & f[j], f[i] & f[k], f[j] & f[k]);
                if a == b && b == c {
                    return false;
                }
            }
        }
    }
    true
}

/// The core `coq/Support.v` builds, rebuilt from the family: the anchor,
/// a second member meeting it in exactly one point (if there is one),
/// and a maximal pairwise-disjoint subfamily of the link at the shared
/// point. Returns the core and the size of that subfamily.
fn anchored_core(f: &[u32]) -> (u32, usize) {
    let a0 = f[0];
    match f.iter().find(|&&a| (a & a0).count_ones() == 1) {
        None => (a0, 0),
        Some(&a1) => {
            let z = a0 & a1;
            let mut m: Vec<u32> = Vec::new();
            for &a in f.iter().filter(|&&a| a & z != 0) {
                let l = a & !z;
                if m.iter().all(|&x| x & l == 0) {
                    m.push(l);
                }
            }
            let t = m.iter().fold(0u32, |acc, &x| acc | x);
            (a0 | (a1 & !z) | t, m.len())
        }
    }
}

/// Every `b`-uniform 3-sunflower-free **intersecting** family on `g`
/// points, by DFS over the `b`-subsets in increasing order, with a node
/// budget. Returns the number of families visited and whether the budget
/// was exhausted before the sweep finished.
fn for_each_family<F: FnMut(&[u32])>(g: u32, b: u32, budget: usize, mut visit: F) -> (usize, bool) {
    let sets: Vec<u32> = ground::m_subsets(g, b).into_iter().map(u32::from).collect();
    let mut count = 0usize;
    let mut cur: Vec<u32> = Vec::new();
    let mut stopped = false;
    fn go<F: FnMut(&[u32])>(
        sets: &[u32],
        i: usize,
        cur: &mut Vec<u32>,
        visit: &mut F,
        count: &mut usize,
        budget: usize,
        stopped: &mut bool,
    ) {
        if *stopped {
            return;
        }
        if *count >= budget {
            *stopped = true;
            return;
        }
        *count += 1;
        visit(cur);
        for j in i..sets.len() {
            let s = sets[j];
            // Intersecting is checked incrementally; sunflower-freeness
            // needs only the triples that include the new member.
            if cur.iter().any(|&c| c & s == 0) {
                continue;
            }
            let ok = (0..cur.len()).all(|p| {
                ((p + 1)..cur.len()).all(|q| {
                    let (x, y, z) = (cur[p] & cur[q], cur[p] & s, cur[q] & s);
                    !(x == y && y == z)
                })
            });
            if !ok {
                continue;
            }
            cur.push(s);
            go(sets, j + 1, cur, visit, count, budget, stopped);
            cur.pop();
        }
    }
    go(
        &sets,
        0,
        &mut cur,
        &mut visit,
        &mut count,
        budget,
        &mut stopped,
    );
    (count, stopped)
}

/// The sweeps this file runs, with the family counts they must find.
/// A changed count is a changed enumeration and fails here first.
const SWEEPS: &[(u32, u32, usize)] =
    &[(6, 2, 96), (5, 3, 388), (6, 3, 14022), (7, 3, 107171), (6, 4, 5789)];

/// The exhaustive sweeps stop where they stop for a measured reason:
/// `(7,4)` has 35 333 735 families and `(8,4)` has more than forty
/// million, so `b = 4` is swept exhaustively only to six points. The
/// larger `b = 4` ground sets are *sampled* instead, by
/// [`sampled_families`], and that is a different statement — recorded
/// here rather than blurred into the exhaustive one.
const SWEEP_LIMIT: &str = "(7,4) = 35333735 families; (8,4) > 40000000";

/// Deterministic pseudo-random maximal families, for the ground sets the
/// exhaustive sweep cannot reach. Not an exhaustion and not claimed as
/// one: the budget is the sample count.
fn sampled_families(g: u32, b: u32, samples: usize, seed: u64) -> Vec<Vec<u32>> {
    let blocks: Vec<u32> = ground::m_subsets(g, b).into_iter().map(u32::from).collect();
    let mut state = seed | 1;
    let mut next = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    let mut out = Vec::with_capacity(samples);
    for _ in 0..samples {
        let mut order = blocks.clone();
        for i in (1..order.len()).rev() {
            let j = (next() % (i as u64 + 1)) as usize;
            order.swap(i, j);
        }
        let mut f: Vec<u32> = Vec::new();
        for &s in &order {
            if f.iter().any(|&c| c & s == 0) {
                continue;
            }
            let ok = (0..f.len()).all(|p| {
                ((p + 1)..f.len()).all(|q| {
                    let (x, y, z) = (f[p] & f[q], f[p] & s, f[q] & s);
                    !(x == y && y == z)
                })
            });
            if ok {
                f.push(s);
            }
        }
        out.push(f);
    }
    out
}

/// The sampled sweeps: ground set, uniformity, how many samples.
const SAMPLES: &[(u32, u32, usize)] = &[(8, 4, 4000), (9, 4, 4000), (10, 4, 2000), (9, 3, 4000)];

#[test]
fn the_enumeration_is_exhaustive_and_its_counts_are_pinned() {
    for &(g, b, want) in SWEEPS {
        let (count, stopped) = for_each_family(g, b, 10_000_000, |_| {});
        assert!(!stopped, "budget hit at g={g} b={b}");
        assert_eq!(count, want, "family count at g={g} b={b}");
    }
}

#[test]
fn every_member_meets_the_anchored_core_twice() {
    let mut checked = 0usize;
    let mut biggest_cover = 0usize;
    let (mut case_a, mut case_b) = (0usize, 0usize);
    let mut widest_core = 0u32;
    for &(g, b, _) in SWEEPS {
        let (_, stopped) = for_each_family(g, b, 10_000_000, |f| {
            if f.is_empty() {
                return;
            }
            let (core, m) = anchored_core(f);
            // The cover of the link has at most two members: three
            // pairwise disjoint ones would be a sunflower with empty core.
            assert!(m <= 2, "link cover of size {m} on {f:?}");
            biggest_cover = biggest_cover.max(m);
            if f.iter().any(|&a| (a & f[0]).count_ones() == 1) {
                case_b += 1;
            } else {
                case_a += 1;
            }
            widest_core = widest_core.max(core.count_ones());
            // The core is no wider than the proof says.
            assert!(
                core.count_ones() <= 4 * b - 3,
                "core {} wide at b={b} on {f:?}",
                core.count_ones()
            );
            // And every member meets it twice. This is the step the whole
            // bound rests on.
            for &a in f {
                assert!(
                    (a & core).count_ones() >= 2,
                    "member {a} meets core {core} once on {f:?}"
                );
            }
            checked += 1;
        });
        assert!(!stopped);
    }
    assert_eq!(checked, 96 + 388 + 14022 + 107171 + 5789 - 5);
    assert_eq!(checked, case_a + case_b);
    assert_eq!(biggest_cover, 2, "the two-member cover is attained");
    // Both branches of the case split are exercised. A sweep that hit
    // only one would leave half the proof unfalsified.
    assert_eq!((case_a, case_b), (7293, 120168), "case split coverage");
    // The core-width bound `4b - 3` is attained, at `b = 2`, where it is
    // five: anchor, second anchor minus the shared point, and a
    // two-member cover of a link of singletons.
    assert_eq!(widest_core, 5);
}

#[test]
fn the_anchored_support_bound_holds_on_every_enumerated_family() {
    for &(g, b, _) in SWEEPS {
        let (_, stopped) = for_each_family(g, b, 10_000_000, |f| {
            let n = f.len() as u32;
            let s = support(f).count_ones();
            assert!(
                s <= wide::anchored_support_bound(b, n),
                "support {s} beats {} at b={b} n={n} on {f:?}",
                wide::anchored_support_bound(b, n)
            );
            assert!(s <= wide::support_bound(b, n));
        });
        assert!(!stopped);
    }
}

#[test]
fn the_second_anchor_pays_off_exactly_above_four_b_minus_four() {
    for b in 2u32..8 {
        for n in 1u32..80 {
            let old = wide::support_bound(b, n);
            let new = wide::anchored_support_bound(b, n);
            if n > 4 * b - 4 {
                assert!(new < old, "b={b} n={n}: {new} vs {old}");
            } else {
                assert!(new >= old, "b={b} n={n}: {new} vs {old}");
            }
            assert_eq!(wide::least_support_bound(b, n), old.min(new));
        }
    }
    // The two numbers the development quotes.
    assert_eq!(wide::support_bound(4, 32), 97);
    assert_eq!(wide::anchored_support_bound(4, 32), 77);
    assert_eq!(wide::support_bound(3, 11), 23);
    assert_eq!(wide::anchored_support_bound(3, 11), 20);
    // And one below the crossover, where quoting the new bound would be
    // quoting the worse number.
    assert_eq!(wide::support_bound(4, 8), 25);
    assert_eq!(wide::anchored_support_bound(4, 8), 29);
}

#[test]
fn the_pair_degree_never_exceeds_g_of_b_minus_two() {
    // `g(2) <= 6` and `g(1) <= 2`, both proved in `coq/PureLink.v`;
    // `g(0) = 1` because a 0-uniform distinct family is one empty set.
    for &(g, b, _) in SWEEPS {
        let cap = match b {
            4 => 6,
            3 => 2,
            _ => 1,
        };
        let (_, stopped) = for_each_family(g, b, 10_000_000, |f| {
            for x in 0..g {
                for y in (x + 1)..g {
                    let q = (1u32 << x) | (1u32 << y);
                    let d = f.iter().filter(|&&a| a & q == q).count();
                    assert!(d <= cap, "pair degree {d} at b={b} on {f:?}");
                }
            }
        });
        assert!(!stopped);
    }
}

#[test]
fn six_is_attained_so_the_pair_degree_constant_is_not_slack() {
    // Two disjoint triangles: 2-uniform, six members, sunflower-free.
    // Coning them with a shared pair makes six 4-sets through that pair.
    let tri = masks(&[&[2, 3], &[3, 4], &[2, 4], &[5, 6], &[6, 7], &[5, 7]]);
    assert!(sunflower_free(&tri));
    assert_eq!(tri.len(), 6);
    let coned: Vec<u32> = tri.iter().map(|&t| t | 0b11).collect();
    assert!(sunflower_free(&coned));
    assert!(intersecting(&coned));
    assert!(coned.iter().all(|&a| a.count_ones() == 4));
    assert_eq!(coned.iter().filter(|&&a| a & 0b11 == 0b11).count(), 6);
}

#[test]
fn the_counting_ceiling_holds_and_forces_nine_points() {
    for &(g, b, _) in SWEEPS {
        if b != 4 {
            continue;
        }
        let (_, stopped) = for_each_family(g, b, 10_000_000, |f| {
            let s = support(f).count_ones() as u64;
            assert!(
                f.len() as u64 <= genprog::binom(s, 2),
                "{} members on {s} points",
                f.len()
            );
        });
        assert!(!stopped);
    }
    // The arithmetic `Support.thirty_two_four_sets_need_nine_points` runs.
    assert_eq!(genprog::binom(8, 2), 28);
    assert_eq!(genprog::binom(9, 2), 36);
    assert!(28 < 32 && 32 <= 36);
    // And the same number the generator-program ceiling computes, which
    // is an independent implementation of the same count.
    assert_eq!(genprog::least_ground(4, 32), 9);
    assert_eq!(genprog::link_bound(4, 9), 36);
    // The proof is two rungs behind the ladder, which refuted g = 10.
    assert!(9 < 11);
}

#[test]
fn the_twenty_seven_member_witness_has_covering_number_at_least_two() {
    let f = iota4();
    assert_eq!(f.len(), 27);
    assert!(f.iter().all(|&a| a.count_ones() == 4));
    assert!(intersecting(&f));
    assert!(sunflower_free(&f));
    // No common point: that is `Support.twenty_seven_four_sets_have_no_common_point`,
    // whose proof caps a family with one at `g(3) <= 26`.
    let common = f.iter().fold(u32::MAX, |a, &x| a & x);
    assert_eq!(common, 0, "the witness has a common point");
    // The bounds it satisfies, for the record.
    let s = support(&f).count_ones();
    assert_eq!(s, 9);
    assert!(s <= wide::least_support_bound(4, 27));
    assert!(f.len() as u64 <= genprog::binom(s as u64, 2));
}

#[test]
fn a_family_with_a_common_point_is_a_three_uniform_family_in_disguise() {
    // The content of `common_point_bounds_the_family`: coning a
    // 3-uniform sunflower-free family is a bijection onto the 4-uniform
    // intersecting families with a common point, so the cap is `g(3)`.
    let (count, stopped) = for_each_family(6, 4, 10_000_000, |f| {
        if f.is_empty() {
            return;
        }
        let common = f.iter().fold(u32::MAX, |a, &x| a & x);
        if common == 0 {
            return;
        }
        let p = 1u32 << common.trailing_zeros();
        let link: Vec<u32> = f.iter().map(|&a| a & !p).collect();
        assert!(link.iter().all(|&a| a.count_ones() == 3));
        assert!(sunflower_free(&link));
        // 26 is the proved cap; on seven points nothing comes close, and
        // that gap is the point — the bound is not tight here, it is
        // simply never violated.
        assert!(f.len() <= 26);
    });
    assert!(!stopped);
    assert_eq!(count, 5789);
}

#[test]
fn the_sampled_families_obey_both_bounds_where_the_sweep_cannot_reach() {
    // Not an exhaustion. The budget is the sample count, and the reason
    // the exhaustive sweep stops short is recorded rather than implied.
    assert!(SWEEP_LIMIT.contains("35333735"));
    let mut seen = 0usize;
    let mut widest = 0u32;
    let mut biggest = 0usize;
    for &(g, b, samples) in SAMPLES {
        for f in sampled_families(g, b, samples, 0x5f3a_9e17 ^ (g as u64) << 8 ^ b as u64) {
            assert!(intersecting(&f), "sampled family is not intersecting");
            assert!(sunflower_free(&f), "sampled family has a sunflower");
            let n = f.len() as u32;
            let s = support(&f).count_ones();
            assert!(s <= wide::support_bound(b, n));
            assert!(s <= wide::anchored_support_bound(b, n));
            let (core, m) = anchored_core(&f);
            assert!(m <= 2);
            assert!(core.count_ones() <= 4 * b - 3);
            for &a in &f {
                assert!((a & core).count_ones() >= 2, "member misses the core twice");
            }
            if b == 4 {
                assert!(f.len() as u64 <= genprog::binom(s as u64, 2));
            }
            widest = widest.max(s);
            biggest = biggest.max(f.len());
            seen += 1;
        }
    }
    assert_eq!(seen, 4000 + 4000 + 2000 + 4000);
    // The samples are big enough to be worth running: the largest
    // reached is recorded so a future change that quietly starts
    // producing two-member families fails here.
    assert!(biggest >= 10, "largest sampled family was only {biggest}");
    assert!(widest >= 8, "widest sampled support was only {widest}");
}

/// The `iota(3) = 10` witness, from `coq/Intersecting.v` via
/// `rust/tests/iota_structure.rs`.
fn iota3() -> Vec<u32> {
    masks(&[
        &[0, 1, 2],
        &[0, 1, 3],
        &[0, 2, 4],
        &[1, 3, 4],
        &[2, 3, 4],
        &[1, 2, 5],
        &[0, 3, 5],
        &[2, 3, 5],
        &[0, 4, 5],
        &[1, 4, 5],
    ])
}

#[test]
fn the_iota_three_witness_is_also_ekr_extremal() {
    // `docs/reading.md` A16, and `docs/papers/furedi78-rendered-pass.md`.
    // Furedi 1978 p. 186 builds his extremal family from "a 3-uniform,
    // intersecting set system H_1 with 10 members on a 6-element set".
    // Those are exactly these parameters. The identification with H_1 is
    // NOT made; what is checked is why the parameters are forced.
    let f = iota3();
    assert_eq!(f.len(), 10);
    assert!(f.iter().all(|&a| a.count_ones() == 3));
    assert_eq!(support(&f).count_ones(), 6);
    assert!(intersecting(&f));
    assert!(sunflower_free(&f));

    // Ten is half of C(6,3), so at `n = 2r` this is an EKR-extremal
    // intersecting family: it takes exactly one set from each of the ten
    // complementary pairs, and no intersecting family of 3-sets on six
    // points can be larger.
    assert_eq!(genprog::binom(6, 3), 20);
    assert_eq!(f.len() as u64, genprog::binom(6, 3) / 2);
    let all = 0b111111u32;
    for &a in &f {
        assert!(
            !f.contains(&(all & !a)),
            "the family contains a complementary pair, so it is not intersecting"
        );
    }
    let mut pairs: Vec<u32> = f.iter().map(|&a| a.min(all & !a)).collect();
    pairs.sort_unstable();
    pairs.dedup();
    assert_eq!(pairs.len(), 10, "one set from each complementary pair");

    // So at b = 3 the sunflower-free constraint is free: the largest
    // intersecting sunflower-free family of 3-sets is exactly as large as
    // the largest intersecting family of 3-sets on six points.
    //
    // The covering number is 3, the maximum possible at b = 3, which is
    // also what `Support.twenty_seven_four_sets_have_no_common_point`
    // measures one uniformity up.
    let mut tau = 4u32;
    for t in 1u32..4 {
        for c in 0..(1u32 << 6) {
            if c.count_ones() == t && f.iter().all(|&a| a & c != 0) {
                tau = tau.min(t);
            }
        }
    }
    assert_eq!(tau, 3);
}
