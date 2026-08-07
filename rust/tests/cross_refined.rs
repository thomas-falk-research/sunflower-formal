//! The objects and the numbers behind `coq/CrossRefined.v`.
//!
//! Four claims are checked here, all of them by construction and
//! exhaustive verification rather than by trusting the Coq side:
//!
//! 1. `g65` really is a 4-uniform intersecting Rao(5)-spread family of
//!    covering number at least 3 with 65 members, and it is *maximal* —
//!    nothing can be added on grounds up to 15. So the constant left open
//!    by `star_extremal_from_tau_three` at `m = 4` is at least 65.
//! 2. Four pairwise cross-intersecting 3-uniform Rao(5)-spread families
//!    can have 100 members between them, and 64 with no common point.
//!    §26.4 asked for 48; the route is dead in both its forms.
//! 3. `cross_pair_refined`'s number, `u·max(2u,r+1)·r^(u-2)`, against
//!    `cross_pair_bound`'s `(r-1)·r^(u-1)` and against the exhaustive
//!    truth at `u = 2`.
//! 4. `nonstar_three_bound`'s `max(3r+2,16)`, which branch binds where,
//!    and the decomposition of `hm16` that shows the remaining gap of one
//!    is the gap between the proved pair bound `2r+2` and the measured
//!    `2r+1`.

use sunflower_formal::spread::{is_rao_spread, Mask};

fn mask(points: &[u32]) -> Mask {
    points.iter().fold(0u32, |a, &p| a | (1u32 << p))
}

/// `CrossRefined.hm16`: the triple `{4,5,6}` together with the fifteen
/// triples `{12, i, y}` for `i` in `{4,5,6}` and `y` in `{7,...,11}`.
fn hm16() -> Vec<Mask> {
    let mut f = vec![mask(&[4, 5, 6])];
    for i in 4..7u32 {
        for y in 7..12u32 {
            f.push(mask(&[12, i, y]));
        }
    }
    f
}

/// `CrossRefined.g65`: `{0,1,2,3}` together with one copy of `hm16`
/// hung on each of its points.
fn g65() -> Vec<Mask> {
    let mut f = vec![mask(&[0, 1, 2, 3])];
    for x in 0..4u32 {
        for &t in hm16().iter() {
            f.push(t | (1u32 << x));
        }
    }
    f
}

/// The 25-member star: a point `10` over `K_{5,5}` on `{0..9}`. Five
/// regular, so every pair `{10,z}` has degree exactly 5 = `r^(3-2)`.
fn k55_star() -> Vec<Mask> {
    let mut f = Vec::new();
    for a in 0..5u32 {
        for b in 5..10u32 {
            f.push(mask(&[10, a, b]));
        }
    }
    f
}

fn intersecting(f: &[Mask]) -> bool {
    f.iter().all(|&a| f.iter().all(|&b| a & b != 0))
}

fn cross_intersecting(f: &[Mask], g: &[Mask]) -> bool {
    f.iter().all(|&a| g.iter().all(|&b| a & b != 0))
}

fn uniform(f: &[Mask], k: u32) -> bool {
    f.iter().all(|&a| a.count_ones() == k)
}

fn distinct(f: &[Mask]) -> bool {
    let mut s: Vec<Mask> = f.to_vec();
    s.sort_unstable();
    s.dedup();
    s.len() == f.len()
}

/// No two points meet every member.
fn tau_at_least_three(f: &[Mask], ground: u32) -> bool {
    (0..ground).all(|p| {
        (p..ground).all(|q| {
            let cover = (1u32 << p) | (1u32 << q);
            !f.iter().all(|&c| c & cover != 0)
        })
    })
}

/// No single point meets every member.
fn unpointed(f: &[Mask], ground: u32) -> bool {
    (0..ground).all(|p| !f.iter().all(|&c| c & (1u32 << p) != 0))
}

#[test]
fn the_sixty_five_member_witness_is_what_it_claims() {
    let g = g65();
    assert_eq!(g.len(), 65);
    assert!(uniform(&g, 4));
    assert!(distinct(&g));
    assert!(intersecting(&g));
    assert!(is_rao_spread(4, &g, 5, 13));
    assert!(tau_at_least_three(&g, 13));

    // the piece it is built from
    let a = hm16();
    assert_eq!(a.len(), 16);
    assert!(uniform(&a, 3));
    assert!(distinct(&a));
    assert!(intersecting(&a));
    assert!(is_rao_spread(3, &a, 5, 13));
    assert!(unpointed(&a, 13));

    // and it is a *maximal* such family: no 4-set at all can be added,
    // on any ground up to 15. A lower bound that cannot be nudged.
    for ground in 13..=15u32 {
        let extensions = (0u32..(1u32 << ground))
            .filter(|b| b.count_ones() == 4)
            .filter(|b| !g.contains(b))
            .filter(|&b| g.iter().all(|&c| c & b != 0))
            .filter(|&b| {
                let mut h = g.clone();
                h.push(b);
                is_rao_spread(4, &h, 5, ground)
            })
            .count();
        assert_eq!(extensions, 0, "ground {ground}");
    }
}

#[test]
fn the_four_family_route_of_section_twenty_six_four_is_dead() {
    // §26.4 asked for  sum |A_x| <= 48  over four pairwise
    // cross-intersecting 3-uniform Rao(5)-spread families.

    // Without the covering-number side condition: four copies of one
    // 25-member star. 100, more than twice what was asked for.
    let s = k55_star();
    assert_eq!(s.len(), 25);
    assert!(uniform(&s, 3));
    assert!(distinct(&s));
    assert!(is_rao_spread(3, &s, 5, 11));
    assert!(intersecting(&s)); // hence four copies cross-intersect
    assert_eq!(4 * s.len(), 100);
    assert!(4 * s.len() > 48);
    // it is pointed, which is what tau(G) >= 3 rules out
    assert!(!unpointed(&s, 11));

    // With it: four copies of `hm16`, no common point, 64.
    let a = hm16();
    assert!(unpointed(&a, 13));
    assert!(cross_intersecting(&a, &a));
    assert_eq!(4 * a.len(), 64);
    assert!(4 * a.len() > 48);

    // 48 was derived as 125 - (1 + 16 + 60); the layers are right, the
    // conclusion is not, because the layers cannot all be full at once.
    assert_eq!(125 - (1 + 16 + 60), 48);
}

#[test]
fn the_same_construction_is_exactly_extremal_at_uniformity_three() {
    // The `m = 3` analogue of `g65`: three copies of the triangle -- the
    // only intersecting graph that is not a star -- hung on the points of
    // one member. `rust/tests/tau_three.rs::max_tau_three` measures the
    // largest 3-uniform intersecting family of covering number >= 3
    // exhaustively as 10 on grounds 5 to 7, *without* imposing the Rao
    // condition; this construction attains 10 *with* it, so 10 is the
    // truth on both sides and the shape `g65` uses is exactly extremal one
    // uniformity down rather than merely a lower bound.
    let triangle = [(3u32, 4u32), (3, 5), (4, 5)];
    let mut g: Vec<Mask> = vec![mask(&[0, 1, 2])];
    for x in 0..3u32 {
        for &(p, q) in triangle.iter() {
            g.push(mask(&[x, p, q]));
        }
    }
    assert_eq!(g.len(), 1 + 3 * 3);
    assert_eq!(g.len(), 10);
    assert!(uniform(&g, 3));
    assert!(distinct(&g));
    assert!(intersecting(&g));
    assert!(is_rao_spread(3, &g, 4, 6));
    assert!(tau_at_least_three(&g, 6));

    // and the arithmetic that makes `g65` the same statement at m = 4
    let hm = hm16();
    assert_eq!(1 + 4 * hm.len(), 65);
}

/// `u * max(2u, r+1) * r^(u-2)`, the conclusion of `cross_pair_refined`.
fn refined(u: u64, r: u64) -> u64 {
    u * std::cmp::max(2 * u, r + 1) * r.pow((u - 2) as u32)
}

/// `(r-1) * r^(u-1)`, the conclusion of `cross_pair_bound`.
fn old_bound(u: u64, r: u64) -> u64 {
    (r - 1) * r.pow((u - 1) as u32)
}

#[test]
fn the_refined_bound_against_the_old_one_and_against_the_truth() {
    // the row that matters, u = 3 (which is m = 4) at r = 5
    assert_eq!(refined(3, 5), 90);
    assert_eq!(old_bound(3, 5), 100);

    // at u = 2 the exhaustive truth is 2r+1 (measured in
    // `cross_intersecting.rs`); the refined bound is 2r+2.
    for r in 4..=8u64 {
        assert_eq!(refined(2, r), 2 * r + 2);
        assert!(refined(2, r) > 2 * r + 1, "r={r}");
        assert!(refined(2, r) < old_bound(2, r), "r={r}");
    }

    // the two are incomparable: the refined bound is worse when 2u
    // dominates, which happens as soon as r is close to u. Both bounds
    // are a coefficient times r^(u-2); at u = 4, r = 6 the coefficients
    // are 32 = 4*max(8,7) against 30 = 6*5.
    assert_eq!(4 * std::cmp::max(2 * 4, 6 + 1), 32);
    assert_eq!(6 * (6 - 1), 30);
    assert_eq!(refined(4, 6), 1152);
    assert_eq!(old_bound(4, 6), 1080);

    // and the exact condition for the improvement, checked against the
    // formula rather than asserted
    for u in 2..=12u64 {
        for r in (u + 2)..=(u + 20) {
            let better = u * std::cmp::max(2 * u, r + 1) < r * (r - 1);
            assert_eq!(better, refined(u, r) < old_bound(u, r), "u={u} r={r}");
        }
    }
}

/// `CrossRefined.nonstar_three_bound`: the two-cover branch gives
/// `2*max(4,r+1) + r`, the covering-number-3 branch gives 16.
fn i2_three_bound(r: u64) -> u64 {
    std::cmp::max(2 * std::cmp::max(4, r + 1) + r, 16)
}

#[test]
fn the_non_star_bound_at_uniformity_three() {
    // the closed form the theorem states, against the two branches it is
    // assembled from
    for r in 3..=20u64 {
        assert_eq!(i2_three_bound(r), std::cmp::max(3 * r + 2, 16));
    }
    // which branch binds where: the covering-number-3 branch until r = 4,
    // the two-cover branch from r = 5 on
    for r in 3..=4u64 {
        assert_eq!(i2_three_bound(r), 16);
    }
    for r in 5..=20u64 {
        assert_eq!(i2_three_bound(r), 3 * r + 2);
    }

    // the row that matters
    assert_eq!(i2_three_bound(5), 17);

    // `hm16` is a witness one below it, so I2(3,5) is 16 or 17
    let a = hm16();
    assert_eq!(a.len(), 16);
    assert!(uniform(&a, 3));
    assert!(distinct(&a));
    assert!(intersecting(&a));
    assert!(is_rao_spread(3, &a, 5, 13));
    assert!(unpointed(&a, 13));
    assert!(a.len() as u64 <= i2_three_bound(5));
    assert_eq!(i2_three_bound(5), a.len() as u64 + 1);

    // and the gap of one is exactly the gap in the pair bound: the
    // two-cover branch is (pair bound at u = 2) + deg{p,q}, and at r = 5
    // that is 12 + 5 = 17 proved against 11 + 5 = 16 measured.
    assert_eq!(refined(2, 5) + 5, 17);
    assert_eq!((2 * 5 + 1) + 5, 16);

    // `cross_pair_bound` cannot prove anything here: 20 + 5 = 25 is the
    // star bound r^(m-1), i.e. no information about non-stars at all.
    assert_eq!(old_bound(2, 5) + 5, 25);
    assert_eq!(5u64.pow(2), 25);

    // hm16 realises the split the proof uses: cover {4,12}, tails of
    // sizes 5 and 5 with 5 members through both -- 5 + 5 + ... let the
    // decomposition speak for itself.
    let p = 4u32;
    let q = 12u32;
    assert!(a.iter().all(|&c| c & ((1 << p) | (1 << q)) != 0));
    let both = a.iter().filter(|&&c| c & (1 << p) != 0 && c & (1 << q) != 0).count();
    let only_p = a.iter().filter(|&&c| c & (1 << p) != 0 && c & (1 << q) == 0).count();
    let only_q = a.iter().filter(|&&c| c & (1 << p) == 0 && c & (1 << q) != 0).count();
    assert_eq!(both + only_p + only_q, 16);
    assert_eq!(both, 5); // = deg{4,12}, exactly r^(m-2)
    assert_eq!(only_p, 1); // the triple {4,5,6}
    assert_eq!(only_q, 10); // the star members through 5 or 6
    assert!(only_p + only_q <= refined(2, 5) as usize);
}

#[test]
fn star_saturation_is_sharp_at_its_threshold() {
    // `star_saturation`: a family pointed at `w` with more than
    // `u*r^(u-2)` members forces every cross-partner into the same star.
    // At u = 2, r = 5 the threshold is 2, and a pointed family of
    // exactly 2 edges does have a partner outside its star: the star at
    // 0 given by {0,1} and {0,2} is met by {1,2}, which misses 0.
    let a: Vec<Mask> = vec![mask(&[0, 1]), mask(&[0, 2])];
    let b: Vec<Mask> = vec![mask(&[1, 2])];
    assert_eq!(a.len(), 2 * 5u32.pow(0) as usize); // = u * r^(u-2)
    assert!(cross_intersecting(&a, &b));
    assert!(is_rao_spread(2, &a, 5, 3));
    assert!(!unpointed(&a, 3));
    assert!(b.iter().any(|&f| f & 1 == 0)); // the partner escapes the star

    // one edge more and it cannot: a pointed family of 3 edges at 0
    // forces every partner through 0, because a 2-set cannot cover 3
    // disjoint leaves.
    let a3: Vec<Mask> = vec![mask(&[0, 1]), mask(&[0, 2]), mask(&[0, 3])];
    assert!(is_rao_spread(2, &a3, 5, 4));
    let partners: Vec<Mask> = (0u32..(1u32 << 4))
        .filter(|e| e.count_ones() == 2)
        .filter(|&e| a3.iter().all(|&c| c & e != 0))
        .collect();
    assert!(!partners.is_empty());
    assert!(partners.iter().all(|&e| e & 1 != 0), "{partners:?}");

    // at u = 3, r = 5 the threshold is 3*5 = 15, and `hm16` has 16
    // members but is not pointed, so it is not a counterexample; the
    // 25-member star is pointed and above the threshold, and every
    // 3-set meeting all of it does contain its centre.
    assert_eq!(3 * 5u32.pow(1), 15);
    let s = k55_star();
    let escapes = (0u32..(1u32 << 11))
        .filter(|e| e.count_ones() == 3)
        .filter(|&e| e & (1u32 << 10) == 0)
        .filter(|&e| s.iter().all(|&c| c & e != 0))
        .count();
    assert_eq!(escapes, 0);
}
