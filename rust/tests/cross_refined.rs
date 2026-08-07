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
//! 4. `nonstar_three_bound`'s `max(3r+1,16)`, which branch binds where,
//!    the decomposition of `hm16` that meets it exactly, and the `r = 3`
//!    row that shows `cross_pair_two_exact`'s `r >= 4` threshold is an
//!    artefact of its case analysis.

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
/// `cross_pair_two_exact`'s `2r+1` plus the pair degree `r`, the
/// covering-number-3 branch gives 16.
fn i2_three_bound(r: u64) -> u64 {
    std::cmp::max((2 * r + 1) + r, 16)
}

#[test]
fn the_non_star_bound_at_uniformity_three() {
    // the closed form the theorem states, against the two branches it is
    // assembled from
    for r in 4..=20u64 {
        assert_eq!(i2_three_bound(r), std::cmp::max(3 * r + 1, 16));
    }
    // which branch binds where: the covering-number-3 branch at r = 4,
    // the two-cover branch from r = 5 on, and they are equal at r = 5
    assert_eq!(i2_three_bound(4), 16);
    assert_eq!(3 * 4 + 1, 13);
    assert_eq!(i2_three_bound(5), 16);
    assert_eq!(3 * 5 + 1, 16);
    for r in 6..=20u64 {
        assert_eq!(i2_three_bound(r), 3 * r + 1);
    }

    // and `hm16` attains it, so I2(3,5) = 16 exactly
    let a = hm16();
    assert_eq!(a.len(), 16);
    assert!(uniform(&a, 3));
    assert!(distinct(&a));
    assert!(intersecting(&a));
    assert!(is_rao_spread(3, &a, 5, 13));
    assert!(unpointed(&a, 13));
    assert_eq!(a.len() as u64, i2_three_bound(5));

    // `cross_pair_bound` cannot prove anything here: 20 + 5 = 25 is the
    // star bound r^(m-1), i.e. no information about non-stars at all;
    // `cross_pair_refined` gives 12 + 5 = 17, one too many.
    assert_eq!(old_bound(2, 5) + 5, 25);
    assert_eq!(5u64.pow(2), 25);
    assert_eq!(refined(2, 5) + 5, 17);

    // hm16 realises the split exactly: cover {4,12}, one member through 4
    // only, ten through 12 only, five through both -- 11 + 5, where 11 is
    // `cross_pair_two_exact`'s 2r+1 and 5 is the pair degree r^(m-2).
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
    assert_eq!(only_p + only_q, 2 * 5 + 1); // the tails, at the exact bound
}

#[test]
fn the_exact_pair_bound_at_uniformity_two() {
    // `cross_pair_two_exact`: 2r+1, proved for r >= 3. It matches the
    // exhaustive truth measured in `cross_intersecting.rs` at r = 4,5,6,
    // where `cross_pair_refined` is one above and `cross_pair_bound` is a
    // factor of about r/2 above.
    for r in 4..=6u64 {
        assert_eq!(refined(2, r), 2 * r + 2);
        assert!(2 * r + 1 < refined(2, r));
        assert!(refined(2, r) < old_bound(2, r));
    }

    // r = 3 is the last row it covers, and it is attained: 7 on 5, 6 and
    // 7 points, exhaustively.
    assert_eq!(2 * 3 + 1, 7);
    for n in 5..=7u32 {
        assert_eq!(max_cross_pair_r(n, 3), 7, "ground {n}");
    }

    // and r = 2 is the first row it does not, because there the statement
    // is false: `CrossRefined.cross_pair_two_exact_needs_three` exhibits
    // two disjoint edges against the four crossing edges, 2 + 4 = 6
    // against 2r+1 = 5. Here is the same pair, checked independently.
    let c2a: Vec<Mask> = vec![mask(&[0, 2]), mask(&[1, 3])];
    let c2b: Vec<Mask> = vec![mask(&[0, 1]), mask(&[0, 3]), mask(&[1, 2]), mask(&[2, 3])];
    assert!(uniform(&c2a, 2) && uniform(&c2b, 2));
    assert!(distinct(&c2a) && distinct(&c2b));
    assert!(is_rao_spread(2, &c2a, 2, 4));
    assert!(is_rao_spread(2, &c2b, 2, 4));
    assert!(cross_intersecting(&c2a, &c2b));
    assert_eq!(c2a.len() + c2b.len(), 6);
    assert!(c2a.len() + c2b.len() > 2 * 2 + 1);
    // and 6 is the exhaustive maximum at r = 2, so nothing weaker than
    // 2r+2 holds there
    for n in 5..=7u32 {
        assert_eq!(max_cross_pair_r(n, 2), 6, "ground {n}");
    }

    // The neither-pointed case is where the threshold lives: the greedy
    // tree at depth two gives four edges each, and 8 exceeds 2r+1 until
    // r = 4. `triangle_bound` and `disjoint_squeeze` are what bring it
    // down to 7 at r = 3.
    assert!(8 > 2 * 3 + 1);
    assert!(8 <= 2 * 4 + 1);
    // and the neither-pointed configurations really do cap at 6
    for n in 5..=6u32 {
        assert_eq!(max_cross_pair_unpointed(n, 6), 6, "ground {n}");
    }
}

/// Exhaustive maximum of `|A| + |B|` over nonempty cross-intersecting
/// Rao(`r`) graphs on `n` points, confined as the proof confines it: an
/// edge of `B` is relabelled `{0,1}` and every edge of `A` meets it.
fn max_cross_pair_r(n: u32, r: usize) -> usize {
    let edges: Vec<(u32, u32)> = (0..n).flat_map(|a| (a + 1..n).map(move |b| (a, b))).collect();
    let meets = |e: (u32, u32), f: (u32, u32)| e.0 == f.0 || e.0 == f.1 || e.1 == f.0 || e.1 == f.1;
    let rao = |g: &[(u32, u32)]| {
        (0..n).all(|v| g.iter().filter(|e| e.0 == v || e.1 == v).count() <= r)
    };
    let anchor: Vec<(u32, u32)> = edges
        .iter()
        .copied()
        .filter(|&(a, b)| a == 0 || a == 1 || b == 0 || b == 1)
        .collect();
    let mut best = 0usize;
    for mask in 0u32..(1u32 << anchor.len()) {
        let a: Vec<(u32, u32)> = (0..anchor.len())
            .filter(|i| mask >> i & 1 == 1)
            .map(|i| anchor[i])
            .collect();
        if a.is_empty() || !rao(&a) {
            continue;
        }
        let pool: Vec<(u32, u32)> = edges
            .iter()
            .copied()
            .filter(|&e| a.iter().all(|&f| meets(e, f)))
            .collect();
        if !pool.contains(&(0, 1)) {
            continue;
        }
        let rest: Vec<(u32, u32)> = pool.iter().copied().filter(|&e| e != (0, 1)).collect();
        let mut bb = 1usize;
        for m2 in 0u32..(1u32 << rest.len()) {
            if 1 + m2.count_ones() as usize <= bb {
                continue;
            }
            let mut b = vec![(0u32, 1u32)];
            b.extend((0..rest.len()).filter(|i| m2 >> i & 1 == 1).map(|i| rest[i]));
            if rao(&b) {
                bb = b.len();
            }
        }
        best = best.max(a.len() + bb);
    }
    best
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

/// Exhaustive maximum of `|A| + |B|` over cross-intersecting Rao(`r`)
/// graphs on `n` points with **neither side pointed** -- the case the
/// `r = 3` row turns on. No anchoring: both sides are enumerated.
fn max_cross_pair_unpointed(n: u32, r: usize) -> usize {
    let edges: Vec<(u32, u32)> = (0..n).flat_map(|a| (a + 1..n).map(move |b| (a, b))).collect();
    let meets = |e: (u32, u32), f: (u32, u32)| e.0 == f.0 || e.0 == f.1 || e.1 == f.0 || e.1 == f.1;
    let rao = |g: &[(u32, u32)]| {
        (0..n).all(|v| g.iter().filter(|e| e.0 == v || e.1 == v).count() <= r)
    };
    let pointed = |g: &[(u32, u32)]| (0..n).any(|v| g.iter().all(|e| e.0 == v || e.1 == v));
    let mut best = 0usize;
    for ma in 1u32..(1u32 << edges.len()) {
        let a: Vec<(u32, u32)> = (0..edges.len())
            .filter(|i| ma >> i & 1 == 1)
            .map(|i| edges[i])
            .collect();
        if pointed(&a) || !rao(&a) || a.len() + edges.len() <= best {
            continue;
        }
        let pool: Vec<(u32, u32)> = edges
            .iter()
            .copied()
            .filter(|&f| a.iter().all(|&e| meets(e, f)))
            .collect();
        for mb in 1u32..(1u32 << pool.len()) {
            let b: Vec<(u32, u32)> = (0..pool.len())
                .filter(|i| mb >> i & 1 == 1)
                .map(|i| pool[i])
                .collect();
            if pointed(&b) || !rao(&b) {
                continue;
            }
            best = best.max(a.len() + b.len());
        }
    }
    best
}
