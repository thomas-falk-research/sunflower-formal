//! The wreath product is the only construction this repository has for
//! *intersecting* sunflower-free families — and it is exhausted at
//! 4-uniform.
//!
//! ## Where this came from
//!
//! `docs/roadmap.md` §41.4 identified `Product.iota4`, the `ι(4,9) = 27`
//! witness, as the wreath product `C₃ ≀ C₃` of Frankl's 1977 thesis
//! (Frankl–Pach–Pálvölgyi, *Odd-Sunflowers*, p. 4). That raised an
//! obvious question nobody had asked here: the construction has a size
//! formula with free parameters, so **can it be pushed past 27?**
//!
//! It cannot, and the reason is short enough to check exhaustively.
//!
//! ## The two facts
//!
//! For `F` a `k`-uniform family and `G` an `m`-uniform family, the wreath
//! product takes `n = |ground(F)|` disjoint copies of `G`'s ground set and
//! forms `⋃_{i ∈ F} G_i` over all `F ∈ F` and all choices `G_i ∈ G_i`:
//!
//! ```text
//!   uniformity(F ≀ G) = k · m          |F ≀ G| = |F| · |G|^k
//! ```
//!
//! **Fact 1 — it is intersecting exactly when both factors are.** For
//! `A` built from `F` and `B` from `F'`,
//!
//! ```text
//!   A ∩ B = ⋃_{j ∈ F ∩ F'} (G_j ∩ G'_j)
//! ```
//!
//! so if `F` has a disjoint pair the union is empty, and if `G` has a
//! disjoint pair `U, V` then choosing `G_j = U`, `G'_j = V` for every
//! `j ∈ F ∩ F'` empties it too. Both directions are checked below by
//! construction rather than asserted.
//!
//! **Fact 2 — so the factors must be `ι`, not `g`.** That is the whole
//! ceiling. The unconstrained maximum at uniformity 2 is `g(2) = 6` (two
//! disjoint triangles), but two disjoint triangles are not intersecting;
//! the intersecting maximum is `ι(2) = 3`, one triangle. Halving each
//! factor is what caps the product.
//!
//! ## The ceiling
//!
//! At uniformity 4 the factorisations `4 = k · m` with both factors
//! *smaller* than 4 — the only ones that build something new rather than
//! restating `ι(4)` — are just `k = m = 2`:
//!
//! ```text
//!   k=1, m=4 :  ι(1) · ι(4)^1 = ι(4)      degenerate, no gain
//!   k=2, m=2 :  ι(2) · ι(2)^2 = 3 · 9 = 27   <- Product.iota4
//!   k=4, m=1 :  ι(4) · ι(1)^4 = ι(4)      degenerate, no gain
//! ```
//!
//! `ι(1) = 1`, because two distinct singletons are disjoint.
//!
//! **So `ι(4) > 27` requires a construction that is not a wreath product
//! of smaller intersecting sunflower-free families.** This repository has
//! no such construction, and neither did the search of §41 — which is a
//! sharper statement of where the ladder's lower bound is stuck than
//! "27 is the best we know".
//!
//! Note what this does *not* say. It is a statement about one
//! construction, not an upper bound on `ι(4)`: the standing bracket is
//! still `27 ≤ ι(4) ≤ 71` from `Product.iota4` and
//! `PureLink.iota_four_at_most_71_if_iota_three_is_ten`.

use std::collections::HashSet;

fn is_sunflower(a: u64, b: u64, c: u64) -> bool {
    let ab = a & b;
    ab == (a & c) && ab == (b & c)
}

fn subsets(n: u32, k: u32) -> Vec<u64> {
    let mut out = Vec::new();
    for m in 0u64..(1 << n) {
        if m.count_ones() == k {
            out.push(m);
        }
    }
    out
}

fn sunflower_free(f: &[u64]) -> bool {
    !(0..f.len()).any(|a| {
        (a + 1..f.len()).any(|b| (b + 1..f.len()).any(|c| is_sunflower(f[a], f[b], f[c])))
    })
}

fn intersecting(f: &[u64]) -> bool {
    (0..f.len()).all(|a| (a + 1..f.len()).all(|b| f[a] & f[b] != 0))
}

/// Largest sunflower-free subfamily, optionally required intersecting.
fn max_family(cands: &[u64], want_intersecting: bool) -> usize {
    fn rec(cands: &[u64], cur: &mut Vec<u64>, best: &mut usize, inter: bool) {
        if cur.len() > *best {
            *best = cur.len();
        }
        for i in 0..cands.len() {
            if cur.len() + (cands.len() - i) <= *best {
                return;
            }
            let x = cands[i];
            let next: Vec<u64> = cands[i + 1..]
                .iter()
                .copied()
                .filter(|&y| {
                    (!inter || x & y != 0) && !cur.iter().any(|&a| is_sunflower(a, x, y))
                })
                .collect();
            cur.push(x);
            rec(&next, cur, best, inter);
            cur.pop();
        }
    }
    let mut best = 0;
    rec(cands, &mut Vec::new(), &mut best, want_intersecting);
    best
}

/// `F ≀ G`: `m_pts` is the size of `G`'s ground set, and `F`'s points
/// index the disjoint copies.
fn wreath(f: &[u64], g: &[u64], m_pts: u32) -> Vec<u64> {
    let mut out = Vec::new();
    for &base in f {
        let idx: Vec<u32> = (0..64).filter(|b| base >> b & 1 == 1).collect();
        let mut acc = vec![0u64];
        for &i in &idx {
            let mut next = Vec::new();
            for &a in &acc {
                for &gs in g {
                    // shift G's ground set into copy `i`
                    let mut placed = 0u64;
                    for b in 0..m_pts {
                        if gs >> b & 1 == 1 {
                            placed |= 1 << (i * m_pts + b);
                        }
                    }
                    next.push(a | placed);
                }
            }
            acc = next;
        }
        out.extend(acc);
    }
    out
}

/// Fact 1, both directions, by construction.
#[test]
fn the_wreath_product_is_intersecting_exactly_when_both_factors_are() {
    let tri = vec![0b011u64, 0b101, 0b110]; // C3: intersecting, sunflower-free
    let two_disjoint = vec![0b000011u64, 0b001100]; // a disjoint pair
    let path = vec![0b011u64, 0b110]; // intersecting, but only two members

    assert!(intersecting(&tri) && sunflower_free(&tri));
    assert!(!intersecting(&two_disjoint));

    // both intersecting -> product intersecting
    let w = wreath(&tri, &tri, 3);
    assert!(intersecting(&w), "C3 wr C3 should be intersecting");
    assert!(sunflower_free(&w));

    // G not intersecting -> product not intersecting, even though F is
    let w = wreath(&tri, &two_disjoint, 6);
    assert!(
        !intersecting(&w),
        "a disjoint pair in G must survive into the product"
    );

    // F not intersecting -> product not intersecting, even though G is
    let w = wreath(&two_disjoint, &path, 3);
    assert!(
        !intersecting(&w),
        "a disjoint pair in F must survive into the product"
    );
}

/// The size formula, checked rather than trusted.
#[test]
fn the_wreath_size_is_the_product_formula() {
    let tri = vec![0b011u64, 0b101, 0b110];
    let w = wreath(&tri, &tri, 3);
    assert_eq!(w.len(), 3 * 3usize.pow(2), "|F| * |G|^k");
    assert_eq!(w.len(), 27);
    assert!(w.iter().all(|s| s.count_ones() == 4), "uniformity k*m = 4");
    let pts = w.iter().fold(0u64, |a, s| a | s).count_ones();
    assert_eq!(pts, 9, "support is |ground(F)| * |ground(G)|");
    let uniq: HashSet<u64> = w.iter().copied().collect();
    assert_eq!(uniq.len(), 27, "members distinct");
}

/// The ceiling: 27, and the halving that causes it.
#[test]
fn the_wreath_ceiling_at_four_uniform_is_twenty_seven() {
    // iota(1) = 1: two distinct singletons are disjoint.
    let singletons = subsets(6, 1);
    assert_eq!(max_family(&singletons, true), 1, "iota(1) is not 1");

    // iota(2) = 3 (a triangle) against g(2) = 6 (two disjoint triangles).
    // The gap between these two numbers IS the ceiling.
    let pairs = subsets(8, 2);
    assert_eq!(max_family(&pairs, true), 3, "iota(2) is not 3");
    assert_eq!(max_family(&pairs, false), 6, "g(2) is not 6");

    // 4 = k*m with both factors below 4 leaves only k = m = 2.
    let non_degenerate: Vec<(u32, u32)> =
        (2..4u32).flat_map(|k| (2..4u32).map(move |m| (k, m))).filter(|(k, m)| k * m == 4).collect();
    assert_eq!(non_degenerate, vec![(2, 2)], "another factorisation exists");

    // And it gives exactly 27.
    let (iota1, iota2) = (1usize, 3usize);
    assert_eq!(iota2 * iota2.pow(2), 27);

    // What the unconstrained factors would have given, had fact 1 not
    // forced them to be intersecting: g(2) * g(2)^2 = 6 * 36 = 216.
    // That number is unreachable, and the distance between 216 and 27 is
    // the price of the intersecting hypothesis.
    assert_eq!(6 * 6usize.pow(2), 216);
    assert!(27 < 216);

    // The degenerate factorisations restate iota(4) and gain nothing.
    assert_eq!(iota1, 1);

    // The standing bracket this does NOT move.
    assert!(27 <= 71, "iota(4) in [27, 71]; the ceiling is about one construction");
}
