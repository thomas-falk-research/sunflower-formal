//! What the literature does and does not say about the *support* of a
//! sunflower-free family, checked first-hand.
//!
//! `docs/roadmap.md` §37.6 and `docs/reading.md` A22 recorded a search
//! for a published bound on the number of points an extremal
//! intersecting sunflower-free 4-uniform family can use. A second,
//! independent search came back with three claims about the primary
//! sources. Every page of all three sources was rendered to an image and
//! read (`docs/reading.md` A24); this file checks the parts that are
//! arithmetic or finite search rather than citation.
//!
//! ## 1. Frankl–Wang `|G(n,4)|` is linear, not cubic
//!
//! A22 said the `k=4, τ=3` maximum "grows like `Θ(n³)`". That is wrong.
//! Frankl–Wang arXiv:2207.05487v3 eq. (1.3) gives
//!
//! ```text
//!   |G(n,k)| = (k² − k + 1)·C(n−3, k−3) + O(C(n−4, k−4))
//! ```
//!
//! and at `k = 4` the leading binomial is `C(n−3, 1) = n−3`, so the
//! growth is **linear**: `13(n−3) + O(1)`. The four `C(·, k−1)` terms of
//! eq. (1.4) carry coefficients `+1 −1 −1 +1`, which sum to zero, so the
//! `n³/6` that A22 read off the first term cancels. Exactly,
//!
//! ```text
//!   |G(n,4)| = 13n − 69      for n ≥ 8.
//! ```
//!
//! A22's *conclusion* is unaffected — `13n − 69 ≥ 35 > 32` already at
//! `n = 8` — so the refutation of §37.5 stands. Only the rate was wrong.
//!
//! ## 2. The Frankl–Pach–Pálvölgyi tree family, in its intersecting reading
//!
//! *Odd-Sunflowers* (arXiv:2310.16701v2), p. 7, defines `g_v(k)` as
//! **the size of the base set** — the support — of the largest
//! sunflower-free `k`-uniform family, says *"We could not find any papers
//! studying the quantity `g_v(k)`"*, and gives `g_v(k) ≥ 2^k − 1` via the
//! root-to-leaf paths of a rooted binary tree of depth `k`. Conjecture 14
//! asks for `g_v(k) ≤ c^k`, and p. 8 credits Zach Hunter with the
//! argument that it is **equivalent to the Erdős–Rado conjecture**.
//!
//! **All of that was already in this repository** — see `docs/references.md`
//! on [FPPTZ24], and `docs/reading.md` B14 for Hunter's answer read in
//! full. `rust/tests/ground_set.rs` already checks the construction to
//! `k = 6`. This file does not restate it.
//!
//! What is new is a distinction between two readings of that one
//! sentence, because they are different families:
//!
//! ```text
//!   paths as EDGE sets    2^k members      2^(k+1) − 2 points   NOT intersecting
//!   paths as VERTEX sets  2^(k−1) members  2^k − 1 points       intersecting
//! ```
//!
//! `construction::tree_paths` is the edge reading, and it is **not
//! intersecting**: two paths through different children of the root share
//! no edge. At `k = 4` it has 64 disjoint pairs out of 120. So the
//! witness this repository has had since the `GroundBounded` work says
//! nothing about `ι`, which is the intersecting object.
//!
//! The vertex reading does. Two paths always share the root *vertex*, so
//! it is intersecting, and at `k = 4` it is a 4-uniform **intersecting**
//! sunflower-free family on **15** points. Nine was never the ceiling.
//!
//! The vertex reading is also the paper's: it reproduces `2^k − 1`
//! exactly, where the edge reading gives `2^(k+1) − 2` and overshoots the
//! figure FPP state. `ground_set.rs`'s family is the stronger support
//! witness; this one is the paper's construction. Neither test should be
//! cited for the other's claim.
//!
//! ## 3. `Product.iota4` is a maximal intersecting family
//!
//! Erdős–Lovász's `N(k)` is the largest number of points in a *maximal*
//! intersecting family of `k`-sets — one satisfying `F = F^⊤`, the
//! "maximal `k`-cliques". Majumder arXiv:1402.7158v1 p. 3 records that
//! Hanson and Toft (*Ars Combinatoria* **16A** (1983), 205–216) proved
//! `N(k) = 2k − 2 + ½C(2k−2, k−1)` exactly for `2 ≤ k ≤ 4`, so
//! `N(4) = 16`.
//!
//! Whether that bears on the ladder turns on whether an extremal
//! intersecting sunflower-free family *is* such a family. For
//! `Product.iota4` it is, and this file proves it: `τ(iota4) = 4 = k`,
//! and no 4-set outside `iota4` blocks `iota4`. The second check is
//! finite over the whole universe of sets, not just over `[9]`, because
//! `τ = 4` means a 4-set using any point outside `[9]` would need a
//! blocking 3-set inside `[9]`, and there is none.
//!
//! This does not close the ladder — a maximum-size intersecting
//! sunflower-free family need not be maximal *as an intersecting family*,
//! since the set one would add may complete a sunflower — but it is a
//! genuine bridge to that literature, and it is the reason the coincidence
//! in §4 below is worth recording rather than dismissing.
//!
//! ## 4. The 27 is also a covering-number number
//!
//! Frankl–Wang p. 2 quotes, for `f(n,k,k)` (intersecting, `τ ≥ k`), the
//! Erdős–Lovász bracket `⌊k!(e−1)⌋ ≤ f(n,k,k) ≤ k^k` and the improved
//! lower bound `(k/2 + 1)^(k−1)` for even `k` from Frankl–Ota–Tokushige
//! (*JCTA* **74** (1996), 33–42). At `k = 4` that lower bound is
//! `3³ = 27` — the value of `ι(4,9)`, attained by a family this file
//! shows has `τ = 4`. Recorded as an observation, not a theorem: the two
//! problems agree on 27 at `k = 4`, and `iota4` is admissible for both.

use std::collections::HashSet;

/// Frankl–Wang eq. (1.4), the exact size of `G(n,k)`.
fn fw_exact(n: i64, k: i64) -> i64 {
    fn binom(n: i64, k: i64) -> i64 {
        if k < 0 || n < k {
            return 0;
        }
        (0..k).fold(1i64, |acc, i| acc * (n - i) / (i + 1))
    }
    binom(n - 1, k - 1) - binom(n - k, k - 1) - binom(n - k - 1, k - 1)
        + binom(n - 2 * k, k - 1)
        + binom(n - k - 2, k - 3)
        + 3
}

/// `Product.iota4`: the Abbott–Hanson–Sauer family, `ι(4,9) = 27`.
fn iota4() -> Vec<u32> {
    const ROWS: [[u32; 4]; 27] = [
        [0, 1, 2, 3], [0, 1, 2, 4], [0, 1, 3, 4], [0, 2, 3, 5], [1, 2, 3, 5],
        [0, 2, 4, 5], [1, 2, 4, 5], [0, 3, 4, 5], [1, 3, 4, 5],
        [0, 1, 6, 7], [2, 3, 6, 7], [2, 4, 6, 7], [3, 4, 6, 7], [0, 5, 6, 7], [1, 5, 6, 7],
        [0, 1, 6, 8], [2, 3, 6, 8], [2, 4, 6, 8], [3, 4, 6, 8], [0, 5, 6, 8], [1, 5, 6, 8],
        [0, 1, 7, 8], [2, 3, 7, 8], [2, 4, 7, 8], [3, 4, 7, 8], [0, 5, 7, 8], [1, 5, 7, 8],
    ];
    ROWS.iter().map(|r| r.iter().fold(0u32, |m, &p| m | 1 << p)).collect()
}

fn is_sunflower(a: u64, b: u64, c: u64) -> bool {
    let ab = a & b;
    ab == (a & c) && ab == (b & c)
}

/// Root-to-leaf paths of a rooted binary tree on `k` levels of vertices,
/// heap-numbered `1 ..= 2^k − 1`. Frankl–Pach–Pálvölgyi p. 7.
fn tree_paths(k: u32) -> Vec<u64> {
    let n = (1u64 << k) - 1;
    let mut out = Vec::new();
    fn walk(node: u64, n: u64, acc: u64, out: &mut Vec<u64>) {
        let acc = acc | 1 << node;
        if 2 * node > n {
            out.push(acc);
            return;
        }
        walk(2 * node, n, acc, out);
        walk(2 * node + 1, n, acc, out);
    }
    walk(1, n, 0, &mut out);
    out
}

/// A22 said `Θ(n³)`. It is `Θ(n)`, and exactly `13n − 69`.
#[test]
fn the_covering_number_three_maximum_is_linear_in_n() {
    // The published spot value this repository already checked by rebuilding
    // the construction (`frankl_wang.rs`).
    assert_eq!(fw_exact(11, 4), 74);

    // Exactly linear, from n = 2k = 8 up.
    for n in 8..=400i64 {
        assert_eq!(
            fw_exact(n, 4),
            13 * n - 69,
            "|G({n},4)| is not 13n - 69"
        );
    }

    // First differences are constant: the signature of linear growth, and
    // the direct refutation of the cubic reading.
    let d: HashSet<i64> = (9..=400i64).map(|n| fw_exact(n, 4) - fw_exact(n - 1, 4)).collect();
    assert_eq!(d.len(), 1, "growth is not linear: differences {d:?}");
    assert!(d.contains(&13), "slope is not 13: {d:?}");

    // eq. (1.3)'s leading coefficient, k² − k + 1 at k = 4.
    assert_eq!(4 * 4 - 4 + 1, 13);

    // The conclusion A22 drew survives the correction: still above 32,
    // already at the smallest admissible n.
    assert!(fw_exact(8, 4) > 32, "the refutation of §37.5 needs this");
    assert_eq!(fw_exact(8, 4), 35);
}

/// `g_v(k) ≥ 2^k − 1`, and the witness is intersecting.
#[test]
fn the_tree_family_is_intersecting_sunflower_free_on_two_to_the_k_minus_one_points() {
    for k in 2..=6u32 {
        let fam = tree_paths(k);

        // 2^(k−1) members, each of size k.
        assert_eq!(fam.len(), 1 << (k - 1), "member count at k={k}");
        assert!(fam.iter().all(|s| s.count_ones() == k), "not {k}-uniform");
        let uniq: HashSet<u64> = fam.iter().copied().collect();
        assert_eq!(uniq.len(), fam.len(), "members not distinct at k={k}");

        // Intersecting: every root-to-leaf path contains the root.
        for i in 0..fam.len() {
            for j in i + 1..fam.len() {
                assert!(fam[i] & fam[j] != 0, "disjoint pair at k={k}");
            }
        }

        // Sunflower-free.
        for i in 0..fam.len() {
            for j in i + 1..fam.len() {
                for l in j + 1..fam.len() {
                    assert!(
                        !is_sunflower(fam[i], fam[j], fam[l]),
                        "3-sunflower at k={k}"
                    );
                }
            }
        }

        // The support is exactly 2^k − 1, which is the paper's bound.
        let support = fam.iter().fold(0u64, |a, s| a | s).count_ones();
        assert_eq!(support as u64, (1u64 << k) - 1, "support at k={k}");
    }

    // At k = 4 this is the concrete statement that matters for the ladder:
    // fifteen points, not nine.
    let fam = tree_paths(4);
    assert_eq!(fam.len(), 8);
    assert_eq!(fam.iter().fold(0u64, |a, s| a | s).count_ones(), 15);
    assert!(15 > 9, "iota4's nine points are not the largest support");
}

/// The edge reading — the family `ground_set.rs` already had — is **not**
/// intersecting, which is why the vertex reading was worth building.
#[test]
fn the_edge_reading_of_the_tree_family_is_not_intersecting() {
    use sunflower_formal::construction::{tree_paths as edge_paths, tree_paths_ground};

    for k in 2..=6u32 {
        let e = edge_paths(k);
        // The counts `ground_set.rs` asserts, restated so a drift is visible.
        assert_eq!(e.len(), 1usize << k, "edge member count at k={k}");
        assert_eq!(tree_paths_ground(k), (1u32 << (k + 1)) - 2);

        // And the property it does not have.
        let disjoint = (0..e.len())
            .flat_map(|i| (i + 1..e.len()).map(move |j| (i, j)))
            .filter(|&(i, j)| e[i] & e[j] == 0)
            .count();
        assert!(disjoint > 0, "edge reading is intersecting at k={k}");

        // The vertex reading, on the same k, has none.
        let v = tree_paths(k);
        let vd = (0..v.len())
            .flat_map(|i| (i + 1..v.len()).map(move |j| (i, j)))
            .filter(|&(i, j)| v[i] & v[j] == 0)
            .count();
        assert_eq!(vd, 0, "vertex reading is not intersecting at k={k}");
    }

    // The concrete figures quoted in docs/reading.md A24d.
    let e = edge_paths(4);
    let pairs = e.len() * (e.len() - 1) / 2;
    let disjoint = (0..e.len())
        .flat_map(|i| (i + 1..e.len()).map(move |j| (i, j)))
        .filter(|&(i, j)| e[i] & e[j] == 0)
        .count();
    assert_eq!((disjoint, pairs), (64, 120));

    // The edge reading overshoots the paper's stated 2^k − 1; the vertex
    // reading reproduces it. Both are true statements about support, and
    // only the second is the figure FPP print.
    assert_eq!(tree_paths_ground(4), 30);
    assert!(30 > (1u32 << 4) - 1);
    assert_eq!(tree_paths(4).iter().fold(0u64, |a, s| a | s).count_ones(), 15);
}

/// `Product.iota4` is the wreath product `C₃ ≀ C₃` of Odd-Sunflowers p. 4.
#[test]
fn iota4_is_the_wreath_product_of_two_triangles() {
    /// `F ≀ G` on `n` disjoint copies of `G`'s ground set, `m` points each.
    fn wreath(f: &[Vec<u32>], g: &[Vec<u32>], m: u32) -> Vec<u32> {
        let mut out = Vec::new();
        for base in f {
            // one choice from G per element of `base`
            let mut acc = vec![0u32];
            for &i in base {
                let mut next = Vec::new();
                for a in &acc {
                    for gs in g {
                        next.push(gs.iter().fold(*a, |b, &x| b | 1 << (i * m + x)));
                    }
                }
                acc = next;
            }
            out.extend(acc);
        }
        out
    }
    // C₃: the three 2-subsets of a 3-set. An antichain, and
    // odd-sunflower-free, which is what FPP's Lemma 7 needs.
    let c3: Vec<Vec<u32>> = vec![vec![0, 1], vec![0, 2], vec![1, 2]];
    let w = wreath(&c3, &c3, 3);

    // The paper's arithmetic: |F ≀ G| = |F|·|G|^k, k = 2.
    assert_eq!(w.len(), 3 * 3usize.pow(2));
    assert_eq!(w.len(), 27);
    assert!(w.iter().all(|s| s.count_ones() == 4), "not 4-uniform");
    assert_eq!(w.iter().fold(0u32, |a, &s| a | s).count_ones(), 9);

    // Intersecting and sunflower-free, as Lemma 7 predicts.
    for i in 0..w.len() {
        for j in i + 1..w.len() {
            assert!(w[i] & w[j] != 0, "wreath product not intersecting");
            for l in j + 1..w.len() {
                assert!(
                    !is_sunflower(w[i] as u64, w[j] as u64, w[l] as u64),
                    "wreath product has a 3-sunflower"
                );
            }
        }
    }

    // And it *is* Product.iota4, up to relabelling the nine points.
    let target: HashSet<u32> = iota4().into_iter().collect();
    let src: Vec<u32> = w.clone();
    let mut perm: Vec<u32> = (0..9).collect();
    let mut found = None;
    // Heap's algorithm over the 9! relabellings.
    fn heap(k: usize, p: &mut Vec<u32>, src: &[u32], target: &HashSet<u32>, found: &mut Option<Vec<u32>>) {
        if found.is_some() {
            return;
        }
        if k == 1 {
            let mapped: HashSet<u32> = src
                .iter()
                .map(|&s| (0..9).filter(|b| s >> b & 1 == 1).fold(0u32, |a, b| a | 1 << p[b as usize]))
                .collect();
            if mapped == *target {
                *found = Some(p.clone());
            }
            return;
        }
        for i in 0..k {
            heap(k - 1, p, src, target, found);
            if found.is_some() {
                return;
            }
            if k % 2 == 0 {
                p.swap(i, k - 1);
            } else {
                p.swap(0, k - 1);
            }
        }
    }
    heap(9, &mut perm, &src, &target, &mut found);
    assert!(
        found.is_some(),
        "C3 wreath C3 is not isomorphic to Product.iota4"
    );
}

/// `Product.iota4` satisfies `F = F^⊤`: it is a maximal intersecting
/// family of 4-sets, so Erdős–Lovász's `N(4) = 16` applies to it.
#[test]
fn iota4_is_a_maximal_intersecting_family() {
    let fam = iota4();
    assert_eq!(fam.len(), 27);

    // Intersecting, as `Product.iota4` is meant to be.
    for i in 0..fam.len() {
        for j in i + 1..fam.len() {
            assert!(fam[i] & fam[j] != 0, "members {i},{j} are disjoint");
        }
    }

    let blocks = |m: u32| fam.iter().all(|&s| s & m != 0);
    let mask = |ps: &[u32]| ps.iter().fold(0u32, |a, &p| a | 1 << p);

    // τ ≥ 4: no set of three or fewer points of [9] meets every member.
    for a in 0..9 {
        assert!(!blocks(mask(&[a])), "tau is 1");
        for b in a + 1..9 {
            assert!(!blocks(mask(&[a, b])), "tau is 2");
            for c in b + 1..9 {
                assert!(!blocks(mask(&[a, b, c])), "tau is 3, at {a},{b},{c}");
            }
        }
    }

    // τ = 4: a member is a blocking set, since the family is intersecting.
    assert!(blocks(fam[0]), "tau is not 4");

    // Maximality over the *whole universe of sets*, not just over [9].
    // A blocking 4-set using j ≥ 1 points outside [9] would restrict to a
    // blocking (4−j)-set inside [9], and the loop above showed there is
    // none of size ≤ 3. So it suffices to range over the 4-subsets of [9].
    let members: HashSet<u32> = fam.iter().copied().collect();
    let mut outside_blockers = 0usize;
    for a in 0..9 {
        for b in a + 1..9 {
            for c in b + 1..9 {
                for d in c + 1..9 {
                    let m = mask(&[a, b, c, d]);
                    if blocks(m) && !members.contains(&m) {
                        outside_blockers += 1;
                    }
                }
            }
        }
    }
    assert_eq!(
        outside_blockers, 0,
        "iota4 is not maximal intersecting: {outside_blockers} blocking 4-sets outside it"
    );

    // So the blocking 4-sets are exactly the members: F = F^⊤.
    let blocking: HashSet<u32> = (0..9)
        .flat_map(|a| (a + 1..9).map(move |b| (a, b)))
        .flat_map(|(a, b)| (b + 1..9).map(move |c| (a, b, c)))
        .flat_map(|(a, b, c)| (c + 1..9).map(move |d| mask(&[a, b, c, d])))
        .filter(|&m| blocks(m))
        .collect();
    assert_eq!(blocking, members, "F != F-transpose");

    // Hanson–Toft: N(4) = 2k − 2 + ½C(2k−2,k−1) = 6 + 10 = 16, and iota4
    // uses nine points, comfortably inside it.
    assert_eq!(2 * 4 - 2 + 20 / 2, 16);
    assert_eq!(fam.iter().fold(0u32, |a, &s| a | s).count_ones(), 9);
    assert!(9 <= 16, "iota4 would contradict Hanson-Toft");
}

/// The tightest literature number for the rung, and it closes the
/// shifting loophole: `35`, three above the 32 the rung asks about.
///
/// Frankl–Wang p. 3 defines `g(n,k,s)` as the maximum of `|F|` over
/// intersecting **initial** (shifted) `k`-graphs with `τ(F) ≥ s`, gives
///
/// ```text
///   K(n,k,s) = { K : 1 ∈ K, |K ∩ [2, k+s−1]| ≥ s−1 } ∪ C([2, k+s−1], k)
/// ```
///
/// and proves in Theorem 1.6 that `g(n,k,s) = |K(n,k,s)|` for `n > 2k` —
/// **for every `k`**, with no `k ≥ 7` restriction. So unlike Theorem 1.4
/// this one does reach `k = 4`.
///
/// At `k = 4, s = 4` the count is `C(6,3) + C(6,4) = 35`, and it does not
/// depend on `n` at all. That matters twice over. It is far tighter than
/// the `42 ≤ r(4) ≤ 64` bracket `docs/reading.md` A22 quotes, and it
/// disposes of the obvious remaining hope — that shifting the family
/// first might bring the covering-number bound under 32. It does not:
/// 35 > 32. The rung survives by three.
///
/// This is not a bound on `ι(4,11)`. Shifting does not preserve
/// 3-sunflower-freeness, so an extremal sunflower-free family need not be
/// initial, and Theorem 1.6 says nothing about the ones that are not.
#[test]
fn even_the_shifted_covering_number_maximum_stays_above_thirty_two() {
    /// `|K(n,k,s)|`, built from the definition rather than a closed form.
    fn k_family(n: u32, k: u32, s: u32) -> Vec<u64> {
        let hi = k + s - 1;
        let band: u64 = (2..=hi).fold(0u64, |m, i| m | 1 << i);
        let mut out: HashSet<u64> = HashSet::new();
        // {K : 1 ∈ K, |K ∩ [2, k+s−1]| ≥ s−1}
        let pts: Vec<u32> = (2..=n).collect();
        let mut idx = vec![0usize; (k - 1) as usize];
        fn rec(
            start: usize,
            depth: usize,
            idx: &mut Vec<usize>,
            pts: &[u32],
            band: u64,
            s: u32,
            out: &mut HashSet<u64>,
        ) {
            if depth == idx.len() {
                let m = idx.iter().fold(1u64 << 1, |a, &i| a | 1 << pts[i]);
                if (m & band & !(1 << 1)).count_ones() >= s - 1 {
                    out.insert(m);
                }
                return;
            }
            for i in start..pts.len() {
                idx[depth] = i;
                rec(i + 1, depth + 1, idx, pts, band, s, out);
            }
        }
        rec(0, 0, &mut idx, &pts, band, s, &mut out);
        // C([2, k+s−1], k)
        let bandpts: Vec<u32> = (2..=hi).collect();
        let mut c = vec![0usize; k as usize];
        fn rec2(start: usize, depth: usize, c: &mut Vec<usize>, pts: &[u32], out: &mut HashSet<u64>) {
            if depth == c.len() {
                out.insert(c.iter().fold(0u64, |a, &i| a | 1 << pts[i]));
                return;
            }
            for i in start..pts.len() {
                c[depth] = i;
                rec2(i + 1, depth + 1, c, pts, out);
            }
        }
        rec2(0, 0, &mut c, &bandpts, &mut out);
        out.into_iter().collect()
    }

    // τ ≥ 4 at k = 4: exactly 35, for every n > 2k = 8.
    for n in 9..=20u32 {
        let f = k_family(n, 4, 4);
        assert_eq!(f.len(), 35, "|K({n},4,4)| is not 35");
        // Intersecting, as the paper says K(n,k,s) is.
        for i in 0..f.len() {
            for j in i + 1..f.len() {
                assert!(f[i] & f[j] != 0, "K({n},4,4) is not intersecting");
            }
        }
    }
    // The closed form the count matches: C(6,3) + C(6,4).
    assert_eq!(20 + 15, 35);

    // τ ≥ 3 at k = 4: 10n − 45, so 65 at n = 11 — below |G(11,4)| = 74,
    // which is consistent, since the paper notes G(n,k) is *not* initial.
    for n in 9..=20u32 {
        assert_eq!(k_family(n, 4, 3).len(), (10 * n - 45) as usize);
    }
    assert_eq!(k_family(11, 4, 3).len(), 65);
    assert!(65 < 74, "the initial maximum should not exceed the general one");

    // Dual verification of the τ ≥ 3 count. The paper gives a closed form
    // for the same quantity in Lemma 5.1 (p. 23), by a different route:
    //
    //   g(n,k,3) = C(n−1,k−1) − C(n−k−2,k−1) − (k+1)C(n−k−2,k−2) + k + 1
    //
    // It agrees with the enumeration above at every n, which checks the
    // K(n,k,s) construction against the paper's own arithmetic rather than
    // against a restatement of it.
    fn lemma_5_1(n: i64, k: i64) -> i64 {
        fn binom(n: i64, k: i64) -> i64 {
            if k < 0 || n < k {
                return 0;
            }
            (0..k).fold(1i64, |acc, i| acc * (n - i) / (i + 1))
        }
        binom(n - 1, k - 1) - binom(n - k - 2, k - 1) - (k + 1) * binom(n - k - 2, k - 2) + k + 1
    }
    for n in 9..=20i64 {
        assert_eq!(
            lemma_5_1(n, 4),
            10 * n - 45,
            "Lemma 5.1 disagrees with the K-family count at n={n}"
        );
    }
    // And eq. (5.1), g(n,k,3) < |G(n,k)|, holds at k = 4 as well, which is
    // the consistency check that the initial maximum sits below the general
    // one — as it must, since G(n,k) is not initial.
    for n in 9..=200i64 {
        assert!(lemma_5_1(n, 4) < fw_exact(n, 4), "eq (5.1) fails at n={n}");
    }

    // What the rung needs, and does not get, from either.
    assert!(35 > 32, "shifting does not bring tau=4 under 32");
    assert!(65 > 32, "shifting does not bring tau=3 under 32");
}

/// The two problems agree on 27 at `k = 4`. An observation, not a theorem.
#[test]
fn twenty_seven_is_also_the_covering_number_four_lower_bound() {
    // Frankl–Ota–Tokushige's even-k lower bound for f(n,k,k), quoted on
    // Frankl–Wang p. 2: (k/2 + 1)^(k−1).
    let k = 4u32;
    assert_eq!((k / 2 + 1).pow(k - 1), 27);
    // And iota4, which has τ = 4 = k, has exactly 27 members.
    assert_eq!(iota4().len(), 27);
    // The Erdős–Lovász bracket the same page quotes, for the record.
    assert_eq!(k.pow(k), 256); // upper, k^k
    assert_eq!((24.0f64 * (std::f64::consts::E - 1.0)).floor() as u32, 41); // ⌊k!(e−1)⌋
}
