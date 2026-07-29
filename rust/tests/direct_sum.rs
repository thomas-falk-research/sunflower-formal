//! Falsification of the direct-sum lower bound.
//!
//! The claim under test:
//!
//! ```text
//!     g(a+b, k) >= g(a, k) * g(b, k)
//! ```
//!
//! where `g(n,k) = f(n,k) - 1` is the largest number of `n`-sets with no
//! `k`-sunflower. Concretely: if `F1` is `a`-uniform and `k`-sunflower-free,
//! `F2` is `b`-uniform and `k`-sunflower-free, and their ground sets are
//! disjoint, then `{A ∪ B : A ∈ F1, B ∈ F2}` is `(a+b)`-uniform,
//! `k`-sunflower-free, and has `|F1| · |F2|` members.
//!
//! The oracle is `sunflower.rs`, the brute-force pairwise-intersection
//! detector, which knows nothing about direct sums. Every family it is
//! handed here is one this file built by concatenation; nothing about the
//! construction is fed to the detector.
//!
//! What the tests aim at, in the order they would break:
//!
//! 1. **The theorem, exhaustively at small parameters.** Every pair of
//!    sunflower-free families drawn from a small ground set, at
//!    uniformities 1 and 2 and widths 2, 3 and 4.
//! 2. **The concrete instances the Coq corollaries evaluate to.**
//!    `two_triangles ⊕ two_triangles` is 36 members of size 4 with no
//!    3-sunflower, which is `DirectSum.lower_bound_f_n_3` at `t = 2`
//!    (`f(4,3) >= 37`, against the product family's 16).
//! 3. **Uniformity is load-bearing.** The two-member counterexample
//!    `Audit.uniformity_is_needed_in_the_direct_sum` pins in Coq, checked
//!    here by the independent detector.
//! 4. **Cross-disjointness is load-bearing**, one step earlier: overlapping
//!    ground sets do not produce a family of sets at all.
//! 5. **The parity relabelling** the Coq proof uses really does separate
//!    the ground sets, and really does preserve sunflower-freeness.

use sunflower_formal::construction::{direct_sum, direct_sum_shifted, relabel};
use sunflower_formal::sunflower::{find_k_sunflower, is_valid_family, Family, Set};

/// All `m`-subsets of `{0, ..., ground-1}`, as canonical sets.
fn m_subsets(ground: u32, m: usize) -> Family {
    let mut out = Family::new();
    for mask in 0u32..(1 << ground) {
        if mask.count_ones() as usize != m {
            continue;
        }
        out.push((0..ground).filter(|i| mask >> i & 1 == 1).collect());
    }
    out
}

/// Every `k`-sunflower-free subfamily of the `m`-subsets of `[ground]`.
/// Exhaustive, so `ground` and `m` must stay small.
fn sunflower_free_families(ground: u32, m: usize, k: usize) -> Vec<Family> {
    let universe = m_subsets(ground, m);
    assert!(universe.len() <= 20, "would enumerate 2^{}", universe.len());
    let mut out = Vec::new();
    for mask in 0u32..(1 << universe.len()) {
        let f: Family = (0..universe.len())
            .filter(|i| mask >> i & 1 == 1)
            .map(|i| universe[i].clone())
            .collect();
        if find_k_sunflower(&f, k).is_none() {
            out.push(f);
        }
    }
    out
}

fn assert_direct_sum_works(f1: &[Set], f2: &[Set], a: usize, b: usize, k: usize) -> usize {
    let sum = direct_sum_shifted(f1, f2);

    assert_eq!(
        sum.len(),
        f1.len() * f2.len(),
        "size is not multiplicative: {f1:?} + {f2:?}"
    );
    assert!(
        is_valid_family(&sum),
        "sum is not a family of distinct sets: {f1:?} + {f2:?} = {sum:?}"
    );
    for s in &sum {
        assert_eq!(
            s.len(),
            a + b,
            "sum is not ({a}+{b})-uniform: {s:?} in {f1:?} + {f2:?}"
        );
    }
    if let Some(sf) = find_k_sunflower(&sum, k) {
        panic!(
            "REFUTED g({a}+{b},{k}) >= g({a},{k})*g({b},{k}):\n  \
             F1 = {f1:?}\n  F2 = {f2:?}\n  sum = {sum:?}\n  \
             {k}-sunflower at {:?} with core {:?}",
            sf.indices, sf.core
        );
    }
    sum.len()
}

/// 1. The theorem, over every pair of sunflower-free families at small
///    parameters. This is the check that would have run before the Coq
///    proof was attempted.
#[test]
fn direct_sum_is_sunflower_free_exhaustively() {
    // The grid, written out rather than taken as a product, because one
    // corner of the product does not finish. At `k = 4` every one of the
    // 64 subfamilies of `K_4`'s edge set is 4-sunflower-free (`K_4` has
    // matching number 2), so the `(4,2) x (4,2)` cell is 4096 pairs whose
    // sums have 36 members each, and deciding those needs
    // `C(36,4) = 58905` quadruples apiece. That cell is excluded; `k = 4`
    // is covered at uniformity 1 only. Nothing else is dropped, and the
    // pair count is asserted below so a shrinking grid cannot pass
    // silently.
    //
    // The pools are hoisted out of the loop: recomputing them per outer
    // family turns a seconds-long test into an hours-long one.
    const SHAPES: [(u32, usize); 3] = [(3, 1), (4, 1), (4, 2)];
    const CHEAP: [(u32, usize); 2] = [(3, 1), (4, 1)];

    let mut pairs = 0usize;
    let mut largest_sum = 0usize;
    for (k, shapes) in [(2usize, &SHAPES[..]), (3, &SHAPES[..]), (4, &CHEAP[..])] {
        let pools: Vec<(usize, Vec<Family>)> = shapes
            .iter()
            .map(|&(g, m)| (m, sunflower_free_families(g, m, k)))
            .collect();
        for (m1, pool1) in &pools {
            for (m2, pool2) in &pools {
                for f1 in pool1 {
                    for f2 in pool2 {
                        let n = assert_direct_sum_works(f1, f2, *m1, *m2, k);
                        largest_sum = largest_sum.max(n);
                        pairs += 1;
                    }
                }
            }
        }
    }
    // The count is pinned rather than bounded, because it is derivable
    // and a shrinking grid is exactly what this test must not do
    // silently:
    //
    //   k = 2  every two distinct members are a 2-sunflower, so the
    //          free families are those of size <= 1:
    //          (1+3) + (1+4) + (1+6) = 16,  16^2 =  256
    //   k = 3  singletons: any 3 are pairwise disjoint, so size <= 2.
    //          (4,2) is K_4, where matching <= 2 is automatic and the
    //          condition is max degree <= 2: 64 - (32-12+4-1) = 41.
    //          7 + 11 + 41 = 59,                     59^2 = 3481
    //   k = 4  1-uniform only: 8 + 15 = 23,          23^2 =  529
    //                                                       -----
    //                                                        4266
    assert_eq!(pairs, 4266, "the grid changed");
    // ...and that the grid is not all trivia. The biggest sum is 16,
    // not 36: at `k = 3` a subfamily of `K_4` must have max degree <= 2,
    // which caps it at the 4-cycle, so the largest cell is 4 x 4. The
    // 6-edge families only survive at `k = 4`, and that is the cell the
    // grid excludes.
    assert_eq!(largest_sum, 16, "no large sum was tested");
}

/// The six-edge two-triangles family, `F23.two_triangles` in Coq.
fn two_triangles() -> Family {
    vec![
        vec![0, 1],
        vec![0, 2],
        vec![1, 2],
        vec![3, 4],
        vec![3, 5],
        vec![4, 5],
    ]
}

/// 2. The instances the Coq corollaries evaluate to. `f(2,3) = 7` is
///    exact, so `g(2,3) = 6` and the direct sum gives `g(2t,3) >= 6^t`.
#[test]
fn f_n_3_lower_bound_instances() {
    let tt = two_triangles();
    assert!(find_k_sunflower(&tt, 3).is_none(), "g(2,3) >= 6 is the input");

    // t = 2: 36 members of size 4, so f(4,3) >= 37.
    let t2 = direct_sum_shifted(&tt, &tt);
    assert_eq!(t2.len(), 36);
    assert!(t2.iter().all(|s| s.len() == 4));
    assert!(is_valid_family(&t2));
    assert!(find_k_sunflower(&t2, 3).is_none(), "6^2 = 36 refuted");

    // The product family reaches only (k-1)^n = 2^4 = 16 at the same
    // uniformity, so the direct sum is strictly better and not by a
    // constant factor.
    assert!(36 > 2usize.pow(4));

    // t = 3: 216 members of size 6, so f(6,3) >= 217 against 2^6 = 64.
    let t3 = direct_sum_shifted(&t2, &tt);
    assert_eq!(t3.len(), 216);
    assert!(t3.iter().all(|s| s.len() == 6));
    assert!(is_valid_family(&t3));
    assert!(find_k_sunflower(&t3, 3).is_none(), "6^3 = 216 refuted");
    assert!(216 > 2usize.pow(6));

    // Odd uniformity: pair up and hang one extra point on the end.
    let singletons: Family = vec![vec![0], vec![1]];
    let odd = direct_sum_shifted(&t2, &singletons);
    assert_eq!(odd.len(), 72);
    assert!(odd.iter().all(|s| s.len() == 5));
    assert!(find_k_sunflower(&odd, 3).is_none(), "6^2 * 2 = 72 refuted");

    // g(3,3) >= 12, so f(3,3) >= 13. Recorded because it contradicts
    // the base case reported for the Abbott-Hanson-Sauer construction
    // in the secondary sources -- "a 3-uniform family of size 10 with
    // no 3-sunflower" cannot be extremal at uniformity 3 if the direct
    // sum already reaches 12. See docs/roadmap.md section 5.
    let u3 = direct_sum_shifted(&tt, &singletons);
    assert_eq!(u3.len(), 12);
    assert!(u3.iter().all(|s| s.len() == 3));
    assert!(is_valid_family(&u3));
    assert!(find_k_sunflower(&u3, 3).is_none(), "g(3,3) >= 12 refuted");
    assert!(12 > 10);
}

/// The clique construction at odd `k`, which is the `k`-general form of
/// the same instantiation: `g(2t, k) >= (k(k-1))^t`.
#[test]
fn clique_power_instances() {
    // Two disjoint copies of K_k, `CliqueLowerBound.two_cliques`.
    fn two_cliques(k: usize) -> Family {
        let mut edges = Family::new();
        for part in 0..2u32 {
            let base = part * k as u32;
            for i in 0..k as u32 {
                for j in (i + 1)..k as u32 {
                    edges.push(vec![base + i, base + j]);
                }
            }
        }
        edges
    }

    // k = 3: squaring is affordable, so check the headline instance
    // `g(4,3) >= (3*2)^2 = 36` against the product family's 2^4 = 16.
    let e3 = two_cliques(3);
    assert_eq!(e3.len(), 6);
    assert!(find_k_sunflower(&e3, 3).is_none());
    let sq3 = direct_sum_shifted(&e3, &e3);
    assert_eq!(sq3.len(), 36);
    assert!(sq3.iter().all(|s| s.len() == 4));
    assert!(find_k_sunflower(&sq3, 3).is_none());
    assert!(36 > 2usize.pow(4));

    // k = 5: `g(2,5) >= 20`, and squaring it would give 400 members of
    // size 4, which brute force cannot decide -- `C(400,5)` is 8e10
    // quintuples. So the sum is taken against two singletons instead,
    // checking `g(3,5) >= 20 * 2 = 40`. That instance does *not* beat
    // the product family's `4^3 = 64`: the direct sum only overtakes it
    // once both factors are clique families, and at k = 5 that instance
    // is out of brute-force reach. What is checked here is the theorem,
    // not the improvement; the improvement is `cliques_beat_product`,
    // whose arithmetic is checked at the end.
    let e5 = two_cliques(5);
    assert_eq!(e5.len(), 20);
    assert!(find_k_sunflower(&e5, 5).is_none(), "two K_5 contain a 5-sunflower");
    let singletons: Family = vec![vec![0], vec![1]];
    let s5 = direct_sum_shifted(&e5, &singletons);
    assert_eq!(s5.len(), 40);
    assert!(s5.iter().all(|s| s.len() == 3));
    assert!(is_valid_family(&s5));
    assert!(find_k_sunflower(&s5, 5).is_none(), "g(3,5) >= 40 refuted");

    // The arithmetic `DirectSum.cliques_beat_product` proves, at both k.
    for k in [3usize, 5] {
        assert!((k * (k - 1)).pow(2) > (k - 1).pow(4));
    }
}

/// 3. Uniformity is load-bearing, and the counterexample is minimal.
///    Same families as `Audit.uniformity_is_needed_in_the_direct_sum`.
#[test]
fn uniformity_is_load_bearing() {
    let f1: Family = vec![vec![0], vec![0, 1]];
    let f2: Family = vec![vec![2], vec![2, 3]];

    // Neither side contains a 3-sunflower: each has two members.
    assert!(find_k_sunflower(&f1, 3).is_none());
    assert!(find_k_sunflower(&f2, 3).is_none());
    // Ground sets are disjoint, so cross-disjointness holds.
    assert!(f1.iter().flatten().all(|x| *x < 2));
    assert!(f2.iter().flatten().all(|x| *x >= 2));

    let sum = direct_sum(&f1, &f2);
    assert_eq!(sum.len(), 4);
    assert!(is_valid_family(&sum));

    let sf = find_k_sunflower(&sum, 3)
        .expect("the non-uniform direct sum should contain a 3-sunflower");
    assert_eq!(sf.core, vec![0, 2]);

    // And the failure really is non-uniformity: making both sides
    // uniform by dropping the smaller member restores the conclusion.
    let g1: Family = vec![vec![0, 1]];
    let g2: Family = vec![vec![2, 3]];
    assert!(find_k_sunflower(&direct_sum(&g1, &g2), 3).is_none());
}

/// Only the *first* family has to be uniform. The proof splits every
/// member of the sum at position `a`, which needs the members of `F1` to
/// have that size and asks nothing about `F2`'s. That is a sharper claim
/// than the symmetric one, so it gets its own exhaustive check: `F1`
/// uniform, `F2` ranging over families of *arbitrary* subsets.
#[test]
fn only_the_first_family_needs_uniformity() {
    // Every family of arbitrary subsets of {0,1,2} with no 3-sunflower.
    let universe: Family = (0u32..8)
        .map(|mask| (0..3).filter(|i| mask >> i & 1 == 1).collect())
        .collect();
    let mut arbitrary: Vec<Family> = Vec::new();
    for mask in 0u32..(1 << universe.len()) {
        let f: Family = (0..universe.len())
            .filter(|i| mask >> i & 1 == 1)
            .map(|i| universe[i].clone())
            .collect();
        if find_k_sunflower(&f, 3).is_none() {
            arbitrary.push(f);
        }
    }
    // 116 of the 256 subfamilies of the 8 subsets of {0,1,2}.
    assert_eq!(arbitrary.len(), 116, "the arbitrary-family pool changed");

    let mut checked = 0usize;
    for f1 in sunflower_free_families(4, 2, 3) {
        for f2 in &arbitrary {
            let sum = direct_sum_shifted(&f1, f2);
            assert_eq!(sum.len(), f1.len() * f2.len());
            if let Some(sf) = find_k_sunflower(&sum, 3) {
                panic!(
                    "REFUTED the asymmetric form:\n  F1 (2-uniform) = {f1:?}\n  \
                     F2 (arbitrary) = {f2:?}\n  sum = {sum:?}\n  core {:?}",
                    sf.core
                );
            }
            checked += 1;
        }
    }
    // 41 sunflower-free subfamilies of K_4 (max degree <= 2) times 116.
    assert_eq!(checked, 41 * 116, "the grid changed");

    // And the asymmetry is real in the other direction too: with F1
    // non-uniform the conclusion fails, which is `uniformity_is_load_bearing`.
}

/// 4. Cross-disjointness is load-bearing one step earlier: with
///    overlapping ground sets the concatenation is not a set.
#[test]
fn cross_disjointness_is_load_bearing() {
    let f1: Family = vec![vec![0], vec![1]];
    // Same ground set, not shifted.
    let sum = direct_sum(&f1, &f1);
    assert_eq!(sum.len(), 4);
    // Two of the four "members" are the doubled points {0,0} and {1,1},
    // which canonicalise to singletons, and the other two are both {0,1}.
    assert!(
        !is_valid_family(&sum),
        "overlapping ground sets should not yield a family of distinct 2-sets"
    );
    // Shifting fixes it.
    assert!(is_valid_family(&direct_sum_shifted(&f1, &f1)));
}

/// 5. The parity relabelling the Coq proof uses: injective, ground-set
///    separating, and sunflower-freeness preserving.
#[test]
fn parity_relabelling_separates_and_preserves() {
    let tt = two_triangles();
    let even = relabel(&tt, false);
    let odd = relabel(&tt, true);

    assert_eq!(even[0], vec![0, 2]);
    assert_eq!(odd[0], vec![1, 3]);
    assert!(even.iter().flatten().all(|x| x % 2 == 0));
    assert!(odd.iter().flatten().all(|x| x % 2 == 1));
    assert_eq!(even.len(), tt.len());
    assert!(is_valid_family(&even) && is_valid_family(&odd));
    assert!(find_k_sunflower(&even, 3).is_none());
    assert!(find_k_sunflower(&odd, 3).is_none());

    // The parity sum is the one `DirectSum.lower_bound_sum` builds.
    let sum = direct_sum(&even, &odd);
    assert_eq!(sum.len(), 36);
    assert!(is_valid_family(&sum));
    assert!(sum.iter().all(|s| s.len() == 4));
    assert!(find_k_sunflower(&sum, 3).is_none());
}

/// Relabelling by an arbitrary injection preserves sunflower-freeness,
/// which is the general fact `DirectSum.rmapF_no_sunflower` proves. The
/// injectivity is what carries the load, and this checks both ways it
/// fails without it.
#[test]
fn relabelling_needs_injectivity() {
    let tt = two_triangles();
    // x -> 3x + 7 is injective, so nothing changes.
    let moved: Family = tt
        .iter()
        .map(|s| {
            let mut v: Set = s.iter().map(|x| 3 * x + 7).collect();
            v.sort_unstable();
            v
        })
        .collect();
    assert_eq!(moved.len(), tt.len());
    assert!(is_valid_family(&moved));
    assert!(find_k_sunflower(&moved, 3).is_none());

    // First failure mode: a non-injective map can *create* a sunflower.
    // {0,1}, {0,2}, {3,4} has none -- its pairwise intersections are
    // {0}, {}, {} -- but merging 3 into 0 makes them {0}, {0}, {0}.
    let f: Family = vec![vec![0, 1], vec![0, 2], vec![3, 4]];
    assert!(find_k_sunflower(&f, 3).is_none(), "the source already has one");
    let merged: Family = f
        .iter()
        .map(|s| {
            let mut v: Set = s.iter().map(|x| if *x == 3 { 0 } else { *x }).collect();
            v.sort_unstable();
            v
        })
        .collect();
    assert!(is_valid_family(&merged), "still three distinct 2-sets");
    let sf = find_k_sunflower(&merged, 3)
        .expect("merging two points should create a 3-sunflower");
    assert_eq!(sf.core, vec![0]);

    // Second failure mode: a non-injective map can collapse distinct
    // members onto each other, so the image is not a family at all.
    // x -> x mod 3 sends both triangles of `two_triangles` to the same
    // three edges. This is why `rmapF_Distinct` needs injectivity too,
    // not only `rmapF_no_sunflower`.
    let collapsed: Family = tt
        .iter()
        .map(|s| {
            let mut v: Set = s.iter().map(|x| x % 3).collect();
            v.sort_unstable();
            v.dedup();
            v
        })
        .collect();
    assert_eq!(collapsed.len(), 6);
    assert!(
        !is_valid_family(&collapsed),
        "x mod 3 should identify the two triangles"
    );
}
