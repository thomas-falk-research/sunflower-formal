//! `tau = 3` at the `iota(4,11)` rung: how far the `tau = 2` method
//! carries, and where it stops.
//!
//! §37.6 disposed of `tau = 3` **by citation** and the citation did not
//! decide it — `docs/reading.md` A22 records that Frankl–Wang's `G(n,k)`
//! has 74 members at `n = 11`, which is above 32 and so excludes nothing.
//! §42 then closed `tau = 2` here rather than by citation, and §49.4
//! proposed the three-part analogue as "the nearest mathematics" that
//! would close the rung without any compute, offering two pieces of it
//! "for free". This file works that proposal and reports what it gives.
//!
//! ## The decomposition
//!
//! Let `F` be 4-uniform, intersecting, sunflower-free on `[11]` with a
//! 3-cover `T = {p, q, r}`. Every member meets `T`, so `F` partitions by
//! `A ∩ T` into seven classes — three singleton, three pair, one triple:
//!
//! ```text
//!   |F| = (a + b + c)  +  (d + e + f)  +  g
//!     a,b,c  A ∩ T is one point;  links are 3-sets on the other eight
//!     d,e,f  A ∩ T is two points; links are 2-sets on the other eight
//!     g      A ⊇ T;               links are 1-sets on the other eight
//! ```
//!
//! ## What §49.4 offered, and what the two pieces are actually worth
//!
//! > Two elementary pieces of it are free: at most **two** members
//! > contain all three cover points (three would have pairwise
//! > intersection exactly the cover, which is a sunflower), and the
//! > members containing a fixed pair have a link with no 3-matching, so
//! > Erdős–Gallai caps them.
//!
//! The first is right and `g <= 2` is checked below. **The second is
//! right and weak, and the repository already had better.** A pair
//! class's link is not merely 3-matching-free: three link edges through
//! a common vertex also have equal pairwise intersections, so the link
//! graph has maximum degree at most two as well — which is to say it is
//! *sunflower-free as a graph*, and `PureLink.g_two_at_most_six` is
//! already in the kernel. On eight points Erdős–Gallai gives **13** and
//! sunflower-freeness gives **6**, so the three pair classes are capped
//! at 18 rather than 39. §49.4 reached outside for a theorem the
//! development had inside, which is the same novelty-audit failure §45.4
//! exists to catch.
//!
//! ## Where it stops
//!
//! With both pieces at their best, `|F| <= (a + b + c) + 18 + 2`, so the
//! case closes only if `a + b + c <= 11`. It is not: `TAU3_WITNESS` below
//! is an explicit 4-uniform intersecting sunflower-free family on `[11]`
//! with `tau = 3` and `a + b + c = 19`, every member holding exactly one
//! cover point. So this decomposition yields at best `|F| <= 39`, and
//! **the `tau = 2` method does not transfer**. What would have to change
//! is the part §49.4 called the hard bit: the singleton classes are not
//! merely pairwise cross-intersecting, they also admit no *transversal*
//! sunflower — one member from each of the three — and nothing here
//! prices that condition.

use sunflower_formal::shift::{is_intersecting, is_sunflower_free};
use sunflower_formal::spread::Mask;

const P: u32 = 8;
const Q: u32 = 9;
const R: u32 = 10;

fn set(points: &[u32]) -> Mask {
    points.iter().fold(0, |m, &v| m | (1 << v))
}

fn is_sunflower(a: Mask, b: Mask, c: Mask) -> bool {
    (a & b) == (a & c) && (a & c) == (b & c)
}

/// Every 2-subset of `[8]`, as a mask.
fn pairs_on_eight() -> Vec<Mask> {
    (0u32..(1 << 8)).filter(|m| m.count_ones() == 2).collect()
}

/// §49.4's first free piece: a fourth member through all of `T` is
/// impossible, and a third already is.
///
/// `A_i = T ∪ {x_i}` with the `x_i` distinct gives `A_i ∩ A_j = T` for
/// every pair, which is a sunflower with core `T`. So the triple class
/// holds at most two members, and this checks it over every choice of
/// three distinct outside points rather than arguing it.
#[test]
fn the_triple_class_holds_at_most_two() {
    let t = set(&[P, Q, R]);
    let mut found = 0;
    for x in 0..8u32 {
        for y in (x + 1)..8u32 {
            for z in (y + 1)..8u32 {
                let (a, b, c) = (t | (1 << x), t | (1 << y), t | (1 << z));
                assert!(is_sunflower(a, b, c), "T ∪ {{{x}}}, {{{y}}}, {{{z}}} must be a sunflower");
                found += 1;
            }
        }
    }
    assert_eq!(found, 56, "all C(8,3) choices of three outside points");
    // Two is attainable, so the bound is exact and not merely an upper one.
    assert!(is_sunflower_free(&[t | 1, t | 2]));
}

/// §49.4's second free piece, and the better bound the kernel already
/// held.
///
/// A pair class `{A : A ∩ T = {p,q}}` has `A_i = {p,q} ∪ e_i`, so
/// `A_i ∩ A_j = {p,q} ∪ (e_i ∩ e_j)` and the class is sunflower-free
/// exactly when the link graph `{e_i}` is. That rules out two shapes, not
/// one: three pairwise disjoint edges (a 3-matching, which is what §49.4
/// saw) *and* three edges through a common vertex (which it did not).
/// The second is the binding one.
#[test]
fn a_pair_class_is_capped_by_g_two_and_not_by_erdos_gallai() {
    let edges = pairs_on_eight();

    // The link characterisation: sunflower-free as a class iff
    // sunflower-free as a graph. Checked on every triple of edges.
    let pq = set(&[P, Q]);
    for i in 0..edges.len() {
        for j in (i + 1)..edges.len() {
            for k in (j + 1)..edges.len() {
                let (e, f, g) = (edges[i], edges[j], edges[k]);
                assert_eq!(
                    is_sunflower(pq | e, pq | f, pq | g),
                    is_sunflower(e, f, g),
                    "a class sunflower and a link sunflower must be the same event"
                );
            }
        }
    }

    // Both shapes a link sunflower can take.
    let three_matching = [set(&[0, 1]), set(&[2, 3]), set(&[4, 5])];
    let three_star = [set(&[0, 1]), set(&[0, 2]), set(&[0, 3])];
    assert!(!is_sunflower_free(&three_matching), "a 3-matching is a sunflower");
    assert!(!is_sunflower_free(&three_star), "and so is a 3-star, which §49.4 missed");
    // Erdős–Gallai sees only the first: the star has matching number one.
    assert!(matching_number(&three_star) < 3);

    // The two caps, on eight points. Sunflower-free: two triangles.
    let best_sf = max_subfamily(&edges, |f| is_sunflower_free(f));
    assert_eq!(best_sf, 6, "g(2) = 6, which PureLink.g_two_at_most_six has");
    // Erdős–Gallai for no 3-matching: max{C(5,2), C(2,2) + 2*(8-2)} = 13.
    let best_eg = max_subfamily(&edges, |f| matching_number(f) <= 2);
    assert_eq!(best_eg, 13, "the bound §49.4 reached for");
    assert_eq!(best_eg, std::cmp::max(10, 1 + 2 * (8 - 2)), "and it is the formula's value");

    // Three pair classes, the two ways.
    assert_eq!(3 * best_sf, 18);
    assert_eq!(3 * best_eg, 39);
    assert!(3 * best_sf < 3 * best_eg, "the kernel's bound is the better one");
}

fn matching_number(f: &[Mask]) -> usize {
    // Small graphs only; exhaustive over subsets of the edge list.
    let mut best = 0;
    for sub in 0u32..(1 << f.len()) {
        let picked: Vec<Mask> = (0..f.len()).filter(|i| sub >> i & 1 == 1).map(|i| f[i]).collect();
        let union = picked.iter().fold(0, |a, &b| a | b);
        if union.count_ones() as usize == 2 * picked.len() && picked.len() > best {
            best = picked.len();
        }
    }
    best
}

/// Largest subfamily of `cands` satisfying `ok`, by branch and bound.
fn max_subfamily(cands: &[Mask], ok: fn(&[Mask]) -> bool) -> usize {
    fn go(cands: &[Mask], i: usize, cur: &mut Vec<Mask>, best: &mut usize, ok: fn(&[Mask]) -> bool) {
        if cur.len() > *best {
            *best = cur.len();
        }
        if i == cands.len() || cur.len() + (cands.len() - i) <= *best {
            return;
        }
        cur.push(cands[i]);
        if ok(cur) {
            go(cands, i + 1, cur, best, ok);
        }
        cur.pop();
        go(cands, i + 1, cur, best, ok);
    }
    let mut best = 0;
    go(cands, 0, &mut Vec::new(), &mut best, ok);
    best
}

/// A `tau = 3` family with nineteen members, all in the singleton
/// classes — which is what stops the decomposition.
///
/// Found by randomized greedy over the three singleton classes with
/// `d = e = f = g = 0`, then re-verified here from scratch. Points 0..=7
/// are the non-cover points; 8, 9, 10 are `p, q, r`.
const TAU3_WITNESS: [[u32; 3]; 19] = [
    // F_p, ten members
    [1, 2, 5], [1, 2, 6], [1, 3, 4], [1, 3, 6], [1, 4, 5],
    [2, 4, 5], [2, 4, 7], [2, 6, 7], [3, 4, 7], [3, 6, 7],
    // F_q, six members
    [1, 2, 3], [1, 2, 7], [1, 4, 6], [1, 4, 7], [2, 3, 5], [4, 5, 6],
    // F_r, three members
    [1, 5, 7], [2, 3, 4], [2, 4, 6],
];

fn witness() -> Vec<Mask> {
    TAU3_WITNESS
        .iter()
        .enumerate()
        .map(|(i, s)| {
            let cover = if i < 10 { P } else if i < 16 { Q } else { R };
            set(s) | (1 << cover)
        })
        .collect()
}

/// The witness is what it claims to be, checked against the definitions
/// rather than against the search that produced it.
#[test]
fn the_witness_is_a_tau_three_family_with_nineteen_members() {
    let f = witness();
    assert_eq!(f.len(), 19);
    assert!(f.iter().all(|m| m.count_ones() == 4), "4-uniform");
    assert!(f.iter().all(|m| m < &(1 << 11)), "on [11]");
    assert!(is_intersecting(&f), "intersecting");
    assert!(is_sunflower_free(&f), "sunflower-free, and distinct");

    // Every member holds exactly one cover point, so a + b + c = 19 and
    // d = e = f = g = 0.
    let t = set(&[P, Q, R]);
    assert!(f.iter().all(|m| (m & t).count_ones() == 1), "singleton classes only");

    // tau(F) = 3: T covers, and nothing smaller does.
    assert!(f.iter().all(|m| m & t != 0), "T is a cover");
    for x in 0..11u32 {
        assert!(!f.iter().all(|m| m >> x & 1 == 1), "no 1-cover at {x}");
        for y in (x + 1)..11u32 {
            let c = (1 << x) | (1 << y);
            assert!(!f.iter().all(|m| m & c != 0), "no 2-cover at {{{x},{y}}}");
        }
    }
}

/// The arithmetic that says the method stops, stated as an assertion so
/// a future session cannot re-derive the proposal without meeting it.
#[test]
fn the_tau_two_method_does_not_close_tau_three() {
    let singletons = witness().len();
    assert_eq!(singletons, 19, "a + b + c is at least this");

    // Both free pieces at their best.
    let pair_classes = 3 * 6;
    let triple_class = 2;
    let bound = singletons + pair_classes + triple_class;
    assert_eq!(bound, 39);
    assert!(bound > 31, "which is what closing the rung would need");

    // Even the improvement over §49.4's own suggestion does not rescue it.
    let bound_as_proposed = singletons + 3 * 13 + 2;
    assert_eq!(bound_as_proposed, 60);
    assert!(bound < bound_as_proposed, "6 beats 13, and neither is enough");

    // For contrast, the same shape at tau = 2 does close: §42's
    // max(|X| + |Y|) = 20 plus g(2) = 6 is 26, six under 32.
    assert!(20 + 6 < 32, "tau = 2, for contrast");
}
