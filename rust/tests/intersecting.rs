//! `iota(b)`: the largest *intersecting* 3-sunflower-free `b`-uniform
//! family, and the two constructions it feeds.
//!
//! Why this quantity. Two disjoint copies of an intersecting
//! sunflower-free family are sunflower-free (`Intersecting.double`), so
//! `g(b) >= 2 iota(b)`. And the Abbott–Hanson–Sauer *substitution* — blow
//! each point of a member of an `a`-uniform family up into a member of a
//! `b`-uniform one — is sunflower-free exactly when the inner family is
//! intersecting, giving `g(ab) >= g(a) iota(b)^a` and, iterated, a rate
//! of `iota(b)^(1/(b-1))` per point.
//!
//! That reconstruction is ours; the paper was not read. What is checked
//! here is the evidence for it:
//!
//! 1. `iota(2) = 3` (the triangle) and its doubling is `two_triangles`,
//!    which is the family behind the proved value `f(2,3) = 7`;
//! 2. `iota(3) = 10`, which makes the rate `10^(1/2) = 3.162...` — the
//!    published 1972 constant, on the nose;
//! 3. the substitution really does produce sunflower-free families, and
//!    really does stop doing so when the inner family is not
//!    intersecting.
//!
//! Point 3 is the one the mathematics rests on, and it is checked
//! against `find_sunflower_128`, which knows nothing about how the
//! families were built.

use sunflower_formal::intersecting::{
    doubled, find_sunflower_128, max_intersecting, substitute, verify,
};

const BUDGET: u64 = 20_000_000_000;

fn iota(ground: u32, b: u32) -> (usize, Vec<u32>) {
    let (n, fam, done) = max_intersecting(ground, b, BUDGET);
    assert!(done, "iota({b}) on {ground} points did not finish");
    verify(&fam, b, true).unwrap_or_else(|e| panic!("iota({b},{ground}): {e}"));
    assert_eq!(fam.len(), n);
    (n, fam)
}

/// 1 and 2: the two values the reconstruction predicts.
#[test]
fn iota_two_and_three() {
    // iota(2) = 3, the triangle, stable from three points on.
    assert_eq!(iota(3, 2).0, 3);
    for g in 3..=9 {
        assert_eq!(iota(g, 2).0, 3, "iota(2) moved at ground {g}");
    }

    // iota(3) = 10, first attained on six points and stable to eleven.
    let row: Vec<usize> = (3..=11).map(|g| iota(g, 3).0).collect();
    assert_eq!(row, vec![1, 4, 6, 10, 10, 10, 10, 10, 10]);

    // The rate this gives is the published AHS constant: iota^(1/(b-1)).
    let rate = (10f64).powf(0.5);
    assert!((rate - 3.1622).abs() < 1e-3);
}

/// The doubling, and that it reproduces the family behind `f(2,3) = 7`.
#[test]
fn doubling_is_sunflower_free() {
    for (g, b) in [(3u32, 2u32), (6, 3), (7, 3)] {
        let (n, fam) = iota(g, b);
        let d = doubled(&fam, g);
        assert_eq!(d.len(), 2 * n);
        verify(&d, b, false).unwrap_or_else(|e| panic!("doubling at b={b}: {e}"));
    }

    // b = 2 gives six 2-sets with no 3-sunflower -- `f(2,3) >= 7`.
    let (_, tri) = iota(3, 2);
    assert_eq!(doubled(&tri, 3).len(), 6);

    // b = 3 gives twenty 3-sets -- `f(3,3) >= 21`, which is
    // `Intersecting.lower_bound_3_3_20` in the Coq.
    let (_, h3) = iota(6, 3);
    let d3 = doubled(&h3, 6);
    assert_eq!(d3.len(), 20);
    verify(&d3, 3, false).expect("the 20-member family is not sunflower-free");
}

/// Without the intersecting hypothesis the doubling is false, and the
/// smallest counterexample is two singletons -- the same one
/// `Audit.intersecting_is_needed_in_the_doubling` pins in the kernel.
#[test]
fn doubling_needs_intersecting() {
    let h: Vec<u32> = vec![0b01, 0b10];
    verify(&h, 1, false).expect("two singletons should be a valid family");
    assert!(h[0] & h[1] == 0, "and they are disjoint, i.e. not intersecting");
    let d = doubled(&h, 2);
    assert_eq!(d.len(), 4);
    assert!(
        verify(&d, 1, false).is_err(),
        "four singletons must contain a 3-sunflower"
    );
}

/// 3: the substitution. This is what the `iota` programme rests on.
#[test]
fn substitution_is_sunflower_free() {
    // two_triangles: 2-uniform, 6 members, sunflower-free. It is *not*
    // intersecting, and does not need to be -- only the inner family is.
    let tt: Vec<u32> = vec![0b000011, 0b000101, 0b000110, 0b011000, 0b101000, 0b110000];
    verify(&tt, 2, false).expect("two_triangles broken");

    // b = 2: g(4) >= 6 * 3^2 = 54, against the direct sum's 36.
    let (n2, h2) = iota(3, 2);
    let out2 = substitute(&tt, 6, &h2, 3);
    assert_eq!(out2.len(), 6 * n2 * n2);
    assert_eq!(out2.len(), 54);
    assert!(out2.iter().all(|m| m.count_ones() == 4));
    assert_eq!(find_sunflower_128(&out2), None, "g(4) >= 54 refuted");
    assert!(54 > 36, "direct sum reaches only 6^2");

    // b = 3: g(6) >= 6 * 10^2 = 600, against 20^2 = 400 from doubling.
    let (n3, h3) = iota(6, 3);
    let out3 = substitute(&tt, 6, &h3, 6);
    assert_eq!(out3.len(), 6 * n3 * n3);
    assert_eq!(out3.len(), 600);
    assert!(out3.iter().all(|m| m.count_ones() == 6));
    assert_eq!(find_sunflower_128(&out3), None, "g(6) >= 600 refuted");
    assert!(600 > 400);
}

/// And the substitution stops working the moment the inner family is
/// not intersecting -- which is what says the hypothesis is the theorem
/// rather than an artefact of the proof.
#[test]
fn substitution_needs_intersecting() {
    let tt: Vec<u32> = vec![0b000011, 0b000101, 0b000110, 0b011000, 0b101000, 0b110000];
    let (_, h3) = iota(6, 3);

    // Same inner family, one member swapped for a disjoint one.
    let mut broken = h3.clone();
    broken.truncate(2);
    broken.push(0b111000);
    verify(&broken, 3, false).expect("the broken inner family is still valid");
    assert!(
        broken.iter().any(|a| broken.iter().any(|b| a & b == 0)),
        "and it is genuinely not intersecting"
    );

    let out = substitute(&tt, 6, &broken, 6);
    assert!(
        find_sunflower_128(&out).is_some(),
        "a non-intersecting inner family should break the substitution"
    );
}

/// `iota(b) <= b * g(b-1)`: every member meets a fixed member, so some
/// point of it has degree at least `|F| / b`, and the link there is
/// sunflower-free of uniformity `b-1`. A sanity bound the search must
/// respect.
#[test]
fn iota_respects_the_link_bound() {
    // g(1) = 2, g(2) = 6 are proved exactly in Coq.
    assert!(iota(9, 2).0 <= 2 * 2);
    assert!(iota(11, 3).0 <= 3 * 6);
}
