//! Falsification and instrumentation for `coq/StarDefect.v`.
//!
//! `rho(F) = |F| / maxdeg(F)` is the ratio Erdős–Rado's first step
//! bounds, and `Intersecting.sunflower_free_star_bound` proves
//! `rho <= 2b`. A *constant* bound would settle the sunflower conjecture
//! at `k = 3` outright, so the question is whether one exists.
//!
//! `rust/tests/iota_sandwich.rs` has measured the worst ratio for a
//! while — 2, 3, 2.75 at uniformities 1, 2, 3 against the proved 2, 4, 6
//! — and that row looks flat. This file is what says it is not, and it
//! ran before any of `coq/StarDefect.v` was written.
//!
//! Four jobs.
//!
//! 1. **The chain identity.** `|F| = rho_0 * rho_1 * ... * rho_{b-1}`
//!    exactly, because each level's maximum degree is the next level's
//!    size. Checked as a telescope rather than as a product, since the
//!    individual ratios are not integers.
//! 2. **`rho` is multiplicative under the substitution**, in exact
//!    rational arithmetic, on every pair the repository can build.
//! 3. **Hence unbounded.** Iterating on `iota(3)` gives `rho = 2^k` at
//!    `b = 3^k`; verified directly at `b = 3` and `b = 9`, where the
//!    10000-member family has maximum degree exactly 2500.
//! 4. **The witness `coq/StarDefect.v` carries.**
//!    `star_bounded_needs_c_at_least_five` rests on the doubling of
//!    `iota(4,9)` having 54 members and maximum degree 12; both are
//!    checked here, against a family rebuilt rather than quoted.

use sunflower_formal::{intersecting, ratio, structure};

fn masks(sets: &[&[u32]]) -> Vec<u32> {
    sets.iter()
        .map(|s| s.iter().fold(0u32, |a, &x| a | 1 << x))
        .collect()
}

fn triangle() -> Vec<u32> {
    masks(&[&[0, 1], &[0, 2], &[1, 2]])
}

fn two_triangles() -> Vec<u32> {
    masks(&[&[0, 1], &[1, 2], &[0, 2], &[3, 4], &[4, 5], &[3, 5]])
}

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

fn iota4() -> Vec<u32> {
    vec![
        15, 23, 27, 45, 46, 53, 54, 57, 58, 195, 204, 212, 216, 225, 226, 323, 332, 340, 344, 353,
        354, 387, 396, 404, 408, 417, 418,
    ]
}

/// Two disjoint copies on shifted ground sets. Valid only when `f` is
/// intersecting, which is `Intersecting.double_no_sunflower`.
fn doubled_128(f: &[u128], shift: u32) -> Vec<u128> {
    let mut out = f.to_vec();
    out.extend(f.iter().map(|&a| a << shift));
    out
}

// ---------------------------------------------------------------------
// 1. The chain identity
// ---------------------------------------------------------------------

/// The greedy chain telescopes, so the product of its ratios is `|F|`
/// exactly. That identity is what makes `rho` the quantity Erdős–Rado's
/// recursion pays: the conjecture is that the product is `C^b`.
#[test]
fn the_greedy_chain_telescopes_to_the_family_size() {
    let cases: Vec<(Vec<u128>, u32, bool)> = vec![
        (structure::widen(&triangle()), 2, true),
        (structure::widen(&two_triangles()), 2, false),
        (structure::widen(&iota3()), 3, true),
        (structure::widen(&iota4()), 4, true),
        (doubled_128(&structure::widen(&iota3()), 6), 3, false),
        (doubled_128(&structure::widen(&iota4()), 9), 4, false),
        (intersecting::substitute(&triangle(), 3, &iota3(), 6), 6, true),
    ];
    for (f, b, inter) in cases {
        structure::verify_128(&f, b, inter).expect("a chain case does not verify");
        let chain = ratio::greedy_chain(&f, b);
        assert_eq!(chain.len(), b as usize, "the chain did not reach the bottom");
        for w in chain.windows(2) {
            assert_eq!(
                w[0].deg, w[1].size,
                "the chain does not telescope: level sizes disagree"
            );
        }
        assert_eq!(chain[0].size, f.len());
        // The bottom level is a single empty set.
        assert_eq!(chain[chain.len() - 1].deg, 1, "the chain did not bottom out at 1");
    }
}

// ---------------------------------------------------------------------
// 2. rho is multiplicative under the substitution
// ---------------------------------------------------------------------

/// `rho(substitute(G,H)) = rho(G) rho(H)`, in exact rational
/// arithmetic. This is the mechanism: `|F| = |G| |H|^a` and
/// `maxdeg(F) = maxdeg(G) maxdeg(H) |H|^(a-1)`, so the `|H|^(a-1)`
/// cancels.
#[test]
fn rho_is_multiplicative_under_the_substitution() {
    let tri = triangle();
    let tt = two_triangles();
    let i3 = iota3();
    let cases: &[(&str, &[u32], u32, &[u32], u32, bool)] = &[
        ("substitute(iota(2), iota(2))", &tri, 3, &tri, 3, true),
        ("substitute(iota(2), iota(3))", &tri, 3, &i3, 6, true),
        ("substitute(iota(3), iota(2))", &i3, 6, &tri, 3, true),
        ("substitute(iota(3), iota(3))", &i3, 6, &i3, 6, true),
        ("substitute(g(2), iota(2))", &tt, 6, &tri, 3, false),
        ("substitute(g(2), iota(3))", &tt, 6, &i3, 6, false),
    ];
    for &(name, g, vg, h, wg, inter) in cases {
        let f = intersecting::substitute(g, vg, h, wg);
        let b = (g[0].count_ones() * h[0].count_ones()) as u32;
        structure::verify_128(&f, b, inter).unwrap_or_else(|e| panic!("{name}: {e}"));
        let (gn, gd) = ratio::rho_128(&structure::widen(g));
        let (hn, hd) = ratio::rho_128(&structure::widen(h));
        let (fnum, fden) = ratio::rho_128(&f);
        assert_eq!(
            gn * hn * fden,
            fnum * gd * hd,
            "{name}: rho({gn}/{gd}) * rho({hn}/{hd}) != {fnum}/{fden}"
        );
    }
}

/// The doubling multiplies `rho` by two: the copies do not share points,
/// so the degrees are unchanged while the family doubles. This is the
/// only other operation in the repository that moves `rho`, and it
/// cannot be iterated — the doubling of an intersecting family is not
/// intersecting, and `Audit.intersecting_is_needed_in_the_doubling` is
/// why.
#[test]
fn the_doubling_doubles_rho() {
    for (f, b, shift) in [
        (structure::widen(&triangle()), 2u32, 3u32),
        (structure::widen(&iota3()), 3, 6),
        (structure::widen(&iota4()), 4, 9),
    ] {
        let d = doubled_128(&f, shift);
        structure::verify_128(&d, b, false).expect("a doubling does not verify");
        let (n, den) = ratio::rho_128(&f);
        let (dn, dden) = ratio::rho_128(&d);
        assert_eq!(dn * den, 2 * n * dden, "the doubling did not double rho");
    }
}

// ---------------------------------------------------------------------
// 3. Hence unbounded
// ---------------------------------------------------------------------

/// `rho = 2^k` at `b = 3^k` on the tower, verified where the family can
/// be built. `b = 27` has `10^13` members and is arithmetic only, which
/// is asserted by its absence rather than glossed over.
#[test]
fn the_substitution_tower_drives_rho_to_infinity() {
    // k = 1: iota(3) itself.
    let f3 = structure::widen(&iota3());
    assert_eq!(ratio::rho_128(&f3), (10, 5), "rho(iota(3)) is not 2");

    // k = 2: substitute(iota(3), iota(3)), 10000 members on 36 points.
    let f9 = intersecting::substitute(&iota3(), 6, &iota3(), 6);
    assert_eq!(f9.len(), 10_000);
    structure::verify_128(&f9, 9, true).expect("the b = 9 tower does not verify");
    let (n9, d9) = ratio::rho_128(&f9);
    assert_eq!((n9, d9), (10_000, 2_500), "rho at b = 9 is not 4");

    // So rho(2^k) at b = 3^k, i.e. rho = b^(log_3 2) = b^0.6309...
    // and the proved ceiling 2b is never reached: 4 against 18 at b = 9.
    assert!(4 * 1 < 2 * 9);
    // The exponent, as a numeric fact rather than prose.
    let exponent = (2f64).ln() / (3f64).ln();
    assert!((exponent - 0.6309).abs() < 1e-4, "the growth exponent moved");
    // b = 27 is arithmetic only.
    let members_at_27 = 10f64.powf((27.0 - 1.0) / 2.0);
    assert!(members_at_27 > 1e12, "the b = 27 row is not out of reach after all");
}

/// The proved ceilings, checked on everything: `rho <= 2b` for
/// sunflower-free families and `rho <= b` for intersecting ones. A
/// construction that violated either would be a counterexample to
/// `Intersecting.sunflower_free_star_bound` or to
/// `Intersecting.intersecting_link_bound`.
#[test]
fn every_family_respects_the_proved_ceilings() {
    let rows: Vec<(&str, Vec<u128>, u32, bool)> = vec![
        ("iota(2)", structure::widen(&triangle()), 2, true),
        ("g(2)", structure::widen(&two_triangles()), 2, false),
        ("iota(3)", structure::widen(&iota3()), 3, true),
        ("iota(4,9)", structure::widen(&iota4()), 4, true),
        ("double(iota(3))", doubled_128(&structure::widen(&iota3()), 6), 3, false),
        ("double(iota(4,9))", doubled_128(&structure::widen(&iota4()), 9), 4, false),
        (
            "substitute(iota(2), iota(3))",
            intersecting::substitute(&triangle(), 3, &iota3(), 6),
            6,
            true,
        ),
        (
            "substitute(g(2), iota(3))",
            intersecting::substitute(&two_triangles(), 6, &iota3(), 6),
            6,
            false,
        ),
        (
            "substitute(iota(3), iota(3))",
            intersecting::substitute(&iota3(), 6, &iota3(), 6),
            9,
            true,
        ),
    ];
    for (name, f, b, inter) in rows {
        structure::verify_128(&f, b, inter).unwrap_or_else(|e| panic!("{name}: {e}"));
        let (n, d) = ratio::rho_128(&f);
        assert!(n <= 2 * (b as usize) * d, "{name}: rho > 2b");
        if inter {
            assert!(n <= (b as usize) * d, "{name}: rho > b for an intersecting family");
        }
        // And every one of them is inside the chain identity.
        let chain = ratio::greedy_chain(&f, b);
        assert_eq!(chain.len(), b as usize, "{name}: short chain");
    }
}

// ---------------------------------------------------------------------
// 4. The witness the Coq carries
// ---------------------------------------------------------------------

/// `StarDefect.star_bounded_needs_c_at_least_five` rests on exactly two
/// numbers: the doubling of `iota(4,9)` has 54 members and every point
/// of it lies in at most 12. Both are checked here on a family rebuilt
/// from the seed, so the Coq transcription is checked rather than
/// trusted.
#[test]
fn the_coq_witness_has_fifty_four_members_and_maximum_degree_twelve() {
    let d = doubled_128(&structure::widen(&iota4()), 9);
    structure::verify_128(&d, 4, false).expect("double(iota(4,9)) does not verify");
    assert_eq!(d.len(), 54);
    assert_eq!(ratio::maxdeg_128(&d), 12);
    // 54 <= 12c forces c >= 5, and the proved ceiling at b = 4 is 2b = 8.
    assert!(54 > 12 * 4 && 54 <= 12 * 5);
    assert!(54 <= 8 * 12);
}

/// The gap the conjecture actually lives in: on the tower the geometric
/// mean of the chain ratios tends to `sqrt(10)` while the largest single
/// ratio grows without bound. Bounding the maximum would settle the
/// conjecture and is impossible; bounding the mean *is* the conjecture.
#[test]
fn the_mean_stays_bounded_while_the_maximum_does_not() {
    // Measured on the two towers that can be built.
    for (f, b) in [
        (structure::widen(&iota3()), 3u32),
        (intersecting::substitute(&iota3(), 6, &iota3(), 6), 9),
    ] {
        let chain = ratio::greedy_chain(&f, b);
        let (max, geo) = ratio::chain_profile(&chain);
        // The geometric mean is |F|^(1/b) by the telescoping identity.
        let want = (f.len() as f64).powf(1.0 / b as f64);
        assert!(
            (geo - want).abs() < 1e-9,
            "the geometric mean is not |F|^(1/b): {geo} against {want}"
        );
        assert!(geo < 3.1623, "the geometric mean passed sqrt(10)");
        assert!(max >= ratio::rho_value(&f) - 1e-9);
    }
    // And the maximum, which is `rho` itself, doubles each time the
    // uniformity triples.
    let r3 = ratio::rho_value(&structure::widen(&iota3()));
    let r9 = ratio::rho_value(&intersecting::substitute(&iota3(), 6, &iota3(), 6));
    assert!((r3 - 2.0).abs() < 1e-9 && (r9 - 4.0).abs() < 1e-9);
}
