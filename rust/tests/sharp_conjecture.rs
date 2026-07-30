//! The standing falsification target: `iota(b)^2 <= 10^(b-1)`.
//!
//! `coq/Sharp.v` proves that the sunflower conjecture at `k = 3` is
//! *exactly* the boundedness of `iota(b)^(1/(b-1))`, and names the sharp
//! form of it:
//!
//! ```text
//!   AHSOptimal  :=  for every b >= 1,  iota(b)^2 <= 10^(b-1)
//! ```
//!
//! — i.e. `iota(b) <= 10^((b-1)/2)`, i.e. the Abbott–Hanson–Sauer
//! substitution is optimal and `L = sqrt(10)`. The squared form is used
//! everywhere here and in the Coq so that nothing leaves the integers.
//!
//! This file is not a proof of anything. It is the *target*: a table with
//! a number in it for every uniformity, so that any future session can
//! ask "did I beat 1972?" without re-deriving the threshold. Three jobs:
//!
//! 1. **Tabulate the thresholds.** `threshold(b)` is the least family
//!    size at uniformity `b` that would refute `AHSOptimal`. The values
//!    at `b = 4..9` are written out by hand and checked against the
//!    computation, because a threshold table that silently drifted is
//!    exactly the failure mode a future session would not notice.
//!
//! 2. **Run every construction the repository has against it.** The rows
//!    of the `iota` table are *rebuilt* here and re-verified by
//!    `structure::verify_128`, not quoted — and then measured against the
//!    threshold. Every one falls short, which is forced (the
//!    substitution's own fixed point is `10^(1/2)`) and is asserted so a
//!    bigger number is not mistaken for a better rate.
//!
//! 3. **Pin where the bound is tight.** It is met with *equality* at
//!    `b = 3`, where `iota(3)^2 = 100 = 10^2`. That single equality is
//!    the whole reason the constant is `sqrt(10)` and not something else,
//!    and it is why the 3-adic tower `b = 3, 9, 27, ...` sits exactly on
//!    the threshold: at those uniformities the substitution gives
//!    precisely `10^((b-1)/2)` and the record falls at `+1`.

use sunflower_formal::{intersecting, structure};

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

/// `10^(b-1)`, the right-hand side of the sharp bound.
fn rhs(b: u32) -> u128 {
    10u128.pow(b - 1)
}

/// The least `N` with `N^2 > 10^(b-1)`: the smallest family at uniformity
/// `b` that would refute `AHSOptimal`, hence beat Abbott–Hanson–Sauer.
fn threshold(b: u32) -> u128 {
    let r = rhs(b);
    // Integer square root by bisection. `hi` has to clear `10^(b-1)`
    // itself at the largest `b` any caller uses -- at `b = 27` that is
    // `10^13`, well past `1 << 40`, and a `hi` that is too small returns
    // a plausible-looking wrong answer rather than failing. `mid * mid`
    // stays inside `u128` because `(1 << 60)^2 = 2^120`.
    let (mut lo, mut hi) = (0u128, 1u128 << 60);
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if mid * mid > r {
            hi = mid;
        } else {
            lo = mid + 1;
        }
    }
    lo
}

/// Does a family of `n` members at uniformity `b` refute the sharp
/// conjecture? This is the one predicate a future session needs.
fn refutes(b: u32, n: u128) -> bool {
    n * n > rhs(b)
}

// ---------------------------------------------------------------------
// 1. The thresholds
// ---------------------------------------------------------------------

/// The table, written out. A drift in `threshold` is a failing assertion,
/// not a quietly different target.
#[test]
fn the_threshold_table_is_what_the_roadmap_says() {
    // (b, the least family size that beats 1972 at that uniformity)
    let table: &[(u32, u128)] = &[
        (1, 2),
        (2, 4),
        (3, 11),
        (4, 32),
        (5, 101),
        (6, 317),
        (7, 1001),
        (8, 3163),
        (9, 10001),
    ];
    for &(b, t) in table {
        assert_eq!(
            threshold(b),
            t,
            "the threshold at b = {b} moved: {} against the tabulated {t}",
            threshold(b)
        );
        assert!(refutes(b, t), "the threshold at b = {b} does not refute");
        assert!(
            !refutes(b, t - 1),
            "one below the threshold at b = {b} already refutes"
        );
    }
}

/// The 3-adic tower sits *exactly* on the threshold: at `b = 3^j` the
/// substitution gives precisely `10^((b-1)/2)` and the record falls at
/// `+1`. So any single improvement anywhere propagates up the whole
/// tower, which is why `b = 9` needs exactly one more set.
#[test]
fn the_three_adic_tower_is_exactly_on_the_threshold() {
    // iota(3) = 10; the substitution iterated at 3, 9, 27 gives
    // iota(3^j) >= 10^((3^j - 1)/2) exactly.
    for j in 1..=3u32 {
        let b = 3u32.pow(j);
        let attained = 10u128.pow((b - 1) / 2);
        assert_eq!(
            attained * attained,
            rhs(b),
            "the tower at b = {b} is not exactly on the bound"
        );
        assert_eq!(
            threshold(b),
            attained + 1,
            "the tower at b = {b} does not miss the record by exactly one"
        );
    }
}

// ---------------------------------------------------------------------
// 2. Every construction, rebuilt and measured
// ---------------------------------------------------------------------

/// Rebuild the rows of the `iota` table, re-verify each with a checker
/// that shares no code with the construction, and measure each against
/// its threshold. **None of them refutes**, and that is forced rather
/// than lucky: the substitution's own fixed point is `10^(1/2)`.
///
/// The row at `b = 8` is stated in `docs/roadmap.md` §11.6 and *not*
/// verified there (2187 members is 1.7e9 triples). It is not rebuilt
/// here either; its arithmetic is checked, and the fact that it is
/// unverified is asserted by its absence from the rebuilt list.
#[test]
fn no_construction_in_the_repository_refutes_the_sharp_conjecture() {
    let tri = triangle();
    let tt = two_triangles();
    let i3 = iota3();
    let i4 = iota4();

    // The exhaustive rows, as families.
    let mut rows: Vec<(u32, Vec<u128>, String)> = vec![
        (2, structure::widen(&tri), "iota(2) = 3, exhaustive".into()),
        (3, structure::widen(&i3), "iota(3) = 10, exhaustive".into()),
        (4, structure::widen(&i4), "iota(4,9) = 27, exhaustive".into()),
    ];

    // b = 5: cone(substitute(g(2), iota(2))) -- 54 members.
    {
        let g4 = intersecting::substitute(&tt, 6, &tri, 3);
        let h = structure::cone_128(&g4, 6 * 3);
        rows.push((5, h, "cone(substitute(g(2), iota(2)))".into()));
    }
    // b = 6: substitute(iota(2), iota(3)) -- 300 members.
    {
        let h = intersecting::substitute(&tri, 3, &i3, 6);
        rows.push((6, h, "substitute(iota(2), iota(3))".into()));
    }
    // b = 7: cone(substitute(g(2), iota(3))) -- 600 members.
    {
        let g6 = intersecting::substitute(&tt, 6, &i3, 6);
        let h = structure::cone_128(&g6, 6 * 6);
        rows.push((7, h, "cone(substitute(g(2), iota(3)))".into()));
    }

    println!("\n  b   members   threshold   fraction   route");
    for (b, f, route) in &rows {
        structure::verify_128(f, *b, true)
            .unwrap_or_else(|e| panic!("row b = {b} ({route}) failed verification: {e}"));
        let n = f.len() as u128;
        let t = threshold(*b);
        println!(
            "  {b}   {n:>7}   {t:>9}   {:>8.3}   {route}",
            n as f64 / t as f64
        );
        assert!(
            !refutes(*b, n),
            "row b = {b} ({route}) refutes the sharp conjecture with {n} members \
             against a threshold of {t} -- this would be the first improvement \
             on Abbott-Hanson-Sauer since 1972 and must be checked by hand \
             before it is believed"
        );
    }

    // The unverified b = 8 row, arithmetic only.
    assert!(
        !refutes(8, 3 * 27 * 27),
        "the (unverified) b = 8 row would refute the sharp conjecture"
    );
    // And it is absent from the rebuilt rows, which is the point of
    // recording it as unverified.
    assert!(rows.iter().all(|(b, _, _)| *b != 8));
}

/// The fractions of the threshold attained, pinned. `docs/roadmap.md`
/// §12 quotes them; a construction that improved would move one of these
/// and fail here rather than drift.
#[test]
fn the_fractions_of_the_threshold_are_what_section_twelve_says() {
    let known: &[(u32, u128, f64)] = &[
        (4, 27, 0.844),
        (5, 54, 0.535),
        (6, 300, 0.946),
        (7, 600, 0.599),
        (8, 2187, 0.691),
        (9, 10_000, 0.9999),
    ];
    for &(b, n, want) in known {
        let got = n as f64 / threshold(b) as f64;
        assert!(
            (got - want).abs() < 5e-4,
            "the fraction at b = {b} moved: {got:.4} against the quoted {want}"
        );
    }
}

// ---------------------------------------------------------------------
// 3. Tightness, and the arithmetic the Coq needs
// ---------------------------------------------------------------------

/// Where the bound is met with equality, and where it is not. `b = 3` is
/// the only uniformity at which the sharp bound is *attained*, and that
/// equality is the whole content of Abbott–Hanson–Sauer.
#[test]
fn the_sharp_bound_is_attained_exactly_at_three() {
    // Attained: iota(3)^2 = 100 = 10^2.
    assert_eq!(10u128 * 10, rhs(3));
    // Not attained anywhere else the search decided.
    assert!(3u128 * 3 < rhs(2), "b = 2 is not slack");
    assert!(27u128 * 27 < rhs(4), "b = 4 is not slack");
    // And one more member at b = 3 would refute.
    assert!(refutes(3, 11));
    assert!(!refutes(3, 10));
}

/// The arithmetic `coq/Sharp.v` turns the sharp bound into a bound of the
/// shape `iota(b) <= C^(b-1)`, with `C = 4`: `10^(b-1) <= (4^(b-1))^2`.
/// Checked numerically before it is proved, per `docs/testing.md`.
#[test]
fn the_sharp_bound_gives_a_base_four_bound() {
    for b in 1..=20u32 {
        let c = 4u128.pow(b - 1);
        assert!(
            rhs(b) <= c * c,
            "10^(b-1) <= (4^(b-1))^2 failed at b = {b}"
        );
    }
    // And base 3 does not work, so 4 is not an arbitrary choice: the
    // sharp rate sqrt(10) = 3.162... is genuinely above 3.
    let mut base_three_fails_somewhere = false;
    for b in 1..=40u32 {
        let c = 3u128.pow(b - 1);
        if rhs(b) > c * c {
            base_three_fails_somewhere = true;
            break;
        }
    }
    assert!(
        base_three_fails_somewhere,
        "base 3 would have sufficed, so the choice of 4 is not forced"
    );
}

/// The shifted exponent is not a cosmetic reindexing: `C^(b-1)` is
/// strictly smaller than `C^b` at every `b >= 1` and every `C >= 2`. So
/// `coq/Sharp.v`'s equivalence really does move the statement, and the
/// constant has to move with it.
#[test]
fn the_shift_in_the_exponent_is_a_real_change() {
    for c in 2..=6u128 {
        for b in 1..=12u32 {
            assert!(
                c.pow(b - 1) < c.pow(b),
                "C^(b-1) < C^b failed at C = {c}, b = {b}"
            );
        }
    }
    // And the equivalence's constant: iota(b) <= C^b for all b implies
    // iota(b) <= (C^2)^(b-1) for all b >= 1. Checked as arithmetic.
    for c in 1..=6u128 {
        for b in 1..=12u32 {
            assert!(
                c.pow(b) <= (c * c).pow(b - 1) || b == 1,
                "C^b <= (C^2)^(b-1) failed at C = {c}, b = {b}"
            );
        }
        // At b = 1 the claim is iota(1) <= 1, which is a theorem
        // (`Product.iota_one_at_most_one`), not arithmetic.
        assert_eq!((c * c).pow(0), 1);
    }
}
