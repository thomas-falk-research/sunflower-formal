//! The uniformity-5 row, and why it is the one that moved.
//!
//! `docs/roadmap.md` §11.6 had `iota(5) >= 54`, from
//! `cone(substitute(g(2), iota(2)))`. Uniformity 5 is the row where the
//! Abbott-Hanson-Sauer substitution cannot be used at all — 5 is prime,
//! so `substitute` has no factorisation to work with — and it is the only
//! row the plateau search of `rust/src/plateau.rs` moved.
//!
//! The family below is what it found: **78 members on fifteen points**,
//! `plateau_run 5 15 200000 1`. It is stored rather than recomputed
//! because a search is not a definition, and because the first pass of
//! this session logged sizes without families and lost a 78 it had
//! already found.
//!
//! What it is not: a record. `78^(1/4) = 2.972` against the 1972 rate of
//! `10^(1/2) = 3.162`, and the sharp conjecture allows `iota(5) <= 100`.
//! It closes `54 -> 78` of a `54 -> 100` gap. `iota_five_does_not_beat_1972`
//! asserts that, so a future session does not mistake a bigger number for
//! a better rate — the same guard `sharp_conjecture.rs` puts on the table.

use sunflower_formal::intersecting::verify;
use sunflower_formal::structure;

/// 78 intersecting 5-sets on `{0,...,14}`, no 3-sunflower.
const IOTA5: &[u32] = &[
    0x00001f, 0x0048b0, 0x00007a, 0x00410d, 0x004306, 0x0009c8, 0x004858, 0x004078,
    0x004286, 0x00028b, 0x000313, 0x0001e8, 0x000195, 0x001a41, 0x004095, 0x000394,
    0x004309, 0x000664, 0x000117, 0x00021b, 0x0048a2, 0x0040e2, 0x001825, 0x0009a8,
    0x000391, 0x004942, 0x004294, 0x000316, 0x002261, 0x002a21, 0x004922, 0x002a41,
    0x0009b0, 0x000172, 0x004838, 0x004219, 0x00430c, 0x000952, 0x004283, 0x0048d0,
    0x0040f0, 0x004291, 0x00008f, 0x004928, 0x000465, 0x000c45, 0x004948, 0x00421c,
    0x0001f0, 0x0008aa, 0x0000ea, 0x000932, 0x00401d, 0x004303, 0x00018d, 0x004087,
    0x000389, 0x004168, 0x0048c2, 0x002845, 0x00021e, 0x00028e, 0x004107, 0x00038c,
    0x0008ca, 0x000e44, 0x00085a, 0x00083a, 0x004162, 0x002065, 0x001a44, 0x0009d0,
    0x001264, 0x000e24, 0x001261, 0x002a24, 0x000e21, 0x000c25,
];

#[test]
fn iota_five_is_at_least_78() {
    assert_eq!(IOTA5.len(), 78);
    verify(IOTA5, 5, true).expect("the pinned iota(5) family is invalid");
    assert_eq!(
        structure::support(IOTA5).count_ones(),
        15,
        "the family moved off fifteen points"
    );
    // It beats what the repository had, which came from the cone.
    assert!(IOTA5.len() > 54, "the previous best at b = 5 was 54");
}

/// The guard: a bigger number is not a better rate.
///
/// `iota(b)` beats Abbott-Hanson-Sauer exactly when `iota(b)^2 > 10^(b-1)`
/// — squared so nothing leaves the integers, the same form as
/// `Sharp.AHSOptimal`.
#[test]
fn iota_five_does_not_beat_1972() {
    let n = IOTA5.len() as u128;
    assert!(
        n * n <= 10u128.pow(4),
        "78 members at b = 5 would refute Sharp.AHSOptimal -- check by hand"
    );
    // The threshold, for the record: 101 members.
    assert!(101u128 * 101 > 10u128.pow(4));
    assert!(100u128 * 100 <= 10u128.pow(4));
}

/// Every point is used and no point is used too often: the degree bound
/// `deg(x) <= g(4)` that `PureLink.link_at_point_bounded` proves, checked
/// on the object.
#[test]
fn the_pinned_family_respects_the_link_bound() {
    let degs = structure::degree_sequence(IOTA5);
    assert_eq!(degs.len(), 15);
    for (x, d) in &degs {
        assert!(*d >= 1, "point {x} is unused but counted in the support");
        // g(4) <= 160 by PureLink.g_four_at_most_160.
        assert!(*d <= 160, "point {x} has degree {d}, above g(4) <= 160");
    }
    // And the support bound of PureLink.intersecting_support_bound:
    // 5 + 4 * 77 = 313, which fifteen points is comfortably inside.
    assert!(structure::support(IOTA5).count_ones() <= 5 + 4 * 77);
}
