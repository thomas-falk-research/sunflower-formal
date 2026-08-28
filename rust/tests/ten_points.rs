//! `ι(4,10) = 27`: a tenth point buys nothing.
//!
//! `docs/roadmap.md` §46. The upper half is a SAT run too long to be a
//! test — `iota_sym 4 10 28`, sixteen coarse cubes plus a 144-way
//! degree-sequence split of the floor cube, 41.5 core-hours, recorded in
//! `docs/ladder/iota4_10.t28.tsv`. What is cheap enough to check here is
//! the lower half, the arithmetic the split rests on, and the
//! consistency of the 144 sequences that run reported.
//!
//! The two halves:
//!
//! ```text
//!   iota(4,10) >= 27   the nine-point family embeds (this file)
//!   iota(4,10) <= 27   iota_sym, UNSAT for 28  (the ladder record)
//! ```
//!
//! Together with `Support.four_uniform_on_nine_is_exactly_27` that gives
//! `ι(4,9) = ι(4,10) = 27`, which is the evidence — not proof — that the
//! Abbott–Hanson–Sauer construction is genuinely extremal rather than
//! merely the only one anyone has built (§44).

use std::collections::HashSet;

fn is_sunflower(a: u32, b: u32, c: u32) -> bool {
    let ab = a & b;
    ab == (a & c) && ab == (b & c)
}

/// `Product.iota4`, the Abbott–Hanson–Sauer family on nine points.
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

/// The lower half: `ι(4,10) ≥ 27`, because a family on nine points is a
/// family on ten that happens not to use the tenth.
///
/// Trivial, and stated anyway: the exact value is a *pair* of bounds, and
/// a ladder record carrying only the upper one invites the reading that
/// `ι(4,10)` might be smaller than `ι(4,9)`, which no monotone quantity
/// can be.
#[test]
fn the_nine_point_family_embeds_in_ten_points() {
    let f = iota4();
    assert_eq!(f.len(), 27);

    // Still 4-uniform, distinct, intersecting, sunflower-free when the
    // ground set is widened to [10] — nothing about the family changed.
    assert!(f.iter().all(|s| s.count_ones() == 4));
    let uniq: HashSet<u32> = f.iter().copied().collect();
    assert_eq!(uniq.len(), 27);
    for i in 0..f.len() {
        for j in i + 1..f.len() {
            assert!(f[i] & f[j] != 0, "not intersecting");
            for k in j + 1..f.len() {
                assert!(!is_sunflower(f[i], f[j], f[k]), "3-sunflower");
            }
        }
    }
    // It uses nine of the ten points, leaving point 9 unused.
    let support = f.iter().fold(0u32, |a, &s| a | s);
    assert_eq!(support.count_ones(), 9);
    assert_eq!(support & (1 << 9), 0, "point 9 should be unused");
    assert!(support < (1 << 10), "lives inside a ten-point ground set");
}

/// Why the floor cube is `deg(0) = 12`, and why it is near-regular.
///
/// This is the arithmetic that made the ten-point probe finish: sixteen
/// of seventeen cubes fell quickly and everything hard was concentrated
/// in one, because the degree sum leaves almost no slack.
#[test]
fn a_twenty_eight_member_family_on_ten_points_is_near_regular() {
    let (members, uniformity, points) = (28usize, 4usize, 10usize);
    let degree_sum = members * uniformity;
    assert_eq!(degree_sum, 112);

    // Mean degree 11.2, so some point has degree >= 12: that is the floor.
    let floor = degree_sum.div_ceil(points);
    assert_eq!(floor, 12);

    // And the run showed max degree <= 12 as well (deg(0) = 13..28 all
    // UNSAT), so any such family is degree-12-capped with only 8 of slack
    // spread over ten points.
    let slack = points * floor - degree_sum;
    assert_eq!(slack, 8);

    // Compare nine points, where the slack is zero and the family is
    // forced exactly 12-regular — §38's Corollary 4.
    assert_eq!(27 * 4, 108);
    assert_eq!(9 * 12, 108);
    assert_eq!(9 * 12 - 27 * 4, 0, "nine points has no slack at all");
}

/// The 144 degree sequences the split reported are internally consistent.
///
/// Not a re-derivation of the split — that would mean reimplementing the
/// symmetry breaking — but a check that the transcription in
/// `docs/ladder/iota4_10.t28.tsv` describes 144 distinct sequences that
/// could each be the degree sequence of a 28-member family with
/// `deg(0) = 12`. A typo in the record would show up here.
#[test]
fn the_recorded_degree_sequences_are_consistent() {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/../docs/ladder/iota4_10.t28.tsv");
    let text = std::fs::read_to_string(path).expect("ladder record missing");

    let mut seqs: Vec<Vec<u32>> = Vec::new();
    for line in text.lines() {
        let line = line.trim();
        if !line.starts_with('[') {
            continue;
        }
        let inner = &line[1..line.find(']').expect("unterminated sequence")];
        seqs.push(inner.split(',').map(|t| t.trim().parse().expect("bad degree")).collect());
    }

    assert_eq!(seqs.len(), 144, "the run reported 144 sequence cubes");
    let uniq: HashSet<Vec<u32>> = seqs.iter().cloned().collect();
    assert_eq!(uniq.len(), 144, "duplicate sequences in the record");

    for s in &seqs {
        assert_eq!(s.len(), 10, "not ten points: {s:?}");
        assert_eq!(s.iter().sum::<u32>(), 112, "degree sum is not 4*28: {s:?}");
        assert_eq!(*s.iter().max().unwrap(), 12, "maximum degree is not 12: {s:?}");
        assert_eq!(s[0], 12, "max_at_zero puts the maximum first: {s:?}");
        // Every degree is a link size, so bounded by g(3,9) = 14 — far
        // from binding here, but it is the bound that governs.
        assert!(s.iter().all(|&d| d <= 14), "degree exceeds g(3,9): {s:?}");
    }

    // The sequences are sorted within blocks, not globally, so they are
    // NOT monotone — that is the sorted_blocks symmetry, and a reader
    // expecting monotone entries would think the record corrupt.
    assert!(
        seqs.iter().any(|s| s.windows(2).any(|w| w[0] < w[1])),
        "if every sequence were monotone the symmetry would be global"
    );
}
