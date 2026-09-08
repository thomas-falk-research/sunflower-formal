//! The two objects certified in `coq/TightThreshold.v` and
//! `coq/TwoCoverSharp.v`, re-checked here by code that shares nothing
//! with the Coq, plus the exhaustive measurement the second file's
//! theorem was written against.
//!
//! * `nine27`: 27 triples on nine points, 9-regular, every pair in at
//!   most three members, no three pairwise disjoint. It satisfies every
//!   hypothesis of `SpreadYieldsDisjoint 3 3 3` except the strict size
//!   bound `27 < |F|`, which it misses by exactly one -- so the threshold
//!   in that statement cannot be weakened to `<=`.
//!
//! * `hm_family`: an intersecting 3-uniform family with covering number
//!   exactly 2 under Rao's caps at `r = 3` (point degree `<= 9`, pair
//!   degree `<= 3`) with `3r + 1 = 10` members, which is what
//!   `TwoCoverSharp.two_cover_at_most_3r_plus_1` says is the most such a
//!   family can have.
//!
//! * The measurement: over every ground set of at most nine points, the
//!   largest intersecting 3-uniform family with covering number exactly
//!   2 under the caps at `r` is `3r + 1` for `r = 3` and `r = 4` (10 and
//!   13) as soon as the ground can hold the extremal shape. The theorem
//!   proves the upper bound for every ground set; this pins that the
//!   constant is not slack on the grounds a search reaches.

use sunflower_formal::spread::{has_k_disjoint, is_distinct, is_rao_spread, is_uniform, Mask};

const NINE27: [[u32; 3]; 27] = [
    [0, 1, 2], [0, 1, 6], [0, 1, 7], [0, 2, 8], [0, 3, 4], [0, 3, 5], [0, 4, 5],
    [0, 6, 7], [0, 7, 8], [1, 2, 3], [1, 2, 5], [1, 3, 4], [1, 3, 8], [1, 5, 6],
    [1, 5, 8], [2, 3, 6], [2, 4, 6], [2, 4, 7], [2, 4, 8], [2, 5, 7], [3, 4, 5],
    [3, 6, 7], [3, 6, 8], [4, 6, 7], [4, 7, 8], [5, 6, 8], [5, 7, 8],
];

const HM_FAMILY: [[u32; 3]; 10] = [
    [0, 2, 4], [0, 2, 5], [0, 2, 6],
    [0, 3, 7], [0, 3, 8], [0, 3, 9],
    [1, 2, 3],
    [0, 1, 10], [0, 1, 11], [0, 1, 12],
];

fn masks(sets: &[[u32; 3]]) -> Vec<Mask> {
    sets.iter().map(|s| s.iter().fold(0u32, |m, &x| m | (1 << x))).collect()
}

fn degree(f: &[Mask], t: Mask) -> usize {
    f.iter().filter(|&&a| a & t == t).count()
}

/// The 27-member family meets every hypothesis of the threshold
/// statement at `(m,k,r) = (3,3,3)` except the strict size bound, and it
/// meets the counting ceiling `9 * 9 / 3 = 27` with equality.
#[test]
fn nine27_is_a_3_spread_family_of_exactly_27_with_no_three_disjoint() {
    let f = masks(&NINE27);
    assert_eq!(f.len(), 27, "3^3 members, not one more");
    assert!(is_uniform(3, &f));
    assert!(is_distinct(&f));
    assert!(is_rao_spread(3, &f, 3, 9), "Rao's absolute condition at r = 3");
    assert!(!has_k_disjoint(&f, 3), "no three pairwise disjoint members");
    // 9-regular: the counting ceiling on nine points is attained.
    for v in 0..9 {
        assert_eq!(degree(&f, 1 << v), 9, "point {v} is in exactly nine members");
    }
    // The pair cap is attained too, so neither cap has slack.
    let max_pair = (0..9)
        .flat_map(|i| (i + 1..9).map(move |j| (1u32 << i) | (1 << j)))
        .map(|p| degree(&f, p))
        .max()
        .unwrap();
    assert_eq!(max_pair, 3);
    // And it does have two disjoint members -- it is not intersecting.
    assert!(has_k_disjoint(&f, 2));
}

/// Any 28-member family with these caps needs at least ten points, by
/// counting: `28 * 3 = 84 > 9 * 9`. So the object above is the largest
/// possible on nine points, not merely the largest found.
#[test]
fn a_28th_member_cannot_live_on_nine_points() {
    assert!(28 * 3 > 9 * 9);
    assert!(27 * 3 <= 9 * 9);
}

fn intersecting(f: &[Mask]) -> bool {
    f.iter().all(|&a| f.iter().all(|&b| a & b != 0))
}

#[test]
fn hm_family_is_intersecting_two_covered_and_has_3r_plus_1_members() {
    let f = masks(&HM_FAMILY);
    assert_eq!(f.len(), 10);
    assert!(is_uniform(3, &f));
    assert!(is_distinct(&f));
    assert!(is_rao_spread(3, &f, 3, 13), "the caps at r = 3");
    assert!(intersecting(&f));
    // {0,1} covers; neither point covers alone.
    assert!(f.iter().all(|&a| a & 0b11 != 0));
    assert!(f.iter().any(|&a| a & 1 == 0));
    assert!(f.iter().any(|&a| a & 2 == 0));
    assert_eq!(f.len(), 3 * 3 + 1);
}

/// The largest intersecting 3-uniform family on `ground` points, with
/// point degree `<= r^2` and pair degree `<= r`, covered by `{0,1}` and
/// by neither point alone. Depth-first over the candidates, which are
/// the 3-subsets meeting `{0,1}`; intersecting-ness is a binary
/// constraint so the search is a maximum-clique search with degree
/// pruning. Exhaustive.
fn max_two_covered(ground: u32, r: u64) -> usize {
    let cands: Vec<Mask> = (0u32..(1 << ground))
        .filter(|s| s.count_ones() == 3 && s & 0b11 != 0)
        .collect();
    let dcap = (r * r) as usize;
    let pcap = r as usize;
    let mut best = 0usize;
    let mut chosen: Vec<Mask> = Vec::new();
    fn ok(chosen: &[Mask], s: Mask, dcap: usize, pcap: usize) -> bool {
        if chosen.iter().any(|&c| c & s == 0) {
            return false;
        }
        for v in 0..32u32 {
            if s & (1 << v) == 0 {
                continue;
            }
            let d = chosen.iter().filter(|&&c| c & (1 << v) != 0).count();
            if d + 1 > dcap {
                return false;
            }
            for w in (v + 1)..32u32 {
                if s & (1 << w) == 0 {
                    continue;
                }
                let p = (1 << v) | (1 << w);
                let dp = chosen.iter().filter(|&&c| c & p == p).count();
                if dp + 1 > pcap {
                    return false;
                }
            }
        }
        true
    }
    fn go(
        i: usize,
        cands: &[Mask],
        chosen: &mut Vec<Mask>,
        best: &mut usize,
        dcap: usize,
        pcap: usize,
    ) {
        if chosen.len() + (cands.len() - i) <= *best {
            return;
        }
        if i == cands.len() {
            // covering number exactly 2: some member misses 0, some misses 1
            let misses0 = chosen.iter().any(|&c| c & 1 == 0);
            let misses1 = chosen.iter().any(|&c| c & 2 == 0);
            if misses0 && misses1 && chosen.len() > *best {
                *best = chosen.len();
            }
            return;
        }
        if ok(chosen, cands[i], dcap, pcap) {
            chosen.push(cands[i]);
            go(i + 1, cands, chosen, best, dcap, pcap);
            chosen.pop();
        }
        go(i + 1, cands, chosen, best, dcap, pcap);
    }
    go(0, &cands, &mut chosen, &mut best, dcap, pcap);
    best
}

/// The exact maximum by ground set. It reaches `3r + 1` once the ground
/// is large enough to hold the extremal shape -- seven points at `r = 3`,
/// eight at `r = 4` -- and then stays there, which is what the theorem
/// says it must do for every larger ground. (`TwoCover.two_cover_bound`
/// proved `max(4r, 3r+4)`, which is 13 and 16 here; the truth is 10 and
/// 13.) These values agree with an independent CP-SAT computation on
/// nine and eleven points recorded in `docs/roadmap.md` §56.
#[test]
fn two_covered_maximum_is_3r_plus_1_on_small_grounds() {
    let rows: [(u32, u64, usize); 8] = [
        (6, 3, 9), (7, 3, 10), (8, 3, 10), (9, 3, 10),
        (6, 4, 10), (7, 4, 12), (8, 4, 13), (9, 4, 13),
    ];
    for (ground, r, expect) in rows {
        assert_eq!(max_two_covered(ground, r), expect, "r = {r}, ground {ground}");
    }
    assert_eq!(3 * 3 + 1, 10);
    assert_eq!(3 * 4 + 1, 13);
}
