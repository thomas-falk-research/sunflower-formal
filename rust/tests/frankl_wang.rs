//! Frankl–Wang's `G(n,k)`, the extremal intersecting family with
//! covering number three, tested against this development's bound.
//!
//! `docs/roadmap.md` §37.5 asked whether the covering-number literature
//! could close the `ι(4,11)` rung on paper: `τ ∈ {3,4}` is forced there,
//! so a literature maximum below 32 for both cases would end it. A
//! commissioned search answered no, and this file checks the load-bearing
//! half of that answer first-hand rather than taking it on report.
//!
//! The construction is quoted verbatim from Frankl–Wang, *Intersecting
//! families with covering number three*, arXiv:2207.05487v3, Example 1.3
//! (published as J. Combin. Theory Ser. B 171 (2025), 96–139):
//!
//! ```text
//!   B = {[2, k + 1], {2} ∪ [k + 2, 2k], {3} ∪ [k + 2, 2k]}
//!   A = { A ∈ ([n] choose k) : 1 ∈ A and A ∩ B ≠ ∅ for each B ∈ B }
//!   Set G(n, k) = A ∪ B.
//! ```
//!
//! *"It is easy to check that for n ≥ 2k, G(n, k) is an intersecting
//! k-graph with τ(G) = 3."*
//!
//! ## What it decides for the ladder
//!
//! At `n = 11, k = 4` this has **74** members. So an intersecting
//! 4-uniform family on eleven points with `τ = 3` can be more than twice
//! the 32 the rung is looking for, and no bound from that literature can
//! exclude 32. The reduction below 32 has to come from
//! 3-sunflower-freeness, and no published theorem combines the two.
//!
//! ## The prediction this development makes about it
//!
//! `PureLink.iota_four_at_most_71_if_iota_three_is_ten` gives
//! `ι(4) ≤ 71` on the exhaustive `ι(3) = 10` of `wide.rs`. 74 > 71, so
//! **`G(11,4)` cannot be sunflower-free** — a falsifiable prediction
//! about a published construction this development did not build. It is
//! checked below, and it holds: the family contains 3481 three-sunflowers.

use std::collections::HashSet;

use sunflower_formal::wide;

/// `[a, b]` as a bitmask on points `1..=n`, bit `i` for point `i`.
fn interval(a: u32, b: u32) -> u64 {
    (a..=b).fold(0u64, |m, i| m | 1 << i)
}

/// Frankl–Wang `G(n, k)`, Example 1.3.
fn g(n: u32, k: u32) -> Vec<u64> {
    let bs = [
        interval(2, k + 1),
        (1u64 << 2) | interval(k + 2, 2 * k),
        (1u64 << 3) | interval(k + 2, 2 * k),
    ];
    let mut out: Vec<u64> = wide::subsets(n + 1, k)
        .into_iter()
        // `subsets(n+1, k)` gives the k-subsets of {0,..,n}; keep those
        // avoiding 0, containing 1, and meeting every member of B.
        .filter(|s| s & 1 == 0 && s & (1 << 1) != 0 && bs.iter().all(|b| s & b != 0))
        .collect();
    for b in bs {
        if !out.contains(&b) {
            out.push(b);
        }
    }
    out
}

fn is_sunflower(a: u64, b: u64, c: u64) -> bool {
    let ab = a & b;
    ab == (a & c) && ab == (b & c)
}

/// The paper's own inclusion–exclusion count, and the family's size.
#[test]
fn g_eleven_four_has_seventy_four_members() {
    fn binom(n: i64, k: i64) -> i64 {
        if k < 0 || n < k {
            return 0;
        }
        (0..k).fold(1i64, |acc, i| acc * (n - i) / (i + 1))
    }
    let (n, k) = (11i64, 4i64);
    // |G| = C(n-1,k-1) - C(n-k,k-1) - C(n-k-1,k-1) + C(n-2k,k-1) + C(n-k-2,k-3) + 3
    let formula = binom(n - 1, k - 1) - binom(n - k, k - 1) - binom(n - k - 1, k - 1)
        + binom(n - 2 * k, k - 1)
        + binom(n - k - 2, k - 3)
        + 3;
    assert_eq!(formula, 74, "the paper's inclusion-exclusion");
    let fam = g(11, 4);
    assert_eq!(fam.len(), 74, "the construction, built from Example 1.3");
    assert!(fam.iter().all(|s| s.count_ones() == 4));
    let uniq: HashSet<u64> = fam.iter().copied().collect();
    assert_eq!(uniq.len(), 74, "members are distinct");
}

/// Intersecting, and the covering number really is three.
#[test]
fn g_eleven_four_is_intersecting_with_covering_number_three() {
    let fam = g(11, 4);
    for i in 0..fam.len() {
        for j in i + 1..fam.len() {
            assert!(fam[i] & fam[j] != 0, "members {i},{j} are disjoint");
        }
    }
    let pts: Vec<u32> = (1..=11).collect();
    let covers = |t: &[u32]| {
        let m = t.iter().fold(0u64, |a, &p| a | 1 << p);
        fam.iter().all(|s| s & m != 0)
    };
    assert!(!pts.iter().any(|&p| covers(&[p])), "tau is not 1");
    let mut two = false;
    for i in 0..pts.len() {
        for j in i + 1..pts.len() {
            if covers(&[pts[i], pts[j]]) {
                two = true;
            }
        }
    }
    assert!(!two, "tau is not 2");
    // {1,2,3} is one of the 3-element transversals the paper names.
    assert!(covers(&[1, 2, 3]), "tau is 3, via the paper's own transversal");
}

/// The prediction: 74 > 71 = `ι(4)` bound, so it must contain a sunflower.
#[test]
fn g_eleven_four_is_very_far_from_sunflower_free() {
    let fam = g(11, 4);
    let mut count = 0usize;
    for i in 0..fam.len() {
        for j in i + 1..fam.len() {
            for l in j + 1..fam.len() {
                if is_sunflower(fam[i], fam[j], fam[l]) {
                    count += 1;
                }
            }
        }
    }
    assert_eq!(count, 3481, "3-sunflowers in G(11,4)");
    // The bound that predicted this, restated so a change to it is visible
    // here: iota(4) <= 71 given the exhaustive iota(3) = 10.
    assert!(74 > 71, "PureLink.iota_four_at_most_71_if_iota_three_is_ten");
}

/// How much of the tau = 3 extremal family survives sunflower-freeness.
///
/// A randomised greedy, so the number is a lower bound on the largest
/// sunflower-free subfamily and **not** a maximum. What matters is only
/// that it is far below 32: the covering-number extremal family is not a
/// route to a counterexample, which is the whole point of §37.5's answer.
#[test]
fn little_of_it_survives_the_sunflower_condition() {
    let fam = g(11, 4);
    let mut state = 0x243F_6A88_85A3_08D3u64;
    let mut rand = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    let mut best: Vec<u64> = Vec::new();
    for _ in 0..400 {
        let mut order = fam.clone();
        for i in (1..order.len()).rev() {
            order.swap(i, (rand() % (i as u64 + 1)) as usize);
        }
        let mut cur: Vec<u64> = Vec::new();
        for x in order {
            let ok = (0..cur.len()).all(|a| {
                (a + 1..cur.len()).all(|b| !is_sunflower(cur[a], cur[b], x))
            });
            if ok {
                cur.push(x);
            }
        }
        if cur.len() > best.len() {
            best = cur;
        }
    }
    wide::verify(&best, 4, true).expect("greedy subfamily is not valid");
    assert!(
        best.len() >= 12,
        "greedy found only {}; the search is broken, not the mathematics",
        best.len()
    );
    assert!(
        best.len() < 32,
        "a sunflower-free subfamily of G(11,4) reached {} -- that would be \
         iota(4,11) >= 32 and would refute the ladder",
        best.len()
    );
}
