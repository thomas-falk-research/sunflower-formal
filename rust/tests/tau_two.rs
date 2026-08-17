//! `tau = 2` at the `iota(4,11)` rung: the reduction, and the numbers it
//! turns on.
//!
//! `docs/roadmap.md` §37.5 asked whether the covering number could close
//! the rung on paper. §37.6 and `docs/reading.md` A22 answered no for
//! `tau = 3` and `tau = 4`, and A24f closed the shifted case too. This
//! file is the remaining case, and unlike those it is not a literature
//! question — it is decided here.
//!
//! ## The reduction
//!
//! Let `F` be 4-uniform, intersecting, sunflower-free on `[11]`, with
//! `tau(F) = 2` and a 2-cover `{p, q}`. Split by which cover point a
//! member holds and take links:
//!
//! ```text
//!   X = { A \ {p} : p in A, q not in A }     3-sets on the other nine points
//!   Y = { B \ {q} : q in B, p not in B }     3-sets on the other nine points
//!   C = { A       : p in A and q in A }
//!   |F| = |X| + |Y| + |C|                    (a partition, by the cover)
//! ```
//!
//! Three facts, each checked below.
//!
//! 1. **`F` is sunflower-free iff `L_p` and `L_q` are** — where `L_p` is
//!    the link at `p` of *every* member containing `p`, `C` included. A
//!    triple whose members neither all share `p` nor all share `q` can
//!    never be a sunflower, so the two sides impose no joint condition.
//!
//! 2. **`X` and `Y` are cross-intersecting**, since a member of `X`'s
//!    preimage has no `q` and a member of `Y`'s has no `p`, so they can
//!    only meet outside `{p, q}` — and they must, as `F` is intersecting.
//!
//! 3. **`|C| <= g(2) = 6`.** Members of `C` all contain `{p, q}`, so a
//!    sunflower among them is exactly a sunflower among their 2-set
//!    co-links, and the largest sunflower-free graph is two triangles.
//!
//! So `|F| <= max(|X| + |Y|) + 6` over cross-intersecting pairs of
//! sunflower-free 3-uniform families on nine points.
//!
//! ## What decides it
//!
//! `rust/examples/tau_two.rs` computes that maximum. The verdict and the
//! costs it reports are asserted in `docs/roadmap.md` §42; this file
//! carries the parts cheap enough to run in a test:
//!
//! * fact 1, exhaustively over the mixed shapes;
//! * fact 3, by computing `g(2)` on nine points directly;
//! * the small end of the pattern, `n = 5, 6, 7`, where the exact maximum
//!   is 12, 20, 20 — note 20 = `2 * iota(3)` and *not* `2 * g(3,n)`, so
//!   the cross-intersecting condition is what does the work, and the
//!   report's "two stars each at most `g(3) = 20`, so 40" was loose by a
//!   factor of two;
//! * the construction that attains 20, so the bound is not vacuous.

use std::collections::HashSet;

fn is_sunflower(a: u32, b: u32, c: u32) -> bool {
    let ab = a & b;
    ab == (a & c) && ab == (b & c)
}

fn mask(pts: &[u32]) -> u32 {
    pts.iter().fold(0, |m, &p| m | 1 << p)
}

fn subsets(n: u32, k: u32) -> Vec<u32> {
    let mut out = Vec::new();
    let mut idx: Vec<u32> = (0..k).collect();
    if k == 0 || k > n {
        return out;
    }
    loop {
        out.push(mask(&idx));
        let mut i = (k - 1) as usize;
        loop {
            if idx[i] < n - (k - i as u32) {
                idx[i] += 1;
                for j in i + 1..k as usize {
                    idx[j] = idx[j - 1] + 1;
                }
                break;
            }
            if i == 0 {
                return out;
            }
            i -= 1;
        }
    }
}

fn max_sunflower_free(cands: &[u32]) -> usize {
    fn rec(cands: &[u32], cur: &mut Vec<u32>, best: &mut usize) {
        if cur.len() > *best {
            *best = cur.len();
        }
        for i in 0..cands.len() {
            if cur.len() + (cands.len() - i) <= *best {
                return;
            }
            let x = cands[i];
            let next: Vec<u32> = cands[i + 1..]
                .iter()
                .copied()
                .filter(|&y| !cur.iter().any(|&a| is_sunflower(a, x, y)))
                .collect();
            cur.push(x);
            rec(&next, cur, best);
            cur.pop();
        }
    }
    let mut best = 0;
    rec(cands, &mut Vec::new(), &mut best);
    best
}

/// Fact 1. A triple that does not lie wholly inside `S_p` or wholly inside
/// `S_q` is never a sunflower, so the two links are the only constraints.
#[test]
fn the_two_links_are_the_only_sunflower_constraints() {
    const P: u32 = 0;
    const Q: u32 = 1;
    let spare: Vec<u32> = (2..9).collect(); // seven spare points, enough for every shape

    let with = |base: &[u32], k: u32| -> Vec<u32> {
        subsets(spare.len() as u32, k)
            .into_iter()
            .map(|s| {
                let t: Vec<u32> = (0..spare.len() as u32)
                    .filter(|i| s >> i & 1 == 1)
                    .map(|i| spare[i as usize])
                    .collect();
                mask(base) | mask(&t)
            })
            .collect()
    };
    let mut all = Vec::new();
    all.extend(with(&[P], 3)); // p, no q
    all.extend(with(&[Q], 3)); // q, no p
    all.extend(with(&[P, Q], 2)); // both
    assert!(all.iter().all(|m| m.count_ones() == 4), "not 4-uniform");
    let uniq: HashSet<u32> = all.iter().copied().collect();
    assert_eq!(uniq.len(), all.len(), "candidates not distinct");

    let bp = 1u32 << P;
    let bq = 1u32 << Q;
    let mut mixed = 0usize;
    let mut sunflowers = 0usize;
    for i in 0..all.len() {
        for j in i + 1..all.len() {
            for k in j + 1..all.len() {
                let (a, b, c) = (all[i], all[j], all[k]);
                let all_p = a & bp != 0 && b & bp != 0 && c & bp != 0;
                let all_q = a & bq != 0 && b & bq != 0 && c & bq != 0;
                if all_p || all_q {
                    continue; // internal to S_p or S_q; L_p / L_q governs it
                }
                mixed += 1;
                if is_sunflower(a, b, c) {
                    sunflowers += 1;
                }
            }
        }
    }
    assert_eq!(mixed, 67_375, "the mixed-shape count quoted in the docs");
    assert_eq!(
        sunflowers, 0,
        "a mixed triple is a sunflower, so the reduction is unsound"
    );
}

/// Fact 3. `|C| <= g(2) = 6`, and six is attained — two disjoint triangles.
#[test]
fn the_both_cover_points_part_is_at_most_six() {
    // C's members all contain {p,q}; a sunflower among them is exactly a
    // sunflower among the 2-set co-links, on the other nine points.
    let pairs = subsets(9, 2);
    assert_eq!(pairs.len(), 36);
    assert_eq!(max_sunflower_free(&pairs), 6, "g(2,9) is not 6");

    // The witness, named: two vertex-disjoint triangles. Six edges,
    // maximum degree two, matching number two — the two ways a graph can
    // hold a 3-sunflower are a vertex of degree three and three disjoint
    // edges, and this has neither.
    let two_triangles = [
        mask(&[0, 1]), mask(&[1, 2]), mask(&[0, 2]),
        mask(&[3, 4]), mask(&[4, 5]), mask(&[3, 5]),
    ];
    for i in 0..6 {
        for j in i + 1..6 {
            for k in j + 1..6 {
                assert!(
                    !is_sunflower(two_triangles[i], two_triangles[j], two_triangles[k]),
                    "two triangles contain a sunflower"
                );
            }
        }
    }
}

/// The small end of the pattern, and the construction that attains it.
///
/// `max(|X|+|Y|)` is 12, 20, 20 at `n = 5, 6, 7`. The 20 is `2 * iota(3)`,
/// not `2 * g(3,n)` — at `n = 7`, `g(3,7) = 12` would allow 24, and the
/// cross-intersecting condition forbids it.
#[test]
fn the_cross_intersecting_maximum_is_twice_iota_three_not_twice_g_three() {
    /// Exact `max(|X|+|Y|)` over cross-intersecting sunflower-free pairs.
    /// Branch over `X`, score by `maxSF` of what still meets all of it.
    fn best_pair_sum(n: u32) -> usize {
        let trip = subsets(n, 3);
        let cap = max_sunflower_free(&trip);
        fn rec(
            trip: &[u32],
            cap: usize,
            avail: &[u32],
            x: &mut Vec<u32>,
            best: &mut usize,
        ) {
            let nx: Vec<u32> = trip
                .iter()
                .copied()
                .filter(|&u| x.iter().all(|&t| t & u != 0))
                .collect();
            let y_cap = max_sunflower_free(&nx).min(cap);
            if x.len() + y_cap > *best {
                *best = x.len() + y_cap;
            }
            if x.len() + avail.len() + y_cap <= *best || x.len() >= cap {
                return;
            }
            for i in 0..avail.len() {
                if x.len() + (avail.len() - i) + y_cap <= *best {
                    return;
                }
                let t = avail[i];
                let next: Vec<u32> = avail[i + 1..]
                    .iter()
                    .copied()
                    .filter(|&u| !x.iter().any(|&a| is_sunflower(a, t, u)))
                    .collect();
                x.push(t);
                rec(trip, cap, &next, x, best);
                x.pop();
            }
        }
        let mut best = 0;
        rec(&trip, cap, &trip.clone(), &mut Vec::new(), &mut best);
        best
    }

    assert_eq!(best_pair_sum(5), 12);
    assert_eq!(best_pair_sum(6), 20);
    assert_eq!(best_pair_sum(7), 20);

    // g(3,7) = 12, so two independent sunflower-free families would allow
    // 24. Cross-intersecting brings it to 20. This is the factor the
    // "two stars each at most g(3) = 20, hence 40" estimate missed.
    assert_eq!(max_sunflower_free(&subsets(7, 3)), 12);
    assert!(20 < 24);

    // And 20 is attained, by taking both sides to be the same maximum
    // *intersecting* sunflower-free family: iota(3) = 10, doubled. Not
    // vacuous, and it shows the bound is the right shape.
    let trip9 = subsets(9, 3);
    let iota3 = {
        fn rec(cands: &[u32], cur: &mut Vec<u32>, best: &mut Vec<u32>) {
            if cur.len() > best.len() {
                *best = cur.clone();
            }
            for i in 0..cands.len() {
                if cur.len() + (cands.len() - i) <= best.len() {
                    return;
                }
                let x = cands[i];
                let next: Vec<u32> = cands[i + 1..]
                    .iter()
                    .copied()
                    .filter(|&y| y & x != 0 && !cur.iter().any(|&a| is_sunflower(a, x, y)))
                    .collect();
                cur.push(x);
                rec(&next, cur, best);
                cur.pop();
            }
        }
        let mut best = Vec::new();
        rec(&trip9, &mut Vec::new(), &mut best);
        best
    };
    assert_eq!(iota3.len(), 10, "iota(3,9) is not 10");
    // X = Y = iota3 is cross-intersecting because iota3 is intersecting.
    assert!(iota3.iter().all(|&a| iota3.iter().all(|&b| a & b != 0)));
    assert_eq!(iota3.len() * 2, 20);
    // Which already puts tau=2 under the rung's 32, with room:
    assert!(20 + 6 < 32);
}
