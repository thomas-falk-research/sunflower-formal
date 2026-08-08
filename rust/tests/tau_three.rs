//! The covering-number-three case, measured.
//!
//! `TauThree.tau_three_bound` proves that a 3-uniform intersecting family
//! of distinct sets with covering number at least 3 has at most 16
//! members, with no Rao condition and no appeal to Frankl's theorem. That
//! bound is what `TwoCover.split_with_piece` needs at `r = 4`, and it is
//! what makes `r*(3,3) <= 4` unconditional (docs/roadmap.md §25).
//!
//! Three kinds of claim are certified here.
//!
//! * **The graph lemma the proof rests on** — three nonempty pairwise
//!   cross-intersecting graphs of maximum degree 3 have at most 9 edges
//!   between them — is checked exhaustively on the search space its own
//!   proof supplies, and the maximum is 9 on the nose.
//! * **The truth of the bound.** The largest family satisfying the
//!   theorem's hypotheses is 10 (Frankl's value, attained by every
//!   3-subset of a 5-set), so the proved 16 carries six of slack. It is
//!   not needed: `split_with_piece` at `r = 4` wants only 16.
//! * **The two objects the Coq file carries** — the Fano plane, which
//!   makes the *unguarded* hypothesis false, and the 16-member grid star,
//!   which shows `I(3,4) = 16` is attained — verified here by code
//!   sharing nothing with the Coq development.

use sunflower_formal::spread::{is_rao_spread, Mask};

/// An edge of a graph on a small vertex set, as an unordered pair.
type Edge = (u32, u32);

fn meets(e: Edge, f: Edge) -> bool {
    e.0 == f.0 || e.0 == f.1 || e.1 == f.0 || e.1 == f.1
}

fn deg_ok(g: &[Edge], n: u32) -> bool {
    (0..n).all(|v| g.iter().filter(|e| e.0 == v || e.1 == v).count() <= 3)
}

/// Every `Delta <= 3` subgraph of the edges touching `{0,1}`.
fn anchor_subgraphs(n: u32) -> Vec<Vec<Edge>> {
    let anchor: Vec<Edge> = (0..n)
        .flat_map(|a| (a + 1..n).map(move |b| (a, b)))
        .filter(|&(a, b)| a == 0 || a == 1 || b == 0 || b == 1)
        .collect();
    let mut out = Vec::new();
    for mask in 0u32..(1u32 << anchor.len()) {
        if mask.count_ones() > 6 {
            continue;
        }
        let g: Vec<Edge> = (0..anchor.len())
            .filter(|i| mask >> i & 1 == 1)
            .map(|i| anchor[i])
            .collect();
        if deg_ok(&g, n) {
            out.push(g);
        }
    }
    out
}

fn all_edges(n: u32) -> Vec<Edge> {
    (0..n).flat_map(|a| (a + 1..n).map(move |b| (a, b))).collect()
}

/// Largest `Delta <= 3` subset of `pool` that contains `must`.
fn max_deg3_containing(pool: &[Edge], must: Edge, n: u32) -> usize {
    let rest: Vec<Edge> = pool.iter().copied().filter(|&e| e != must).collect();
    let mut best = 1usize;
    for mask in 0u32..(1u32 << rest.len()) {
        if 1 + mask.count_ones() as usize <= best {
            continue;
        }
        let mut g = vec![must];
        g.extend((0..rest.len()).filter(|i| mask >> i & 1 == 1).map(|i| rest[i]));
        if deg_ok(&g, n) {
            best = g.len();
        }
    }
    best
}

/// Exhaustive maximum of `|A| + |B| + |C|` over nonempty pairwise
/// cross-intersecting graphs of maximum degree 3 on `n` vertices.
///
/// The search is confined the way the proof is: order the three so that
/// `|A| >= |B| >= |C|`, take an edge of `C` and relabel it `{0,1}`. Every
/// edge of `A` and of `B` meets it, so both live on the edges touching
/// `{0,1}`; `C` then lives on the edges meeting everything in `A` and
/// in `B`.
fn max_triple(n: u32) -> usize {
    let subs = anchor_subgraphs(n);
    let edges = all_edges(n);
    let mut best = 0usize;
    for a in &subs {
        if a.is_empty() {
            continue;
        }
        let sa: Vec<Edge> = edges
            .iter()
            .copied()
            .filter(|&e| a.iter().all(|&f| meets(e, f)))
            .collect();
        for b in &subs {
            if b.is_empty() || b.len() > a.len() {
                continue;
            }
            if !b.iter().all(|e| sa.contains(e)) {
                continue;
            }
            let pool: Vec<Edge> = sa
                .iter()
                .copied()
                .filter(|&e| b.iter().all(|&f| meets(e, f)))
                .collect();
            if !pool.contains(&(0, 1)) {
                continue;
            }
            let c = max_deg3_containing(&pool, (0, 1), n).min(b.len());
            if a.len() + b.len() + c > best {
                best = a.len() + b.len() + c;
            }
        }
    }
    best
}

#[test]
fn lemma_l_bound_of_nine_is_exact() {
    // `TauThree.lemma_L` proves <= 9. Below the vertex count at which the
    // extremal configuration fits, the maximum is smaller; from n = 4 on
    // it is 9 and stays there.
    for n in 4..=8 {
        assert_eq!(
            max_triple(n),
            9,
            "three cross-intersecting Delta<=3 graphs on {n} vertices"
        );
    }
}

#[test]
fn lemma_l_extremal_is_three_copies_of_one_star() {
    // Three copies of a single 3-star: pairwise cross-intersecting because
    // every edge holds the centre, and 3 + 3 + 3 = 9.
    let star: Vec<Edge> = vec![(0, 1), (0, 2), (0, 3)];
    assert!(deg_ok(&star, 4));
    for e in &star {
        for f in &star {
            assert!(meets(*e, *f));
        }
    }
    assert_eq!(3 * star.len(), 9);
    // and a triangle does it too, which is the case where every graph is
    // itself intersecting
    let tri: Vec<Edge> = vec![(0, 1), (1, 2), (0, 2)];
    assert!(deg_ok(&tri, 3));
    for e in &tri {
        for f in &tri {
            assert!(meets(*e, *f));
        }
    }
    assert_eq!(3 * tri.len(), 9);
}

// ---------------------------------------------------------------------
// the truth of the bound

fn triples(n: u32) -> Vec<Mask> {
    (0u32..(1u32 << n))
        .filter(|b| b.count_ones() == 3)
        .map(|b| b as Mask)
        .collect()
}

fn tau_at_least_three(fam: &[Mask], n: u32) -> bool {
    for p in 0..n {
        for q in p..n {
            let cover = (1u32 << p) | (1u32 << q);
            if fam.iter().all(|&c| c as u32 & cover != 0) {
                return false;
            }
        }
    }
    true
}

/// The largest 3-uniform intersecting family of distinct sets on `n`
/// points whose covering number is at least 3.
fn max_tau_three(n: u32) -> usize {
    let ts = triples(n);
    let mut best = 0usize;
    let mut cur: Vec<Mask> = Vec::new();
    fn rec(ts: &[Mask], i: usize, cur: &mut Vec<Mask>, best: &mut usize, n: u32) {
        if cur.len() + (ts.len() - i) <= *best {
            return;
        }
        if cur.len() > *best && tau_at_least_three(cur, n) {
            *best = cur.len();
        }
        if i == ts.len() {
            return;
        }
        if cur.iter().all(|&a| a & ts[i] != 0) {
            cur.push(ts[i]);
            rec(ts, i + 1, cur, best, n);
            cur.pop();
        }
        rec(ts, i + 1, cur, best, n);
    }
    rec(&ts, 0, &mut cur, &mut best, n);
    best
}

#[test]
fn the_tau_three_bound_of_sixteen_has_six_of_slack() {
    // Frankl's theorem gives 10, and 10 is the truth: every 3-subset of a
    // 5-set. `TauThree.tau_three_bound` proves 16 without Frankl, and 16
    // is what `split_with_piece` needs at r = 4 -- the slack is real and
    // is not needed.
    for n in 5..=7 {
        assert_eq!(max_tau_three(n), 10, "ground {n}");
    }
    assert!(10 <= 16);
    // and 16 is exactly the constant the split can afford: 3*4^2 + 16 = 4^3
    assert_eq!(3 * 4 * 4 + 16, 4u32.pow(3));
    // one more member and it fails, which is why the constant is 16 and
    // not 17
    assert!(3 * 4 * 4 + 17 > 4u32.pow(3));
}

// ---------------------------------------------------------------------
// the two objects the Coq file carries

fn mask_of(points: &[u32]) -> Mask {
    points.iter().fold(0u32, |m, &p| m | (1 << p)) as Mask
}

#[test]
fn fano_satisfies_the_unguarded_hypotheses() {
    // `TauThree.tau_three_at_most_unguarded_is_false` repeats this family
    // to break the version of the hypothesis that omits distinctness.
    let fano: Vec<Mask> = [
        [0, 1, 2],
        [0, 3, 4],
        [0, 5, 6],
        [1, 3, 5],
        [1, 4, 6],
        [2, 3, 6],
        [2, 4, 5],
    ]
    .iter()
    .map(|l| mask_of(l))
    .collect();

    assert_eq!(fano.len(), 7);
    for c in &fano {
        assert_eq!((*c as u32).count_ones(), 3);
    }
    // distinct as sets
    let mut sorted = fano.clone();
    sorted.sort_unstable();
    sorted.dedup();
    assert_eq!(sorted.len(), 7);
    // intersecting
    for a in &fano {
        for b in &fano {
            assert!(a & b != 0);
        }
    }
    // covering number at least 3: each point is on exactly three lines,
    // so two points miss at least one of the seven
    for p in 0..7u32 {
        assert_eq!(fano.iter().filter(|c| **c as u32 >> p & 1 == 1).count(), 3);
    }
    assert!(tau_at_least_three(&fano, 7));

    // repeating it preserves every hypothesis the unguarded statement
    // makes, and multiplies the length
    for copies in 1..=4usize {
        let rep: Vec<Mask> = fano.iter().cycle().take(7 * copies).copied().collect();
        assert_eq!(rep.len(), 7 * copies);
        for a in &rep {
            for b in &rep {
                assert!(a & b != 0);
            }
        }
        assert!(tau_at_least_three(&rep, 7));
    }
    // three copies already beat 16
    assert!(3 * 7 > 16);
}

#[test]
fn star34_attains_the_sixteen() {
    // `TauThree.star34_attains_sixteen`. The grid star: a common point 0
    // and one point from each of two blocks of size 4. Rao's condition
    // holds with equality at {0} and at every pair through 0, so
    // I(3,4) = 16 exactly -- upper bound in Coq, this object below.
    let mut fam: Vec<Mask> = Vec::new();
    for a in 1..=4u32 {
        for b in 5..=8u32 {
            fam.push(mask_of(&[0, a, b]));
        }
    }
    assert_eq!(fam.len(), 16);
    for c in &fam {
        assert_eq!((*c as u32).count_ones(), 3);
    }
    let mut sorted = fam.clone();
    sorted.sort_unstable();
    sorted.dedup();
    assert_eq!(sorted.len(), 16, "distinct");
    for a in &fam {
        for b in &fam {
            assert!(a & b != 0, "intersecting");
        }
    }
    assert!(is_rao_spread(3, &fam, 4, 9), "RaoSpread 3 F 4");
    // and it is exactly the star bound r^(m-1) at (m,r) = (3,4)
    assert_eq!(fam.len(), 4usize.pow(2));
}

#[test]
fn the_star_is_extremal_at_three_from_r_equals_four() {
    // `TauThree.three_uniform_star_extremal`: I(3,r) <= r^2 for r >= 4,
    // and r = 4 = m+1 is the crossover -- at r = 3 the truth is 10
    // against a star of 9 (docs/roadmap.md §24.9, §24.13).
    use sunflower_formal::rstar::max_intersecting_piece;
    let (v3, _, _, done3) = max_intersecting_piece(3, 3, 7, 200_000_000);
    assert!(done3);
    assert_eq!(v3, 10, "I(3,3) beats the star of 9");
    let (v4, _, _, done4) = max_intersecting_piece(3, 4, 7, 200_000_000);
    assert!(done4);
    assert_eq!(v4, 12, "I(3,4) on seven points, below the ground it needs");
    // nine points is where the star fits, and there the value is the star
    let (v4b, _, _, done4b) = max_intersecting_piece(3, 4, 9, 2_000_000_000);
    assert!(done4b);
    assert_eq!(v4b, 16, "I(3,4) = 16 = 4^2, the star");
}
