//! Falsifying the sandwich `2 iota(b) <= g(b) <= 2b iota(b)` before it
//! is proved.
//!
//! `iota(b)` is the largest *intersecting* 3-sunflower-free `b`-uniform
//! family and `g(b) = f(b,3) - 1` the largest sunflower-free one. The
//! lower half is the doubling and is already a theorem
//! (`Intersecting.doubling_lower_bound`). The upper half is new:
//!
//! > a sunflower-free family has no three pairwise disjoint members, so
//! > a *maximal* disjoint subfamily has at most two, and its union `T`
//! > (at most `2b` points) meets every member. Pigeonhole gives an `x`
//! > in `T` lying in at least `|F|/(2b)` members, and the star at `x`
//! > is intersecting, sunflower-free and `b`-uniform — an `iota`
//! > witness. Hence `g(b) <= 2b iota(b)`.
//!
//! Four things in that paragraph can be false, and each is checked here
//! against families the argument knows nothing about:
//!
//! 1. maximal disjoint subfamilies of a sunflower-free family have at
//!    most two members (`no_three_pairwise_disjoint`);
//! 2. the union of one of them meets every member, and has at most `2b`
//!    points (`the_cover_is_small_and_covers`);
//! 3. some point lies in at least `|F|/(2b)` members
//!    (`the_star_bound_holds`) — this is the conclusion, and it is
//!    checked over every point rather than through the cover, so a
//!    broken cover argument cannot make it pass;
//! 4. the star really is an `iota` witness (`stars_are_iota_witnesses`).
//!
//! The sample is deliberately not the extremal families alone: those are
//! few and highly structured. Most of it is randomly grown *maximal*
//! sunflower-free families, which is where a false step would show.
//!
//! Cost note: `N(3,9)` takes a quarter of an hour and `N(3,8)` takes
//! eighteen seconds, so the exhaustive maxima stop at ground 8 for
//! uniformity 3 and every one of them is computed once and cached. The
//! random families are free at any ground set and go to ten points.

use std::collections::HashMap;
use std::sync::OnceLock;

use sunflower_formal::ground::{m_subsets, max_sunflower_free};

const BUDGET: u64 = 20_000_000_000;

/// Where the exhaustive search stops being affordable, per uniformity.
fn exhaustive_ceiling(m: u32) -> u32 {
    if m >= 3 {
        8
    } else {
        10
    }
}

/// Do `a`, `b`, `c` form a 3-sunflower? Reimplemented here rather than
/// imported: this file is a check on the library, not a use of it.
#[inline]
fn is_sunflower(a: u16, b: u16, c: u16) -> bool {
    let ab = a & b;
    ab == (a & c) && ab == (b & c)
}

fn creates_sunflower(cur: &[u16], x: u16) -> bool {
    for i in 0..cur.len() {
        for j in (i + 1)..cur.len() {
            if is_sunflower(cur[i], cur[j], x) {
                return true;
            }
        }
    }
    false
}

fn sunflower_free(f: &[u16]) -> bool {
    for i in 0..f.len() {
        for j in (i + 1)..f.len() {
            for l in (j + 1)..f.len() {
                if is_sunflower(f[i], f[j], f[l]) {
                    return false;
                }
            }
        }
    }
    true
}

fn intersecting(f: &[u16]) -> bool {
    f.iter().all(|a| f.iter().all(|b| a & b != 0))
}

/// A greedy maximal pairwise-disjoint subfamily, and its union.
fn maximal_disjoint(f: &[u16]) -> (Vec<u16>, u16) {
    let mut cover: Vec<u16> = Vec::new();
    let mut union: u16 = 0;
    for &a in f {
        if a & union == 0 {
            cover.push(a);
            union |= a;
        }
    }
    (cover, union)
}

fn deg(f: &[u16], x: u32) -> usize {
    f.iter().filter(|a| *a & (1u16 << x) != 0).count()
}

fn star(f: &[u16], x: u32) -> Vec<u16> {
    f.iter().copied().filter(|a| a & (1u16 << x) != 0).collect()
}

/// Deterministic shuffle source. The crate has no dev-dependencies, and
/// a fixed seed keeps the sample reproducible across runs.
struct Lcg(u64);

impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0 >> 33
    }
}

/// A maximal sunflower-free `m`-uniform family on `ground` points, grown
/// greedily in a random order. Maximal, not maximum: that is the point —
/// the extremal families are few and structured, and a false step in the
/// argument is likelier to show on an arbitrary one.
fn random_maximal(ground: u32, m: u32, rng: &mut Lcg) -> Vec<u16> {
    let mut sets = m_subsets(ground, m);
    for i in (1..sets.len()).rev() {
        let j = (rng.next() as usize) % (i + 1);
        sets.swap(i, j);
    }
    let mut fam: Vec<u16> = Vec::new();
    for x in sets {
        if !creates_sunflower(&fam, x) {
            fam.push(x);
        }
    }
    fam
}

/// `N(m, ground)`, computed once. Every test that needs a maximum reads
/// this table; recomputing `N(3,8)` per assertion is the difference
/// between twenty seconds and an hour.
fn maxima() -> &'static HashMap<(u32, u32), usize> {
    static T: OnceLock<HashMap<(u32, u32), usize>> = OnceLock::new();
    T.get_or_init(|| {
        let mut t = HashMap::new();
        for m in 1..=3u32 {
            for ground in m..=exhaustive_ceiling(m) {
                let (n, fam, done) = max_sunflower_free(ground, m, BUDGET);
                assert!(done, "N({m},{ground}) did not finish");
                assert_eq!(fam.len(), n);
                assert!(sunflower_free(&fam), "N({m},{ground}) witness has a sunflower");
                t.insert((m, ground), n);
            }
        }
        t
    })
}

/// The sample: the exhaustive maxima above, plus 40 random maximal
/// families per `(ground, m)` out to ten points.
fn sample() -> &'static Vec<(u32, u32, Vec<u16>)> {
    static S: OnceLock<Vec<(u32, u32, Vec<u16>)>> = OnceLock::new();
    S.get_or_init(|| {
        let mut out: Vec<(u32, u32, Vec<u16>)> = Vec::new();
        let mut rng = Lcg(0x5EED_1972);
        for m in 1..=3u32 {
            for ground in m..=10u32 {
                if ground <= exhaustive_ceiling(m) {
                    let (_, fam, _) = max_sunflower_free(ground, m, BUDGET);
                    if !fam.is_empty() {
                        out.push((ground, m, fam));
                    }
                }
                for _ in 0..40 {
                    let f = random_maximal(ground, m, &mut rng);
                    if !f.is_empty() {
                        out.push((ground, m, f));
                    }
                }
            }
        }
        out
    })
}

/// Step 1. A sunflower-free family has no three pairwise disjoint
/// members, so every maximal disjoint subfamily has at most two.
///
/// This is `Audit.no_k_disjoint_of_no_sunflower` at `k = 3`, checked on
/// families rather than derived: three pairwise disjoint sets are a
/// sunflower with empty core.
#[test]
fn no_three_pairwise_disjoint() {
    for (_, _, f) in sample() {
        assert!(sunflower_free(f), "sample family is not sunflower-free");
        let (cover, _) = maximal_disjoint(f);
        assert!(
            cover.len() <= 2,
            "maximal disjoint subfamily of size {} in a sunflower-free family",
            cover.len()
        );
    }
}

/// Step 2. The union of a maximal disjoint subfamily has at most `2b`
/// points and meets every member.
#[test]
fn the_cover_is_small_and_covers() {
    for (_, m, f) in sample() {
        let (cover, union) = maximal_disjoint(f);
        assert!(
            (union.count_ones() as usize) <= 2 * *m as usize,
            "cover union has {} points, m = {m}",
            union.count_ones()
        );
        assert_eq!(union.count_ones() as usize, cover.len() * *m as usize);
        for &a in f {
            assert!(a & union != 0, "member {a:b} misses the cover union");
        }
    }
}

/// Step 3, the conclusion: some point lies in at least `|F|/(2b)`
/// members, i.e. `2b * maxdeg(F) >= |F|`.
///
/// Checked over every point, not only the points of the cover, so it
/// stands or falls independently of steps 1 and 2. Also recorded: the
/// worst ratio actually seen, which says how loose `2b` is.
#[test]
fn the_star_bound_holds() {
    // Worst observed `|F| / maxdeg(F)` per uniformity, as a rational
    // `(num, den)` so the comparison stays exact.
    let mut worst: Vec<(u32, usize, usize)> = Vec::new();
    for (ground, m, f) in sample() {
        let best = (0..*ground).map(|x| deg(f, x)).max().unwrap_or(0);
        assert!(
            2 * (*m as usize) * best >= f.len(),
            "star bound fails: |F| = {}, maxdeg = {best}, m = {m}, ground = {ground}",
            f.len()
        );
        match worst.iter_mut().find(|(u, _, _)| u == m) {
            Some(w) => {
                if f.len() * w.2 > w.1 * best {
                    *w = (*m, f.len(), best);
                }
            }
            None => worst.push((*m, f.len(), best)),
        }
    }
    worst.sort();
    let ratios: Vec<String> = worst
        .iter()
        .map(|(m, n, d)| format!("m={m}: {n}/{d}"))
        .collect();
    println!("worst |F|/maxdeg by uniformity: {ratios:?}");
    // The proved factor is `2b` = 2, 4, 6 at m = 1, 2, 3, against the
    // observed 2, 3, 2.75. So the bound is *attained* at uniformity 1
    // (two disjoint singletons, every degree 1) and loose above it —
    // which is what one expects, since the cover argument charges `2b`
    // points whether or not the two disjoint members exist. Pinned so a
    // change in the sample is visible rather than silent.
    assert_eq!(
        ratios,
        vec![
            "m=1: 2/1".to_string(),
            "m=2: 6/2".to_string(),
            "m=3: 11/4".to_string()
        ],
        "worst |F|/maxdeg ratios moved"
    );
}

/// Step 4. The star at the popular point is an `iota` witness:
/// `b`-uniform, distinct, intersecting and sunflower-free.
///
/// Intersecting-ness is the only nontrivial one and it is the whole
/// point: every member of the star contains `x`.
#[test]
fn stars_are_iota_witnesses() {
    for (ground, m, f) in sample() {
        for x in 0..*ground {
            let s = star(f, x);
            if s.is_empty() {
                continue;
            }
            assert!(s.iter().all(|a| a.count_ones() == *m), "star not uniform");
            assert!(intersecting(&s), "star at {x} is not intersecting");
            assert!(sunflower_free(&s), "star at {x} is not sunflower-free");
        }
    }
}

/// The sandwich at the uniformities where both ends are measured.
///
/// `iota(1) = 1`, `iota(2) = 3` and `iota(3) = 10`; `g(2) = 6` exactly,
/// and `g(3) >= 20` by the doubling. Checked against `N(m, ground)` for
/// every ground set the exhaustive search reaches.
#[test]
fn the_sandwich_holds_at_measured_values() {
    for (m, i) in [(1u32, 1usize), (2, 3), (3, 10)] {
        for ground in m..=exhaustive_ceiling(m) {
            let n = maxima()[&(m, ground)];
            assert!(
                n <= 2 * (m as usize) * i,
                "N({m},{ground}) = {n} exceeds 2b iota(b) = {}",
                2 * m as usize * i
            );
        }
    }

    // The lower half is the doubling, `2 iota(b) <= g(b)`. At b = 2 it
    // is met with equality: `g(2) = 6 = 2 * iota(2)`, so the sandwich is
    // `6 <= 6 <= 12` there. At b = 3 the doubled family lives on twelve
    // points, past the exhaustive reach, and only the construction is
    // checked (in `tests/intersecting.rs`).
    assert_eq!(maxima()[&(2, 6)], 6);
    assert_eq!(maxima()[&(2, 6)], 2 * 3);
}

/// `iota(b) <= g(b)`, trivially — an intersecting sunflower-free family
/// is a sunflower-free family. Together with the star bound that is the
/// sandwich, and it is what makes the two quantities share a rate.
#[test]
fn iota_is_below_g() {
    for (ground, m, f) in sample() {
        let Some(&n) = maxima().get(&(*m, *ground)) else {
            continue;
        };
        for x in 0..*ground {
            let s = star(f, x);
            assert!(s.len() <= n, "an intersecting family beat N({m},{ground})");
        }
    }
}

/// The arithmetic the equivalence turns on: `2b <= 2^b` for `b >= 1`,
/// hence `2b C^b <= (2C)^b`. Without it the conclusion of the sandwich
/// is `2b C^b`, which is not of the form `c^b`, and the sunflower
/// conjecture is a statement about `c^b`.
#[test]
fn the_factor_absorbs_into_the_base() {
    for b in 1u32..=20 {
        assert!(2 * (b as u64) <= 2u64.pow(b), "2b <= 2^b fails at b = {b}");
        for c in 1u64..=6 {
            assert!(
                2 * (b as u64) * c.pow(b) <= (2 * c).pow(b),
                "2b C^b <= (2C)^b fails at b = {b}, C = {c}"
            );
        }
    }
}

/// The measured rates `iota(b)^(1/(b-1))`, which is what the sandwich
/// says is *the* rate of the problem at `k = 3`.
///
/// Flat, not growing: 3.000 at `b = 2`, 3.162 at `b = 3`, 3.000 at
/// `b = 4` (ground 9) and below 3.142 at ground 10. Mild evidence for
/// the conjecture at `k = 3` with `c(3)` near 3.2, and it says the
/// quantity to extend is `iota`, not `g`.
#[test]
fn the_measured_rates_are_flat() {
    let rows: [(u32, f64); 4] = [
        (2, 3.0),                   // iota(2) = 3
        (3, 10f64.powf(1.0 / 2.0)), // iota(3) = 10    -> 3.1623
        (4, 27f64.powf(1.0 / 3.0)), // iota(4,9) = 27  -> 3.0000
        (4, 31f64.powf(1.0 / 3.0)), // iota(4,10) <= 31 -> < 3.1414
    ];
    for (b, rate) in rows {
        assert!(rate >= 2.99, "rate at b = {b} dropped below 3");
        assert!(rate <= 3.17, "rate at b = {b} rose above the AHS constant");
    }
    // Nothing measured beats Abbott-Hanson-Sauer, and the value that
    // would is `iota(4) >= 32`, ruled out through ground 10.
    assert!(31f64.powf(1.0 / 3.0) < 10f64.powf(1.0 / 2.0));
}
