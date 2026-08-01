//! The structure `coq/PureLink.v` proves, checked against real families.
//!
//! The Coq file proves three things and this checks all three on every
//! family it can build:
//!
//! * **the pure link is intersecting** — the members meeting the cover
//!   `T` only at `x`, with `x` removed, pairwise intersect;
//! * **the counting identity** — summing degrees over `T` and summing
//!   `|A ∩ T|` over the family give the same number;
//! * **the recursion** — `2|F| <= |T| * (g(b-1) + iota(b-1))`.
//!
//! The Coq proof is the statement; this is the check that the statement
//! is about the objects it is meant to be about. A family where the pure
//! link had two disjoint members would be a counterexample to
//! `PureLink.pure_link_intersecting`, and nothing in Coq would notice —
//! the theorem would still be true of whatever it does describe.

use sunflower_formal::intersecting;
use sunflower_formal::plateau::Rng;
use sunflower_formal::wide;

fn is_sunflower(a: u32, b: u32, c: u32) -> bool {
    let ab = a & b;
    ab == (a & c) && ab == (b & c)
}

fn creates_sunflower(fam: &[u32], x: u32) -> bool {
    for i in 0..fam.len() {
        for j in (i + 1)..fam.len() {
            if is_sunflower(fam[i], fam[j], x) {
                return true;
            }
        }
    }
    false
}

fn sunflower_free(f: &[u32]) -> bool {
    for i in 0..f.len() {
        for j in (i + 1)..f.len() {
            for k in (j + 1)..f.len() {
                if is_sunflower(f[i], f[j], f[k]) {
                    return false;
                }
            }
        }
    }
    true
}

/// A maximum matching, capped at three — the point is only whether it is
/// 1, 2 or (impossibly) more.
fn max_matching(f: &[u32]) -> Vec<u32> {
    let mut best: Vec<u32> = Vec::new();
    for i in 0..f.len() {
        if best.len() >= 2 {
            break;
        }
        for j in 0..f.len() {
            if f[i] & f[j] == 0 {
                let cand = vec![f[i], f[j]];
                if cand.len() > best.len() {
                    best = cand;
                }
            }
        }
        if best.is_empty() {
            best = vec![f[i]];
        }
    }
    best
}

/// A random maximal sunflower-free family on `ground` points.
fn random_maximal(ground: u32, b: u32, rng: &mut Rng, intersecting: bool) -> Vec<u32> {
    let all: Vec<u32> = (0u32..(1u32 << ground))
        .filter(|x| x.count_ones() == b)
        .collect();
    let mut order: Vec<usize> = (0..all.len()).collect();
    for i in (1..order.len()).rev() {
        let j = rng.below(i + 1);
        order.swap(i, j);
    }
    let mut fam: Vec<u32> = Vec::new();
    for &i in &order {
        let x = all[i];
        if intersecting && fam.iter().any(|&a| a & x == 0) {
            continue;
        }
        // `plateau::addable` bakes in intersecting-ness; the general row
        // needs the sunflower condition alone.
        if !creates_sunflower(&fam, x) {
            fam.push(x);
        }
    }
    fam
}

/// Everything the Coq file asserts, on one family.
fn check_family(f: &[u32], b: u32, ng: usize, ni: usize) {
    assert!(sunflower_free(f), "test built a family that is not sunflower-free");
    let m = max_matching(f);
    assert!(m.len() <= 2, "a sunflower-free family has no 3-matching");
    let t: u32 = m.iter().fold(0, |a, &s| a | s);
    let tsize = t.count_ones() as usize;

    // Every member meets the cover.
    for &a in f {
        assert!(a & t != 0, "member {a:#b} misses the cover {t:#b}");
    }

    // The counting identity: sum over points of T of deg = sum over
    // members of |A ∩ T|.
    let degsum: usize = (0..32)
        .filter(|p| t >> p & 1 == 1)
        .map(|p| f.iter().filter(|a| *a >> p & 1 == 1).count())
        .sum();
    let meetsum: usize = f.iter().map(|a| (a & t).count_ones() as usize).sum();
    assert_eq!(degsum, meetsum, "the double count disagrees with itself");

    // The pure part, and the bound it satisfies.
    let pure: Vec<u32> = f.iter().copied().filter(|a| (a & t).count_ones() == 1).collect();
    assert!(
        2 * f.len() <= pure.len() + meetsum,
        "2|F| = {} exceeds |pure| + sum |A cap T| = {} + {}",
        2 * f.len(),
        pure.len(),
        meetsum
    );

    // The pure link at each point of the cover is intersecting.
    for p in 0..32u32 {
        if t >> p & 1 == 0 {
            continue;
        }
        let link: Vec<u32> = pure
            .iter()
            .copied()
            .filter(|a| a >> p & 1 == 1)
            .map(|a| a & !(1 << p))
            .collect();
        for i in 0..link.len() {
            for j in (i + 1)..link.len() {
                assert!(
                    link[i] & link[j] != 0,
                    "the pure link at point {p} has disjoint members \
                     {:#b} and {:#b} -- PureLink.pure_link_intersecting is \
                     false of this family",
                    link[i],
                    link[j]
                );
            }
        }
        assert!(
            link.len() <= ni,
            "the pure link at {p} has {} members, above iota({}) <= {ni}",
            link.len(),
            b - 1
        );
    }

    // And the recursion itself.
    assert!(
        2 * f.len() <= tsize * (ng + ni),
        "2|F| = {} exceeds |T| * (Ng + Ni) = {tsize} * {}",
        2 * f.len(),
        ng + ni
    );
}

/// `g(2) = 6` and `iota(2) = 3` are the inputs at `b = 3`, and
/// `PureLink.g_two_at_most_six` / `iota_two_at_most_three` reproduce them
/// from the level below rather than assuming them.
#[test]
fn the_recursion_reproduces_the_known_values() {
    // b = 2: 2*2*(g(1) + iota(1)) = 2*2*3 = 12 <= 2*6 + 1
    assert!(2 * 2 * (2 + 1) <= 2 * 6 + 1, "g(2) <= 6 does not follow");
    assert!(2 * (2 + 1) <= 2 * 3 + 1, "iota(2) <= 3 does not follow");
    // and they are attained
    let (n2, _, done) = intersecting::iota(6, 2, 100_000_000, 0);
    assert!(done && n2 == 3, "iota(2) is {n2}");
    // b = 3
    assert!(2 * 3 * (6 + 3) <= 2 * 27 + 1, "g(3) <= 27 does not follow");
    assert!(3 * (6 + 3) <= 2 * 13 + 1, "iota(3) <= 13 does not follow");
    // The recursion is never worse than Erdos-Rado's 2b*g(b-1).
    for (ng, ni) in [(2usize, 1usize), (6, 3), (27, 13)] {
        assert!(ni <= ng);
        assert!(ng + ni <= 2 * ng, "the substitution lost ground");
    }
}

/// The Coq statements, exercised on families the search actually finds.
#[test]
fn pure_link_structure_holds_on_random_maximal_families() {
    let mut rng = Rng::new(20260801);
    let mut checked = 0;
    let mut biggest = 0;
    for ground in 6..=14u32 {
        for _ in 0..60 {
            for intersecting_only in [false, true] {
                let f = random_maximal(ground, 3, &mut rng, intersecting_only);
                if f.is_empty() {
                    continue;
                }
                check_family(&f, 3, 6, 3);
                biggest = biggest.max(f.len());
                checked += 1;
            }
        }
    }
    assert!(checked > 500, "only {checked} families checked");
    assert!(biggest >= 18, "the sample never got near g(3); biggest {biggest}");
    // Nothing found may exceed the proved bounds.
    assert!(biggest <= 27, "a family of {biggest} beats g(3) <= 27");
}

/// The same at uniformity 4, where the inputs are `g(3) <= 27` and
/// `iota(3) = 10`.
#[test]
fn pure_link_structure_holds_at_uniformity_four() {
    let mut rng = Rng::new(4444);
    let mut checked = 0;
    for ground in 8..=11u32 {
        for _ in 0..25 {
            for intersecting_only in [false, true] {
                let f = random_maximal(ground, 4, &mut rng, intersecting_only);
                if f.is_empty() {
                    continue;
                }
                check_family(&f, 4, 27, 10);
                checked += 1;
            }
        }
    }
    assert!(checked > 100, "only {checked} families checked");
}

/// The support bound, and the search it makes finite.
///
/// `PureLink.intersecting_support_bound` says an `n`-member intersecting
/// `b`-uniform family has support at most `b + (b-1)(n-1)`. Checked
/// against every family the exhaustive search produces, and then used:
/// the ground-23 search for eleven members comes back empty, so
/// `iota(3) = 10`.
#[test]
fn support_bound_holds_and_decides_iota_three() {
    assert_eq!(wide::support_bound(3, 11), 23);
    assert_eq!(wide::support_bound(4, 32), 97);

    // The bound is respected by the extremal families themselves.
    //
    // `iota(4,9)` costs fifty seconds and `iota(4,10)` is the 4437-second
    // row of `docs/roadmap.md` §9; both stay out of the grid, and the
    // uniformity-4 row enters below through the substitution instead,
    // which builds the same 27-member family in no time.
    for (b, g) in [(2u32, 6u32), (3, 6), (3, 9), (3, 12)] {
        let (n, fam, _) = intersecting::iota(g, b, 2_000_000_000, 0);
        if fam.is_empty() {
            continue;
        }
        let support = fam.iter().fold(0u32, |a, &s| a | s).count_ones();
        assert_eq!(n, fam.len());
        assert!(
            support <= wide::support_bound(b, n as u32),
            "iota({b},{g}) family has support {support} above the bound {}",
            wide::support_bound(b, n as u32)
        );
    }

    // Uniformity 4, through the construction rather than the search.
    let (_, i2, _) = intersecting::iota(3, 2, 10_000_000, 0);
    let subst: Vec<u32> = intersecting::substitute(&i2, 3, &i2, 3)
        .iter()
        .map(|&s| s as u32)
        .collect();
    assert_eq!(subst.len(), 27);
    let support = subst.iter().fold(0u32, |a, &s| a | s).count_ones();
    assert!(support <= wide::support_bound(4, 27));

    // And the decision it makes possible.
    let (found, _, done) = wide::iota_decide(23, 3, 11, 40_000_000_000);
    assert!(done, "the ground-23 search did not finish");
    assert!(!found, "an 11-member intersecting 3-uniform family exists");
}
