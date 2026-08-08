//! The spread Hilton–Milner family `HM(m,r)`, and the two inequalities
//! that meet at `r = m` — the objects and numbers behind
//! `coq/HiltonMilner.v`.
//!
//! `HM(m,r)` is the set `E = {0,...,m-1}` together with every transversal
//! `{i, w} ∪ {y_0, ..., y_{m-3}}`, where `w = m` is the apex, `i` ranges
//! over `E`, and `y_j` ranges over the `j`-th block of `r` fresh points.
//! It has `m·r^(m-2) + 1` members.
//!
//! Five claims are checked here, all by construction and exhaustive
//! verification, sharing no code with the Coq side:
//!
//! 1. `|HM(m,r)| = m·r^(m-2) + 1`, and the family is `m`-uniform,
//!    distinct, intersecting and not a star.
//! 2. **`HM(m,r)` is Rao(`r`)-spread exactly when `r >= m`**, with the
//!    unique binding constraint the apex: `deg {w} = m·r^(m-2)` against
//!    the ceiling `r^(m-1)`.
//! 3. **`|HM(m,r)| > r^(m-1)` exactly when `r <= m`.**
//! 4. Hence at `r = m` — and, over the range searched, at `r = m` only —
//!    the family is spread *and* beats the star, which is
//!    `HiltonMilner.not_star_extremal_at_m_m`.
//! 5. The individual numbers the roadmap quotes: 10 against 9 at `(3,3)`,
//!    65 against 64 at `(4,4)`, 626 against 625 at `(5,5)`, 7777 against
//!    7776 at `(6,6)`, and `|HM(4,5)| = 101 = 76 + 25`, the two-cover
//!    split of §28 read at `(4,5)`.

use std::collections::HashSet;

use sunflower_formal::spread::{deg, is_distinct, is_rao_spread, is_uniform, pow_sat, Mask};

/// `HM(m,r)` and the size of its ground set.
///
/// Points: `0..m` is `E`, `m` is the apex `w`, and block `j` is
/// `m+1+j*r .. m+1+(j+1)*r` for `j < m-2`.
fn hm(m: u32, r: u32) -> (Vec<Mask>, u32) {
    assert!(m >= 2, "HM is defined for m >= 2");
    let k = m - 2; // number of grid blocks
    let ground = m + 1 + k * r;
    assert!(ground <= 32, "ground set {ground} does not fit in a u32 mask");

    let e: Mask = ((1u64 << m) - 1) as Mask;
    let w: Mask = 1u32 << m;

    // all transversals of the k blocks
    let mut grid: Vec<Mask> = vec![0];
    for j in 0..k {
        let base = m + 1 + j * r;
        let mut next = Vec::with_capacity(grid.len() * r as usize);
        for &g in &grid {
            for t in 0..r {
                next.push(g | (1u32 << (base + t)));
            }
        }
        grid = next;
    }

    let mut fam = vec![e];
    for i in 0..m {
        for &g in &grid {
            fam.push((1u32 << i) | w | g);
        }
    }
    (fam, ground)
}

/// Masks are `u32`, so only `(m,r)` whose ground set fits in 32 points
/// can be built. That excludes exactly one pair in the ranges below,
/// `(m,r) = (6,7)`, whose ground set has 35 points; the arithmetic half
/// of the claim is checked for it (and much further) in
/// `beating_the_star_is_arithmetic`, which needs no family at all.
const MAX_GROUND: u32 = 32;

fn fits(m: u32, r: u32) -> bool {
    m + 1 + (m - 2) * r <= MAX_GROUND
}

/// Every `(m,r)` in the scanned box that fits, listed so that the
/// coverage of the tests below is a stated number rather than whatever
/// the loop happened to reach.
fn scanned_pairs() -> Vec<(u32, u32)> {
    let mut v = Vec::new();
    for m in 2..=6u32 {
        for r in 2..=7u32 {
            if fits(m, r) {
                v.push((m, r));
            }
        }
    }
    v
}

fn intersecting(f: &[Mask]) -> bool {
    f.iter().all(|&a| f.iter().all(|&b| a & b != 0))
}

/// Not a star: no single point lies in every member.
fn nonstar(f: &[Mask], ground: u32) -> bool {
    (0..ground).all(|p| !f.iter().all(|&a| a & (1u32 << p) != 0))
}

/// The covering number, capped at 3 — enough to separate "star" (1),
/// "two-point cover" (2) and "neither" (>= 3).
fn tau_capped(f: &[Mask], ground: u32) -> u32 {
    for p in 0..ground {
        if f.iter().all(|&a| a & (1u32 << p) != 0) {
            return 1;
        }
    }
    for p in 0..ground {
        for q in (p + 1)..ground {
            let cover = (1u32 << p) | (1u32 << q);
            if f.iter().all(|&a| a & cover != 0) {
                return 2;
            }
        }
    }
    3
}

/// Rao's condition, checked over the deduplicated subsets of members.
///
/// A set `T` with positive degree is a subset of some member, so this
/// enumeration is complete; deduplicating first is what makes the larger
/// instances (`m = 6`, 7777 members) finish in reasonable time.
/// `spread_via_ground` below re-checks the same thing over the whole
/// power set of the ground for the instances where that is affordable.
fn spread_via_members(m: u32, f: &[Mask], r: u64) -> Option<Mask> {
    let mut cands: HashSet<Mask> = HashSet::new();
    for &a in f {
        let mut t = a;
        loop {
            if t != 0 {
                cands.insert(t);
            }
            if t == 0 {
                break;
            }
            t = (t - 1) & a;
        }
    }
    let mut worst: Option<Mask> = None;
    for &t in &cands {
        let cap = pow_sat(r, m.saturating_sub(t.count_ones()));
        if deg(t, f) as u64 > cap {
            // deterministic choice so failures are reproducible
            if worst.is_none() || t < worst.unwrap() {
                worst = Some(t);
            }
        }
    }
    worst
}

fn is_spread(m: u32, f: &[Mask], r: u64) -> bool {
    spread_via_members(m, f, r).is_none()
}

/// Every violating `T`, not just the smallest — used to check that the
/// apex is the *unique* obstruction rather than merely the first one the
/// enumeration reaches.
fn all_violators(m: u32, f: &[Mask], r: u64) -> Vec<Mask> {
    let mut cands: HashSet<Mask> = HashSet::new();
    for &a in f {
        let mut t = a;
        loop {
            if t != 0 {
                cands.insert(t);
            }
            if t == 0 {
                break;
            }
            t = (t - 1) & a;
        }
    }
    let mut out: Vec<Mask> = cands
        .into_iter()
        .filter(|&t| deg(t, f) as u64 > pow_sat(r, m.saturating_sub(t.count_ones())))
        .collect();
    out.sort_unstable();
    out
}

// ---------------------------------------------------------------------
// 1. Shape and size
// ---------------------------------------------------------------------

#[test]
fn the_scan_covers_what_it_says() {
    let pairs = scanned_pairs();
    assert_eq!(pairs.len(), 29, "5 uniformities x 6 values of r, less (6,7)");
    assert!(!pairs.contains(&(6, 7)));
    assert!(pairs.contains(&(6, 6)));
    assert!(pairs.contains(&(5, 7)));
}

#[test]
fn hm_has_the_stated_size_and_shape() {
    for (m, r) in scanned_pairs() {
        {
            let (f, ground) = hm(m, r);
            let expected = (m as u64) * pow_sat(r as u64, m - 2) + 1;
            assert_eq!(f.len() as u64, expected, "|HM({m},{r})|");
            assert!(is_uniform(m, &f), "HM({m},{r}) is not {m}-uniform");
            assert!(is_distinct(&f), "HM({m},{r}) has a repeated member");
            assert!(intersecting(&f), "HM({m},{r}) is not intersecting");
            assert!(nonstar(&f, ground), "HM({m},{r}) is a star");
            assert_eq!(
                tau_capped(&f, ground),
                2,
                "HM({m},{r}) should have covering number exactly 2 \
                 (the apex plus any point of E)"
            );
        }
    }
}

// ---------------------------------------------------------------------
// 2. Spread exactly when r >= m, and the apex is why
// ---------------------------------------------------------------------

#[test]
fn hm_is_rao_spread_exactly_when_r_at_least_m() {
    for (m, r) in scanned_pairs() {
        {
            let (f, _) = hm(m, r);
            let spread = is_spread(m, &f, r as u64);
            assert_eq!(
                spread,
                r >= m,
                "HM({m},{r}): spread = {spread}, expected {}",
                r >= m
            );
        }
    }
}

#[test]
fn the_apex_is_the_binding_constraint() {
    for m in 2..=6u32 {
        for r in m..=(m + 2) {
            if !fits(m, r) {
                continue;
            }
            let (f, ground) = hm(m, r);
            let apex: Mask = 1u32 << m;
            let apex_deg = deg(apex, &f) as u64;
            assert_eq!(
                apex_deg,
                (m as u64) * pow_sat(r as u64, m - 2),
                "deg({{w}}) in HM({m},{r})"
            );
            // At r = m the apex sits exactly on the ceiling r^(m-1), and
            // no other T is within a factor of one of its own ceiling
            // unless it also contains the apex or is inside a member.
            let ceiling = pow_sat(r as u64, m - 1);
            assert!(apex_deg <= ceiling);
            if r == m {
                assert_eq!(apex_deg, ceiling, "HM({m},{m}) apex is not on the ceiling");
            } else {
                assert!(apex_deg < ceiling, "HM({m},{r}) apex should be slack");
            }
            // Dropping r by one breaks the apex constraint and nothing else
            // is needed to see it.
            if r == m && m >= 3 {
                // Dropping r by one breaks the spread condition, and every
                // way it breaks goes through the apex: the violators are
                // exactly the sets containing w, missing E, and meeting
                // each grid block at most once, of which there are
                // (r-1+1)^(m-2) = m^(m-2). The apex alone is the smallest.
                let (fm, _) = hm(m, r - 1);
                let bad = all_violators(m, &fm, (r - 1) as u64);
                assert!(
                    !bad.is_empty(),
                    "HM({m},{}) must fail the spread condition",
                    r - 1
                );
                assert_eq!(bad[0], 1u32 << m, "the smallest violator is the apex");
                assert!(
                    bad.iter().all(|t| t & (1u32 << m) != 0),
                    "every violator of HM({m},{}) should contain the apex, got {bad:?}",
                    r - 1
                );
                assert_eq!(
                    bad.len() as u64,
                    pow_sat(m as u64, m - 2),
                    "HM({m},{}) should have exactly m^(m-2) violators",
                    r - 1
                );
            }
            let _ = ground;
        }
    }
}

/// The member-subset enumeration above and the full power-set
/// enumeration `Reflect.rao_spreadb` uses must agree. Only run where the
/// ground set is small enough for `2^ground` to be cheap.
#[test]
fn the_two_spread_enumerations_agree() {
    for m in 2..=4u32 {
        for r in 2..=5u32 {
            let (f, ground) = hm(m, r);
            assert_eq!(
                is_spread(m, &f, r as u64),
                is_rao_spread(m, &f, r as u64, ground),
                "the two enumerations disagree on HM({m},{r})"
            );
        }
    }
}

// ---------------------------------------------------------------------
// 3 & 4. Beating the star, and the single crossing point
// ---------------------------------------------------------------------

/// The size half of the claim is pure arithmetic -- `m*r^(m-2) + 1 >
/// r^(m-1)` iff `r <= m` -- so it can be checked far outside the range
/// where the family fits in a 32-point mask.
#[test]
fn beating_the_star_is_arithmetic() {
    for m in 2..=12u128 {
        for r in 2..=20u128 {
            let size = m * r.pow((m - 2) as u32) + 1;
            let star = r.pow((m - 1) as u32);
            assert_eq!(size > star, r <= m, "m={m} r={r}: {size} against {star}");
        }
    }
}

#[test]
fn hm_beats_the_star_exactly_when_r_at_most_m() {
    for (m, r) in scanned_pairs() {
        {
            let (f, _) = hm(m, r);
            let star = pow_sat(r as u64, m - 1);
            assert_eq!(
                (f.len() as u64) > star,
                r <= m,
                "HM({m},{r}): {} members against a star bound of {star}",
                f.len()
            );
        }
    }
}

#[test]
fn spread_and_beating_the_star_coincide_only_at_r_equals_m() {
    for m in 2..=6u32 {
        let mut crossings = Vec::new();
        for r in 2..=7u32 {
            if !fits(m, r) {
                continue;
            }
            let (f, _) = hm(m, r);
            let star = pow_sat(r as u64, m - 1);
            if is_spread(m, &f, r as u64) && (f.len() as u64) > star {
                crossings.push(r);
            }
        }
        assert_eq!(
            crossings,
            vec![m],
            "at uniformity {m} the family refutes star-extremality at {crossings:?}, \
             expected exactly {{{m}}}"
        );
    }
}

// ---------------------------------------------------------------------
// 5. The individual numbers the roadmap quotes
// ---------------------------------------------------------------------

#[test]
fn the_quoted_numbers() {
    // ~StarExtremalAt m m, one row per m, with the margin of exactly one.
    let rows: [(u32, u64, u64); 5] = [
        (2, 3, 2),
        (3, 10, 9),
        (4, 65, 64),
        (5, 626, 625),
        (6, 7777, 7776),
    ];
    for (m, size, star) in rows {
        let (f, _) = hm(m, m);
        assert_eq!(f.len() as u64, size, "|HM({m},{m})|");
        assert_eq!(pow_sat(m as u64, m - 1), star, "star bound at ({m},{m})");
        assert_eq!(size, star + 1, "the margin at ({m},{m}) should be exactly one");
        assert!(is_spread(m, &f, m as u64));
    }

    // The two-cover split at (4,5) is tight against HM: 101 = 76 + 25,
    // where 76 is the conjectured C(3,5) and 25 is r^(m-2).
    let (f45, _) = hm(4, 5);
    assert_eq!(f45.len(), 101);
    assert_eq!(101, 76 + 25);

    // HM(3,5) is `CrossRefined.hm16` up to relabelling: 16 members, and
    // `nonstar_three_bound`'s max(3r+1,16) = 16 is attained.
    let (f35, g35) = hm(3, 5);
    assert_eq!(f35.len(), 16);
    assert!(is_spread(3, &f35, 5));
    assert!(nonstar(&f35, g35));

    // I2(3,r) = 3r+1 for r >= 5: HM(3,r) attains the bound
    // max(3r+1,16), which is 3r+1 there.
    for r in 5..=9u32 {
        let (f, g) = hm(3, r);
        assert_eq!(f.len() as u64, 3 * (r as u64) + 1);
        assert!(is_spread(3, &f, r as u64));
        assert!(nonstar(&f, g));
        assert!(3 * (r as u64) + 1 >= 16, "the max should bind on 3r+1 at r={r}");
    }
}

/// At `m = 2` the construction degenerates to the triangle, which is
/// already in the development as the sharpness witness for
/// `CrossRefined.unpointed_pair_bound`. That the general family reduces
/// to an object the repository already knows is a check on the encoding.
#[test]
fn the_two_uniform_instance_is_the_triangle() {
    let (f, ground) = hm(2, 2);
    assert_eq!(ground, 3);
    let mut got: Vec<Mask> = f.clone();
    got.sort_unstable();
    let mut want: Vec<Mask> = vec![
        0b011, // {0,1} = E
        0b101, // {0,2} = {0,w}
        0b110, // {1,2} = {1,w}
    ];
    want.sort_unstable();
    assert_eq!(got, want);
    assert!(is_spread(2, &f, 2));
    assert_eq!(f.len(), 3);
    assert_eq!(pow_sat(2, 1), 2);
}

// ---------------------------------------------------------------------
// 6. The barrier: what the route could give even if it all worked
// ---------------------------------------------------------------------

/// A minimal exact big natural, base 10^9, enough for `mul_small` and
/// comparison. `(n+1)^n` and `2^n·n!` both overflow `u128` well before
/// `n = 40`, and the claim below is asymptotic, so the comparison has to
/// be exact rather than floating point.
#[derive(Clone, PartialEq, Eq)]
struct Big(Vec<u64>); // little-endian limbs < 10^9

impl Big {
    fn one() -> Big {
        Big(vec![1])
    }
    fn mul_small(&mut self, k: u64) {
        let mut carry = 0u64;
        for l in self.0.iter_mut() {
            let v = *l * k + carry;
            *l = v % 1_000_000_000;
            carry = v / 1_000_000_000;
        }
        while carry > 0 {
            self.0.push(carry % 1_000_000_000);
            carry /= 1_000_000_000;
        }
    }
    /// Number of decimal digits.
    fn digits(&self) -> usize {
        let top = *self.0.last().unwrap();
        (self.0.len() - 1) * 9 + top.to_string().len()
    }
    fn cmp_to(&self, other: &Big) -> std::cmp::Ordering {
        use std::cmp::Ordering::*;
        if self.0.len() != other.0.len() {
            return self.0.len().cmp(&other.0.len());
        }
        for i in (0..self.0.len()).rev() {
            match self.0[i].cmp(&other.0[i]) {
                Equal => continue,
                o => return o,
            }
        }
        Equal
    }
}

/// `f(n,3) <= r^n + 1` needs `r >= n+1` once the star-extremality
/// hypothesis is the source of `SpreadYieldsDisjoint` — because that
/// hypothesis ranges over every uniformity `m <= n` and so includes
/// `StarExtremalAt r r`, which `HM(r,r)` refutes.
///
/// So the route's ceiling is `(n+1)^n + 1`. This checks the arithmetic
/// that the ceiling is *above* Erdős–Rado's `2^n·n! + 1` from `n = 3`
/// on — the route cannot produce a record at `k = 3` even if every
/// conjecture in sight were proved.
#[test]
fn the_route_ceiling_is_worse_than_erdos_rado() {
    // n = 1: both 2. n = 2: 9 against 8, Erdős–Rado already ahead.
    for n in 1..=200u64 {
        let mut route = Big::one(); // (n+1)^n
        for _ in 0..n {
            route.mul_small(n + 1);
        }
        let mut er = Big::one(); // 2^n * n!
        for i in 1..=n {
            er.mul_small(2 * i);
        }
        let ord = er.cmp_to(&route);
        if n == 1 {
            assert_eq!(ord, std::cmp::Ordering::Equal, "n=1: 2^1*1! = 2 = 2^1");
        } else {
            assert_eq!(
                ord,
                std::cmp::Ordering::Less,
                "n={n}: Erdos-Rado should be strictly below the route ceiling"
            );
        }
    }
    // And the gap grows like 1.359^n: the number of decimal digits
    // between the two sides, which is log10 of the ratio.
    let gap = |n: u64| -> i64 {
        let mut route = Big::one();
        for _ in 0..n {
            route.mul_small(n + 1);
        }
        let mut er = Big::one();
        for i in 1..=n {
            er.mul_small(2 * i);
        }
        route.digits() as i64 - er.digits() as i64
    };
    let g50 = gap(50);
    let g100 = gap(100);
    let g200 = gap(200);
    assert!(g50 >= 5, "digit gap at n=50 was {g50}");
    assert!(g100 >= 12, "digit gap at n=100 was {g100}");
    assert!(g200 >= 25, "digit gap at n=200 was {g200}");
    assert!(g50 < g100 && g100 < g200, "the gap should grow: {g50} {g100} {g200}");
}

// ---------------------------------------------------------------------
// 7. The other family that ties at (3,3), and why it does not generalise
// ---------------------------------------------------------------------

/// The complete `m`-uniform hypergraph on `2m-1` points. Any two of its
/// members meet (`m + m > 2m-1`), and its worst degree is that of an
/// `(m-1)`-set, which is `m` — so it is Rao(`m`)-spread for the same
/// arithmetic reason `HM(m,m)` is.
///
/// It beats the star bound `m^(m-1)` at `m = 2` (3 > 2) and `m = 3`
/// (10 > 9) and loses from `m = 4` on (35 < 64). `tau_piece_scan`
/// returns it, not `HM(3,3)`, as the first witness for `I2(3,3) = 10`;
/// the two tie there and only `HM` continues.
fn complete_on_two_m_minus_one(m: u32) -> (Vec<Mask>, u32) {
    let ground = 2 * m - 1;
    let fam: Vec<Mask> = (0u32..(1u32 << ground))
        .filter(|b| b.count_ones() == m)
        .collect();
    (fam, ground)
}

fn binom(n: u64, k: u64) -> u64 {
    let mut acc = 1u64;
    for i in 0..k {
        acc = acc * (n - i) / (i + 1);
    }
    acc
}

#[test]
fn the_complete_graph_on_two_m_minus_one_ties_only_at_m_three() {
    let mut beats = Vec::new();
    for m in 2..=6u32 {
        let (f, ground) = complete_on_two_m_minus_one(m);
        assert_eq!(f.len() as u64, binom((2 * m - 1) as u64, m as u64));
        assert!(intersecting(&f), "K^{m} on {ground} points is not intersecting");
        assert!(
            is_spread(m, &f, m as u64),
            "K^{m} on {ground} points should be Rao({m})-spread"
        );
        assert!(nonstar(&f, ground));
        if (f.len() as u64) > pow_sat(m as u64, m - 1) {
            beats.push(m);
        }
    }
    assert_eq!(
        beats,
        vec![2, 3],
        "the complete family should beat the star only at m = 2 and 3"
    );

    // At (3,3) the two extremal families have the same size and are not
    // isomorphic -- they do not even live on the same number of points.
    let (k5, g5) = complete_on_two_m_minus_one(3);
    let (hm33, g33) = hm(3, 3);
    assert_eq!(k5.len(), hm33.len());
    assert_eq!(k5.len(), 10);
    assert_eq!(g5, 5);
    assert_eq!(g33, 7);
    // and HM(3,3) genuinely needs its seventh point: it is not supported
    // on any 5 of them, since a 5-point support would force the apex
    // degree 9 into C(4,2) = 6 available pairs.
    let support = hm33.iter().fold(0u32, |a, &b| a | b);
    assert_eq!(support.count_ones(), 7);
}

// ---------------------------------------------------------------------
// 8. Below the boundary: projective planes
// ---------------------------------------------------------------------

/// `PG(2,q)` as a family of lines, for a prime `q`: points are the
/// normalised triples over `GF(q)` and a line is the set of points
/// orthogonal to a given one. `(q+1)`-uniform, `q^2+q+1` members, any
/// two of which meet in exactly one point.
fn projective_plane(q: u32) -> (Vec<Mask>, u32) {
    let mut pts: Vec<(u32, u32, u32)> = Vec::new();
    for a in 0..q {
        for b in 0..q {
            pts.push((1, a, b));
        }
    }
    for b in 0..q {
        pts.push((0, 1, b));
    }
    pts.push((0, 0, 1));
    let ground = pts.len() as u32;
    assert_eq!(ground, q * q + q + 1);
    assert!(ground <= 32, "PG(2,{q}) needs {ground} points, past the mask width");
    let dot = |u: (u32, u32, u32), v: (u32, u32, u32)| (u.0 * v.0 + u.1 * v.1 + u.2 * v.2) % q;
    let mut lines: Vec<Mask> = Vec::new();
    for &l in &pts {
        let mut mask: Mask = 0;
        for (i, &p) in pts.iter().enumerate() {
            if dot(l, p) == 0 {
                mask |= 1u32 << i;
            }
        }
        if !lines.contains(&mask) {
            lines.push(mask);
        }
    }
    (lines, ground)
}

/// `HiltonMilner.fano` and `HiltonMilner.pg23`: the `r = 2` end of the
/// star-extremality question, which `HM` cannot reach because it is not
/// spread below `r = m`.
///
/// A projective plane of order `q` is Rao(2)-spread for every `q >= 1`
/// (its worst degree is `q+1` at a point, against a ceiling of `2^q`)
/// and beats the star bound `2^q` exactly when `q^2+q+1 > 2^q` — at
/// `q = 2, 3, 4` and no further.
#[test]
fn projective_planes_refute_star_extremality_at_r_two() {
    let mut refuted = Vec::new();
    // q = 7 would need 57 points, past the 32-bit mask.
    for q in [2u32, 3, 5] {
        let (lines, ground) = projective_plane(q);
        let m = q + 1;
        assert_eq!(lines.len() as u32, q * q + q + 1, "PG(2,{q}) line count");
        assert!(is_uniform(m, &lines), "PG(2,{q}) is not {m}-uniform");
        assert!(intersecting(&lines), "PG(2,{q}) lines do not pairwise meet");
        assert!(nonstar(&lines, ground));
        assert!(
            is_spread(m, &lines, 2),
            "PG(2,{q}) should be Rao(2)-spread"
        );
        if (lines.len() as u64) > pow_sat(2, m - 1) {
            refuted.push(q);
        }
    }
    // q = 4 is a plane too but 4 is not prime, so this construction does
    // not build it; the arithmetic q^2+q+1 > 2^q is checked separately.
    assert_eq!(
        refuted,
        vec![2, 3],
        "among the prime orders tried, only q = 2, 3 beat the star at r = 2"
    );
    for q in 1..=12u64 {
        let beats = q * q + q + 1 > 1u64 << q;
        assert_eq!(beats, q <= 4, "q={q}: q^2+q+1 against 2^q");
    }

    // The exact families in coq/HiltonMilner.v.
    let (fano, gf) = projective_plane(2);
    assert_eq!(gf, 7);
    assert_eq!(fano.len(), 7);
    assert!(7 > pow_sat(2, 2)); // against the star bound 4
    let (pg23, gp) = projective_plane(3);
    assert_eq!(gp, 13);
    assert_eq!(pg23.len(), 13);
    assert!(13 > pow_sat(2, 3)); // against the star bound 8
}

/// The `m = 3` row of Conjecture T, complete: star extremality at
/// uniformity three fails at `r = 2` (Fano) and `r = 3` (`HM(3,3)`) and
/// holds at every `r >= 4` (`TauThree.three_uniform_star_extremal`).
///
/// The failure side is what this checks; the `r >= 4` side is a Coq
/// theorem, not a computation. `r = 0` and `r = 1` are degenerate — both
/// force an intersecting family to have at most one member — which is
/// why the threshold has to be defined as "holds for every larger `r`"
/// rather than "least `r`".
#[test]
fn the_uniformity_three_row_fails_exactly_at_two_and_three() {
    let (fano, _) = projective_plane(2);
    assert!(is_spread(3, &fano, 2) && fano.len() as u64 > pow_sat(2, 2));

    let (hm33, _) = hm(3, 3);
    assert!(is_spread(3, &hm33, 3) && hm33.len() as u64 > pow_sat(3, 2));

    // The `r >= 4` side is `TauThree.three_uniform_star_extremal`, a Coq
    // theorem rather than a computation, and is not re-checked here: an
    // exhaustive search over a fixed ground would only ever confirm it on
    // that ground, and the ground-8 run needed more time than this suite
    // is allowed. What is checked here is the failure side, which is what
    // the two witnesses are for.
}
