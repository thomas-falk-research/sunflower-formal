//! The Erdős–Rado ratio, and whether it can be a constant.
//!
//! Erdős–Rado's proof is one step iterated. Find a heavy point, recurse
//! into its link. `Intersecting.sunflower_free_star_bound` proves the
//! step: every 3-sunflower-free `b`-uniform family has a point of degree
//! at least `|F| / (2b)`. Write
//!
//! ```text
//!   rho(F)  =  |F| / maxdeg(F)
//! ```
//!
//! for the ratio that step bounds. Two facts make it the quantity to
//! watch.
//!
//! **It is exactly what the recursion pays.** The link at a maximum
//! degree point has `maxdeg(F)` members and uniformity `b - 1`, so
//! `|F| = rho(F) * |link|` and, descending to the bottom,
//!
//! ```text
//!   |F|  =  rho_0 * rho_1 * ... * rho_{b-1}
//! ```
//!
//! **exactly**, not as an estimate. Erdős–Rado bounds each factor by
//! `2(b-j)` and gets `2^b b!`. The sunflower conjecture at `k = 3` is
//! precisely that the product is `C^b` — that the ratios are `O(1)`
//! *on average along the chain*.
//!
//! **And a constant bound on a single factor would settle it outright.**
//! If `rho(F) <= c` for every sunflower-free family then
//! `g(b) <= c * g(b-1)`, hence `g(b) <= 2c^(b-1)`: the whole conjecture,
//! from one inequality with one number in it. `coq/StarDefect.v` proves
//! that implication.
//!
//! So: is `rho` bounded? `rust/tests/iota_sandwich.rs` has measured it
//! for a while — worst observed 2, 3, 2.75 at uniformities 1, 2, 3
//! against the proved 2, 4, 6 — and that row looks flat.
//!
//! **It is not flat.** `rho` is *exactly multiplicative* under the
//! Abbott–Hanson–Sauer substitution:
//!
//! ```text
//!   |substitute(G,H)|      = |G| |H|^a
//!   maxdeg(substitute(G,H)) = maxdeg(G) maxdeg(H) |H|^(a-1)
//!   ==>  rho(substitute(G,H)) = rho(G) rho(H)
//! ```
//!
//! — the `|H|^(a-1)` cancels. With `rho(iota(2)) = 3/2` and
//! `rho(iota(3)) = 2`, iterating the substitution on `iota(3)` gives
//! `rho = 2^k` at `b = 3^k`, i.e. `rho = b^(log_3 2) = b^0.6309...`.
//! Unbounded. So **no constant star bound exists**, and the family that
//! refutes it is the one giving the best lower bound known.
//!
//! What survives is the average. On the same tower the product of the
//! `b` chain ratios is `10^((b-1)/2)`, so their geometric mean is
//! `10^((b-1)/(2b)) -> sqrt(10) = 3.162...` — bounded, while the largest
//! single factor grows like `b^0.63`. That gap is exactly
//! `docs/roadmap.md` §4's "are the covers correlated across levels?",
//! and it is the shape "pay the log once" has to take.

/// `maxdeg(F)`: the largest number of members through a single point.
pub fn maxdeg_128(f: &[u128]) -> usize {
    let support = f.iter().fold(0u128, |a, &x| a | x);
    (0..128)
        .filter(|p| support >> p & 1 == 1)
        .map(|p| f.iter().filter(|&&a| a >> p & 1 == 1).count())
        .max()
        .unwrap_or(0)
}

/// A point attaining `maxdeg`, or `None` for an empty family.
pub fn heaviest_point_128(f: &[u128]) -> Option<u32> {
    let support = f.iter().fold(0u128, |a, &x| a | x);
    (0..128)
        .filter(|p| support >> p & 1 == 1)
        .max_by_key(|&p| f.iter().filter(|&&a| a >> p & 1 == 1).count())
}

/// `rho(F) = |F| / maxdeg(F)`, exactly, as `(numerator, denominator)`.
pub fn rho_128(f: &[u128]) -> (usize, usize) {
    (f.len(), maxdeg_128(f))
}

/// `rho` as a float, for tables only. Comparisons stay on the rational.
pub fn rho_value(f: &[u128]) -> f64 {
    let (n, d) = rho_128(f);
    if d == 0 {
        0.0
    } else {
        n as f64 / d as f64
    }
}

/// The link at `p`: the members through `p`, with `p` removed.
pub fn link_128(f: &[u128], p: u32) -> Vec<u128> {
    f.iter()
        .filter(|&&a| a >> p & 1 == 1)
        .map(|&a| a & !(1u128 << p))
        .collect()
}

/// One level of the greedy chain.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Level {
    /// The uniformity at this level.
    pub b: u32,
    /// How many members the family at this level has.
    pub size: usize,
    /// The heaviest point's degree — the size of the next level.
    pub deg: usize,
    /// The point chosen.
    pub point: u32,
}

impl Level {
    /// `rho` at this level, exactly.
    pub fn rho(&self) -> (usize, usize) {
        (self.size, self.deg)
    }
}

/// Descend the greedy maximum-degree chain and record every level.
///
/// The product of the ratios telescopes to `|F| / (size of the last
/// level)`, and the last level has one member (the empty set) whenever
/// the descent runs the full `b` steps — so the product **is** `|F|`.
/// That identity is checked in `rust/tests/star_defect.rs` rather than
/// assumed here.
pub fn greedy_chain(f: &[u128], b: u32) -> Vec<Level> {
    let mut out = Vec::new();
    let mut cur = f.to_vec();
    for j in 0..b {
        if cur.is_empty() {
            break;
        }
        let p = match heaviest_point_128(&cur) {
            Some(p) => p,
            None => break,
        };
        let next = link_128(&cur, p);
        out.push(Level {
            b: b - j,
            size: cur.len(),
            deg: next.len(),
            point: p,
        });
        cur = next;
    }
    out
}

/// The largest `rho` over the chain, and the geometric mean, as floats.
///
/// The gap between them is the measurement: a bounded maximum would
/// settle the conjecture outright, a bounded mean *is* the conjecture,
/// and the substitution families separate the two.
pub fn chain_profile(levels: &[Level]) -> (f64, f64) {
    if levels.is_empty() {
        return (0.0, 0.0);
    }
    let mut max = 0.0f64;
    let mut logsum = 0.0f64;
    for l in levels {
        let r = l.size as f64 / l.deg.max(1) as f64;
        if r > max {
            max = r;
        }
        logsum += r.ln();
    }
    (max, (logsum / levels.len() as f64).exp())
}
