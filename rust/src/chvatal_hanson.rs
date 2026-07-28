//! The Chvátal–Hanson extremal function, and the two places it governs
//! this development.
//!
//! # Why this module exists
//!
//! At uniformity 2 the spread condition collapses into a degree bound.
//! `RaoSpread 2 F r` asks `deg T F <= r^(2 - |T|)` for every nonempty
//! `T`; for a *distinct* 2-uniform family the `|T| = 2` clause reads
//! `deg T F <= 1`, which holds automatically, and every larger `T` has
//! degree 0. What is left is the `|T| = 1` clause: every vertex lies in
//! at most `r` members. So
//!
//! > `RaoSpread 2 F r` <-> `F` is a simple graph with maximum degree
//! > at most `r`,
//!
//! and `SpreadReduction.SpreadYieldsDisjoint 2 k r` says precisely:
//!
//! > a simple graph with maximum degree at most `r` and more than `r^2`
//! > edges has `k` pairwise disjoint edges.
//!
//! That is a statement about the extremal function
//!
//! > `CH(D, v)` = the largest number of edges in a simple graph with
//! > maximum degree at most `D` and matching number at most `v`,
//!
//! evaluated by Chvátal and Hanson (*Degrees and matchings*, JCTB 20
//! (1976) 128–138):
//!
//! ```text
//!     CH(D, v) = v*D + floor(D/2) * floor(v / ceil(D/2)).
//! ```
//!
//! Two consequences, which is why one function is worth a module:
//!
//! * **the sharp spread threshold at uniformity 2** is
//!   `r*(2,k) = min { r : CH(r, k-1) <= r^2 }` — below it the extremal
//!   graph is a counterexample, at or above it the statement is true;
//! * **an infinite family of exact sunflower numbers**,
//!   `f(2,k) = CH(k-1, k-1) + 1`. A `k`-sunflower in a graph is `k`
//!   disjoint edges or `k` edges through a point, so a 2-uniform family
//!   has no `k`-sunflower exactly when its matching number and its
//!   maximum degree are both at most `k-1`.
//!
//! The roadmap listed the Rao campaign and the `f(2,k)` program as
//! alternatives. They are the same extremal function seen twice.
//!
//! # What is checked here
//!
//! The formula is *recalled* from the literature, so it is treated the
//! way this repository treats every recalled statement — as something
//! to falsify before building on it. [`ch`] is the formula;
//! [`max_edges`] computes the same quantity by exhaustive search over a
//! ground set; [`extremal`] builds the construction that is supposed to
//! attain it. `tests/chvatal_hanson.rs` runs all three against each
//! other, and against the spread thresholds `tests/spread_axiom.rs`
//! measures independently.

use crate::spread::{matching_number, Mask};
use crate::testbed::search;

/// `CH(d, v)`: the largest number of edges in a simple graph with
/// maximum degree at most `d` and matching number at most `v`.
///
/// `CH(d, v) = v*d + floor(d/2) * floor(v / ceil(d/2))`.
pub fn ch(d: u64, v: u64) -> u64 {
    if d == 0 || v == 0 {
        return 0;
    }
    let half_up = d.div_ceil(2);
    v * d + (d / 2) * (v / half_up)
}

/// The number of vertices [`extremal`] uses.
pub fn extremal_vertices(d: u64, v: u64) -> u64 {
    if d == 0 || v == 0 {
        return 0;
    }
    let half_up = d.div_ceil(2);
    let (cliques, stars) = (v / half_up, v % half_up);
    cliques * (2 * half_up + 1) + stars * (d + 1)
}

/// The extremal construction: a disjoint union of
///
/// * `floor(v / ceil(d/2))` copies of the densest graph on
///   `2*ceil(d/2) + 1` vertices with maximum degree `d` — an odd
///   number of vertices, so its matching number is `ceil(d/2)` and it
///   contributes `ceil(d/2)*d + floor(d/2)` edges, more per unit of
///   matching number than anything else available; and
/// * `v mod ceil(d/2)` stars `K_{1,d}`, which spend the leftover
///   matching budget one unit at a time.
///
/// Both component types are "odd near-regular": all the slack in the
/// bound `2*(edges) <= (vertices)*d` comes from the single unmatched
/// vertex in each component, which is where the `floor(d/2)` term in
/// [`ch`] comes from.
///
/// Vertices are numbered from 0; the result is a list of 2-element
/// bitmasks, so it needs [`extremal_vertices`] to be at most 32.
pub fn extremal(d: u64, v: u64) -> Vec<Mask> {
    assert!(
        extremal_vertices(d, v) <= 32,
        "extremal(d = {d}, v = {v}) needs {} vertices, more than a u32 mask holds",
        extremal_vertices(d, v)
    );
    if d == 0 || v == 0 {
        return Vec::new();
    }
    let half_up = d.div_ceil(2);
    let (cliques, stars) = (v / half_up, v % half_up);
    let mut f = Vec::new();
    let mut base = 0u32;

    for _ in 0..cliques {
        let n = (2 * half_up + 1) as u32;
        f.extend(odd_near_regular(base, n, d as u32));
        base += n;
    }
    for _ in 0..stars {
        for leaf in 1..=d as u32 {
            f.push(edge(base, base + leaf));
        }
        base += d as u32 + 1;
    }
    f
}

fn edge(u: u32, w: u32) -> Mask {
    1 << u | 1 << w
}

/// The densest graph on the `n` vertices `base .. base + n` with
/// maximum degree at most `d`, for `n` odd and `n >= d + 1`.
///
/// `K_n` has degree `n - 1`. When `n = d + 1` that is already `d` and
/// the complete graph is the answer. Otherwise `n = d + 2` and every
/// degree must drop by exactly one, so a minimum edge cover is removed
/// — a near-perfect matching plus one edge to reach the last vertex,
/// `(n+1)/2` edges, which is the least possible.
fn odd_near_regular(base: u32, n: u32, d: u32) -> Vec<Mask> {
    assert!(n % 2 == 1 && n >= d + 1 && n <= d + 2);
    let mut f = Vec::new();
    for i in 0..n {
        for j in (i + 1)..n {
            f.push(edge(base + i, base + j));
        }
    }
    if n == d + 2 {
        let mut cover: Vec<Mask> = (0..(n - 1) / 2)
            .map(|i| edge(base + 2 * i, base + 2 * i + 1))
            .collect();
        cover.push(edge(base, base + n - 1));
        f.retain(|e| !cover.contains(e));
    }
    f
}

/// The exhaustive counterpart of [`ch`], restricted to a ground set:
/// the largest graph on `ground` vertices with maximum degree at most
/// `d` and matching number at most `v`.
///
/// This is [`crate::testbed::search`] at `m = 2`, `k = v + 1`, `r = d`,
/// which is the identification this module is about: at uniformity 2
/// the search for a maximum spread family with no `k` disjoint members
/// *is* the Chvátal–Hanson search.
///
/// Always at most `CH(d, v)`; equal to it once `ground` is at least
/// [`extremal_vertices`].
pub fn max_edges(ground: u32, d: u64, v: u64) -> Vec<Mask> {
    search(ground, 2, (v + 1) as usize, d, false).largest
}

/// `f(2,k) = CH(k-1, k-1) + 1`, the exact sunflower number at
/// uniformity 2 — the least size forcing a `k`-sunflower in a family of
/// distinct pairs.
pub fn f_2_k(k: u64) -> u64 {
    if k == 0 {
        return 0;
    }
    ch(k - 1, k - 1) + 1
}

/// `r*(2,k) = min { r : CH(r, k-1) <= r^2 }`, the sharp threshold for
/// `SpreadReduction.SpreadYieldsDisjoint 2 k r`.
///
/// Below it the extremal graph has more than `r^2` edges, maximum
/// degree `r` — hence is `r`-spread — and matching number `k-1`, so it
/// refutes the statement. At or above it no graph clears `r^2` without
/// picking up `k` disjoint edges.
pub fn r_star(k: u64) -> u64 {
    let mut r = 1;
    while ch(r, k - 1) > r * r {
        r += 1;
    }
    r
}

/// Maximum degree of a 2-uniform family, over vertices `0..ground`.
pub fn max_degree(f: &[Mask], ground: u32) -> usize {
    (0..ground)
        .map(|v| f.iter().filter(|&&a| a >> v & 1 == 1).count())
        .max()
        .unwrap_or(0)
}

/// Check a claimed extremal graph against the two constraints and the
/// claimed size, from scratch rather than by construction.
pub fn verify_extremal(f: &[Mask], d: u64, v: u64) -> Result<(), String> {
    let ground = 32;
    if !crate::spread::is_uniform(2, f) {
        return Err("not a graph: some member is not a 2-set".to_string());
    }
    if !crate::spread::is_distinct(f) {
        return Err("repeated edge".to_string());
    }
    let deg = max_degree(f, ground) as u64;
    if deg > d {
        return Err(format!("maximum degree {deg} exceeds {d}"));
    }
    let nu = matching_number(f) as u64;
    if nu > v {
        return Err(format!("matching number {nu} exceeds {v}"));
    }
    if f.len() as u64 != ch(d, v) {
        return Err(format!(
            "{} edges, but CH({d}, {v}) = {}",
            f.len(),
            ch(d, v)
        ));
    }
    Ok(())
}

/// A table of `CH`, the constructions attaining it, and the two
/// quantities it determines, for the build log.
pub fn report(kmax: u64) -> String {
    let mut out = String::new();
    out.push_str("  Chvatal-Hanson CH(D, v) = v*D + floor(D/2)*floor(v/ceil(D/2))\n\n");
    out.push_str("      D\\v ");
    for v in 1..=kmax {
        out.push_str(&format!("{v:>5}"));
    }
    out.push('\n');
    for d in 1..=kmax {
        out.push_str(&format!("  {d:>7} ", ));
        for v in 1..=kmax {
            out.push_str(&format!("{:>5}", ch(d, v)));
        }
        out.push('\n');
    }
    out.push_str("\n  What it determines at uniformity 2\n\n");
    out.push_str("    k    f(2,k) = CH(k-1,k-1)+1    r*(2,k) = min{r : CH(r,k-1) <= r^2}\n");
    for k in 2..=kmax + 1 {
        out.push_str(&format!(
            "  {k:>3}    {:>22}    {:>33}\n",
            f_2_k(k),
            r_star(k)
        ));
    }
    out.push_str(
        "\n  The threshold column is r*(2,k) = k for every k >= 3, against the\n  \
         2k-1 that SpreadReduction.spread_disjoint_above_elementary proves.\n",
    );
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The formula reproduces the values that can be checked by hand.
    #[test]
    fn ch_small_values() {
        assert_eq!(ch(0, 5), 0);
        assert_eq!(ch(5, 0), 0);
        // A matching: v disjoint edges.
        assert_eq!(ch(1, 4), 4);
        // Triangles: 3 edges each, matching number 1.
        assert_eq!(ch(2, 1), 3);
        assert_eq!(ch(2, 3), 9);
        // Two triangles — `F23.two_triangles`, the f(2,3) witness.
        assert_eq!(ch(2, 2), 6);
        // K_4 plus a star, or a 3-regular-ish graph on 7 vertices.
        assert_eq!(ch(3, 3), 10);
        // Two copies of K_5.
        assert_eq!(ch(4, 4), 20);
    }

    /// `f(2,3) = 7` is `F23.f_2_3_eq_7`, the one exact sunflower number
    /// the repository proves. The formula must agree.
    #[test]
    fn f_2_3_is_7() {
        assert_eq!(f_2_k(3), 7);
    }

    /// For odd `k` the construction is two disjoint copies of `K_k`,
    /// giving `f(2,k) = k(k-1) + 1`; for even `k` one near-regular
    /// graph on `k+1` vertices plus `(k-2)/2` stars.
    #[test]
    fn f_2_k_closed_forms() {
        for k in 3..=15u64 {
            if k % 2 == 1 {
                assert_eq!(f_2_k(k), k * (k - 1) + 1, "odd k = {k}");
            } else {
                assert_eq!(f_2_k(k), (k - 1) * (k - 1) + (k - 2) / 2 + 1, "even k = {k}");
            }
        }
    }

    /// The construction really has the degree bound, the matching
    /// number, and the edge count claimed for it.
    #[test]
    fn extremal_attains_ch() {
        for d in 1..=6u64 {
            for v in 1..=6u64 {
                if extremal_vertices(d, v) > 32 {
                    continue;
                }
                let f = extremal(d, v);
                verify_extremal(&f, d, v)
                    .unwrap_or_else(|e| panic!("extremal(d = {d}, v = {v}) is wrong: {e}"));
            }
        }
    }

    /// At `d = v = k-1` with `k` odd the construction is exactly two
    /// disjoint copies of `K_k`, which is `F23.two_triangles` at
    /// `k = 3`. This is the shape the Coq lower bound generalises.
    #[test]
    fn odd_case_is_two_cliques() {
        for k in [3u64, 5, 7] {
            let d = k - 1;
            let f = extremal(d, d);
            assert_eq!(f.len() as u64, k * (k - 1));
            assert_eq!(extremal_vertices(d, d), 2 * k);
            // Two components, each a K_k on consecutive vertices.
            for (lo, hi) in [(0u32, k as u32), (k as u32, 2 * k as u32)] {
                for i in lo..hi {
                    for j in (i + 1)..hi {
                        assert!(f.contains(&edge(i, j)), "K_{k} missing edge {i}-{j}");
                    }
                }
            }
        }
    }
}
