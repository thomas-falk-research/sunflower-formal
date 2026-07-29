//! Does `iota(b, g)` plateau in the ground set, and what do the extremal
//! families look like?
//!
//! Two questions, both cheap, both aimed at `IotaGroundBounded` — the
//! hypothesis that an extremal *intersecting* sunflower-free `b`-uniform
//! family can be realised on `O(b)` points. `coq/SliceRank.v` proves that
//! it plus Naslund-Sawin settles the sunflower conjecture at `k = 3`; the
//! general version of the same hypothesis is the one that file already
//! carried, and the general ground-set row is *still climbing* where the
//! intersecting one has gone flat. This measures how flat.
//!
//! 1. **The plateau.** `iota(3, g)` was known flat at 10 from `g = 6` to
//!    `g = 11`. Push it further. Every extra flat entry is evidence the
//!    intersecting problem is ground-set-bounded where the general one is
//!    not measurably so.
//!
//! 2. **The structure.** `iota3`'s extremal family is 5-regular on six
//!    points. Is regularity a pattern? The degree-counting bound
//!    `b * |F| <= g * N(b-1, g-1)` (proved in `coq/IotaGround.v` as
//!    `link_degree_ground_bound`) is met with equality exactly when the
//!    family is regular *and* every link is an extremal `N(b-1,g-1)`
//!    family, so the tight rows are where the structure is rigid.
//!
//! Usage: `cargo run --release --example iota_ground [max_ground_b3]`

use std::io::Write;

use sunflower_formal::ground::max_sunflower_free;
use sunflower_formal::intersecting::{iota, iota_decide, verify};

const BUDGET: u64 = 20_000_000_000_000;

/// Degrees of every ground point, and the diversity `|F| - maxdeg`.
fn degrees(f: &[u32], ground: u32) -> (Vec<usize>, usize) {
    let d: Vec<usize> = (0..ground)
        .map(|x| f.iter().filter(|a| *a >> x & 1 == 1).count())
        .collect();
    let maxdeg = d.iter().copied().max().unwrap_or(0);
    (d, f.len() - maxdeg)
}

fn regular(d: &[usize]) -> bool {
    d.iter().all(|x| *x == d[0])
}

fn main() {
    let maxg3: u32 = std::env::args()
        .nth(1)
        .and_then(|s| s.parse().ok())
        .unwrap_or(14);

    // ---- 1. The plateau, pushed. -------------------------------------
    println!("iota(b, g): the intersecting row, extended");
    println!("  b   g   iota   rate      (N(b,g) general, where affordable)");
    std::io::stdout().flush().ok();

    for b in 2u32..=3 {
        let hi = if b == 2 { 12 } else { maxg3 };
        for g in b..=hi {
            let t = std::time::Instant::now();
            let (n, fam, done) = iota(g, b, BUDGET, 0);
            let secs = t.elapsed().as_secs_f64();
            if !fam.is_empty() {
                verify(&fam, b, true).unwrap_or_else(|e| panic!("iota({b},{g}): {e}"));
            }
            // The general maximum, for the comparison that motivates all
            // of this -- but only where it is affordable. N(3,9) is a
            // quarter of an hour and N(3,10) does not finish.
            let general = if b <= 2 || g <= 8 {
                let (m, _, d) = max_sunflower_free(g, b, BUDGET);
                if d { format!("{m}") } else { format!(">={m}") }
            } else {
                "-".to_string()
            };
            let rate = (n as f64).powf(1.0 / (b as f64 - 1.0));
            println!(
                "  {b}  {g:>2}   {n:>4}   {rate:.4}    {general:>8}   ({secs:.1}s{})",
                if done { "" } else { ", budget" }
            );
            std::io::stdout().flush().ok();
        }
    }

    // ---- 2. The structure of the extremal families. ------------------
    println!();
    println!("Extremal iota witnesses: degree sequence and diversity");
    println!("  b   g   |F|  maxdeg  div  regular   b|F|   g*N(b-1,g-1)  tight?");
    std::io::stdout().flush().ok();

    // (b, ground, a target known to be attained) -- the decision form
    // returns as soon as it finds one, which is what we want here.
    // Ground 10 at b = 4 is deliberately absent: finding a 27-member
    // family there is not informative (one embeds from ground 9) and the
    // search for it is expensive. The informative question at that row is
    // whether 28 is reachable, which is `iota_ladder`.
    let cases: [(u32, u32, usize); 8] = [
        (2, 3, 3),
        (2, 6, 3),
        (3, 6, 10),
        (3, 7, 10),
        (3, 8, 10),
        (3, 9, 10),
        (4, 8, 24),
        (4, 9, 27),
    ];

    for (b, g, target) in cases {
        let (found, fam, _) = iota_decide(g, b, target, BUDGET);
        if !found {
            println!("  {b}  {g:>2}   -- no family of {target} found");
            continue;
        }
        verify(&fam, b, true).unwrap_or_else(|e| panic!("witness ({b},{g}): {e}"));
        let (d, div) = degrees(&fam, g);
        // The link bound: every point's link is a (b-1)-uniform
        // sunflower-free family on the other g-1 points, so
        // b|F| = sum of degrees <= g * N(b-1, g-1).
        let cap = {
            let (m, _, done) = max_sunflower_free(g - 1, b - 1, BUDGET);
            assert!(done, "N({},{}) did not finish", b - 1, g - 1);
            m
        };
        let lhs = b as usize * fam.len();
        let rhs = g as usize * cap;
        assert!(lhs <= rhs, "link degree bound violated at b={b}, g={g}");
        println!(
            "  {b}  {g:>2}  {:>4}  {:>6}  {div:>3}  {:>7}   {lhs:>4}   {rhs:>12}  {}",
            fam.len(),
            d.iter().copied().max().unwrap_or(0),
            if regular(&d) { "yes" } else { "no" },
            if lhs == rhs { "TIGHT" } else { "" }
        );
        std::io::stdout().flush().ok();
    }
}
