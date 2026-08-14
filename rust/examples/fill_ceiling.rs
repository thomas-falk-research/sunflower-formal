//! How far does a pure random fill get, and does it ever reach the
//! constructions that are known to live on the same ground set?
//!
//! `docs/roadmap.md` records that `plateau.rs`'s fill move "can never
//! beat" the 1972 constructions, because a fill stops at a *maximal*
//! family and `extend.rs` shows those constructions are already
//! maximal. That is an argument about where a fill *stops*, not a
//! measurement of where it stops in practice, and the two are different
//! claims. This driver measures.
//!
//! The interesting parameters are the ones where the answer is known:
//!
//! * `(3, 6)` and `(3, 7)`: `iota(3) = 10`, exhaustively (`wide.rs`).
//! * `(4, 9)`: `Product.iota_four_at_least_27` puts a 27-member family
//!   on exactly nine points.

use sunflower_formal::plateau;

fn main() {
    let runs: u64 = std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(100_000);
    println!("  b    n   runs      target   best   hits    mean");
    for &(b, n, target) in &[(3u32, 6u32, 10usize), (3, 7, 10), (3, 10, 10), (4, 9, 27), (4, 10, 27)] {
        let mut best = 0usize;
        let mut hits = 0u64;
        let mut total = 0u64;
        let mut hist = [0u64; 64];
        for s in 0..runs {
            let f = plateau::search(n, b, 0, s.wrapping_mul(0x9E3779B97F4A7C15) ^ 0x5A5A, &[], true, |_, _| {});
            total += f.best as u64;
            hist[f.best.min(63)] += 1;
            if f.best > best {
                best = f.best;
            }
            if f.best >= target {
                hits += 1;
            }
        }
        println!(
            "{b:3} {n:4} {runs:6}  {target:8} {best:6} {hits:6}  {:6.2}",
            total as f64 / runs as f64
        );
        let lo = hist.iter().position(|&c| c > 0).unwrap();
        let hi = 63 - hist.iter().rev().position(|&c| c > 0).unwrap();
        let cells: Vec<String> = (lo..=hi).map(|i| format!("{i}:{}", hist[i])).collect();
        println!("       {}", cells.join(" "));
    }
}
