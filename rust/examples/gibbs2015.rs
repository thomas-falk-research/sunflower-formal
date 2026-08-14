//! Re-run the 2015 Polymath10 random-fill experiment on intersecting
//! sunflower-free families, at the parameters it was run on.
//!
//! Source: Philip Gibbs ("GFP"), comment 22690 on *Polymath10, Post 2:
//! Homological Approach*, 25 Nov 2015. He reports, for each `(k, n)`,
//! the average and maximum family size over 100 runs of the random
//! greedy process, requiring the family to be intersecting.
//!
//! `plateau::search` with `steps = 0` is that process: fill to
//! maximality at random, stop. Nothing else in this repository is a
//! pure fill, so this driver exists to say what the 2015 method
//! actually reaches.

use sunflower_formal::plateau;

fn fill_max(ground: u32, b: u32, runs: u64) -> (f64, usize) {
    let mut total = 0usize;
    let mut best = 0usize;
    for s in 0..runs {
        let f = plateau::search(ground, b, 0, s.wrapping_mul(0x9E3779B97F4A7C15) ^ 0xA5, &[], true, |_, _| {});
        total += f.best;
        if f.best > best {
            best = f.best;
        }
    }
    (total as f64 / runs as f64, best)
}

fn main() {
    let runs: u64 = std::env::args()
        .nth(1)
        .and_then(|s| s.parse().ok())
        .unwrap_or(100);
    // (k, n, average reported in 2015, max reported in 2015)
    let rows: &[(u32, u32, f64, usize)] = &[
        (3, 4, 4.0, 4),
        (3, 7, 8.61, 10),
        (3, 10, 7.24, 10),
        (3, 13, 6.97, 10),
        (4, 5, 5.0, 5),
        (4, 9, 18.06, 21),
        (4, 13, 17.56, 22),
        (4, 17, 17.67, 24),
        (4, 21, 17.45, 21),
        (5, 6, 6.0, 6),
        (5, 11, 38.46, 42),
        (5, 16, 37.43, 46),
        (5, 21, 38.43, 58),
        (5, 26, 38.86, 49),
        (5, 31, 40.23, 52),
    ];
    println!("  k    n    avg2015  max2015     avg     max");
    for &(k, n, a15, m15) in rows {
        let (avg, max) = fill_max(n, k, runs);
        println!("{k:3} {n:4}  {a15:8.2} {m15:8}  {avg:6.2}  {max:6}");
    }
}
