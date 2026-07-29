//! Ground 10 only: does `iota(4)` reach 32 there?
//!
//! The agreement check between the decision search and the plain maximum
//! search lives in `tests/intersecting.rs`; this is just the one
//! expensive query, kept separate so a long run is not preceded by ten
//! minutes of checking.
use std::io::Write;
use sunflower_formal::intersecting::{iota_decide, verify};

fn main() {
    let ground: u32 = std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(10);
    let target: usize = std::env::args().nth(2).and_then(|s| s.parse().ok()).unwrap_or(32);
    println!(
        "b = 4, ground {ground}, target {target} (rate {:.4}; AHS is 3.1623)",
        (target as f64).powf(1.0 / 3.0)
    );
    std::io::stdout().flush().ok();

    let t = std::time::Instant::now();
    let (reached, fam, done) = iota_decide(ground, 4, target, 20_000_000_000_000);
    let secs = t.elapsed().as_secs_f64();

    if reached {
        verify(&fam, 4, true).expect("witness invalid");
        println!("FOUND {} members in {secs:.0}s", fam.len());
        println!(
            "{:?}",
            fam.iter()
                .map(|m| (0..16u32).filter(|x| m >> x & 1 == 1).collect::<Vec<_>>())
                .collect::<Vec<_>>()
        );
    } else if done {
        println!("NO family of {target}+ on {ground} points -- exhaustive ({secs:.0}s)");
    } else {
        println!("inconclusive: budget exhausted after {secs:.0}s");
    }
    std::io::stdout().flush().ok();
}
