//! Does `iota(4) >= 32`? That -- not the exact value -- is what decides
//! whether `b = 4` beats the 1972 bound.
//!
//! Asking the decision question is much cheaper than asking for the
//! maximum: seeding the incumbent at `target - 1` makes the bound
//! `|cur| + |cands| <= target - 1` prune every branch that cannot reach
//! the target, which is almost all of them once the target is above the
//! true value.
use sunflower_formal::intersecting::{iota, verify};

fn main() {
    let target: usize = std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(32);
    let budget: u64 = std::env::args().nth(2).and_then(|s| s.parse().ok())
        .unwrap_or(2_000_000_000_000);
    println!("b = 4: is there an intersecting sunflower-free family of {target}+ 4-sets?");
    println!("  (iota(4) >= {target} would give rate {:.4} against AHS's 3.1623)",
             (target as f64).powf(1.0 / 3.0));
    for g in 9u32..=13 {
        let t = std::time::Instant::now();
        let (n, fam, done) = iota(g, 4, budget, target - 1);
        let secs = t.elapsed().as_secs_f64();
        if fam.is_empty() {
            println!("  ground {g:>2}: NO family of {target}+ {}   ({secs:.0}s)",
                     if done { "-- exhaustive" } else { "found, but budget ran out" });
        } else {
            verify(&fam, 4, true).expect("witness invalid");
            println!("  ground {g:>2}: FOUND {n} >= {target}  rate {:.4}  ({secs:.0}s)",
                     (n as f64).powf(1.0 / 3.0));
            println!("    witness: {:?}", fam.iter()
                .map(|m| (0..16u32).filter(|x| m >> x & 1 == 1).collect::<Vec<_>>())
                .collect::<Vec<_>>());
        }
    }
}
