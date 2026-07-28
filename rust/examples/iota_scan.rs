//! iota(b): the largest intersecting 3-sunflower-free b-uniform family.
//!
//! The Abbott-Hanson-Sauer rate is iota(b)^(1/(b-1)); iota(3) = 10 gives
//! their 10^(1/2) = 3.162. Any b with iota(b) > 10^((b-1)/2) improves it.
use sunflower_formal::intersecting::{max_intersecting_from, verify};

fn main() {
    let budget: u64 = std::env::args().nth(1).and_then(|s| s.parse().ok())
        .unwrap_or(20_000_000_000);
    println!("   b    g   iota(b,g)  exhaustive   rate=iota^(1/(b-1))   AHS target");
    for b in 2u32..=5 {
        let target = 10f64.powf((b as f64 - 1.0) / 2.0);
        // iota(b,g) is non-decreasing in g, so the previous row is a
        // valid incumbent -- and it is what makes the search finish.
        let mut seed = 0usize;
        for g in b..=(4 * b).min(16) {
            let t = std::time::Instant::now();
            let (n, fam, done) = max_intersecting_from(g, b, budget, seed);
            if !fam.is_empty() {
                verify(&fam, b, true).expect("witness is not an intersecting sf family");
            }
            seed = n;
            let rate = if b > 1 { (n as f64).powf(1.0 / (b as f64 - 1.0)) } else { 0.0 };
            println!(
                "   {b}   {g:>2}   {n:>6}      {:<7}   {rate:.4}                {target:.1}   ({:.1}s)",
                if done { "yes" } else { "NO" }, t.elapsed().as_secs_f64()
            );
            if !done { break; }
        }
    }
}
