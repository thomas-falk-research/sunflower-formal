//! Why `b = 3` is special.
//!
//! On `2b` points, two `b`-sets are disjoint exactly when they are
//! complementary. So an intersecting family takes at most one from each
//! complementary pair — a ceiling of `C(2b,b)/2` — and whether
//! `iota(b, 2b)` reaches it is exactly whether some transversal of those
//! pairs is sunflower-free.
//!
//! ```text
//!     b = 2:  ceiling  3    reached  ->  rate 3
//!     b = 3:  ceiling 10    reached  ->  rate 10^(1/2) = 3.162  (AHS)
//!     b = 4:  ceiling 35    ?
//! ```
//!
//! If `b = 4` reached its ceiling the rate would be `35^(1/3) = 3.27`,
//! above AHS. It does not.
use sunflower_formal::intersecting::{iota, verify};

fn choose(n: u64, k: u64) -> u64 {
    (0..k).fold(1, |a, i| a * (n - i) / (i + 1))
}

fn main() {
    println!("  b   2b   ceiling C(2b,b)/2   iota(b,2b)   rate      reached?  transversal?");
    for b in 2u32..=4 {
        let ceiling = choose(2 * b as u64, b as u64) / 2;
        let t = std::time::Instant::now();
        let (n, fam, done) = iota(2 * b, b, 400_000_000_000, 0);
        verify(&fam, b, true).expect("bad witness");
        let full: u32 = (1u32 << (2 * b)) - 1;
        let transversal = !fam.is_empty() && fam.iter().all(|a| !fam.contains(&(full ^ a)));
        let rate = (n as f64).powf(1.0 / (b as f64 - 1.0));
        println!(
            "  {b}   {:>2}      {ceiling:>4}            {n:>4}     {rate:.4}    {:<6}    {transversal}  ({}, {:.0}s)",
            2 * b,
            if n as u64 == ceiling { "YES" } else { "no" },
            if done { "exhaustive" } else { "LOWER BOUND ONLY" },
            t.elapsed().as_secs_f64()
        );
    }
    println!();
    println!("ceiling rates: b=2 -> {:.4}, b=3 -> {:.4}, b=4 -> {:.4}",
             3f64, 10f64.powf(0.5), 35f64.powf(1.0 / 3.0));
}
