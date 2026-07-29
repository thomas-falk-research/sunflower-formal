//! One `iota` query: `iota_query <b> <ground> [target]`.
//!
//! With a target, decides whether `iota(b, ground) >= target`. Without
//! one, computes the maximum. The decision form is much cheaper when the
//! answer is no, which is the common case near the top of the range.
use std::io::Write;
use sunflower_formal::intersecting::{iota, iota_decide, verify};

fn choose(n: u64, k: u64) -> u64 {
    (0..k).fold(1, |a, i| a * (n - i) / (i + 1))
}

fn main() {
    let mut args = std::env::args().skip(1);
    let b: u32 = args.next().and_then(|s| s.parse().ok()).unwrap_or(5);
    let ground: u32 = args.next().and_then(|s| s.parse().ok()).unwrap_or(2 * b);
    let target: Option<usize> = args.next().and_then(|s| s.parse().ok());
    let budget: u64 = 20_000_000_000_000;

    // The ceiling only applies at ground exactly 2b, where disjoint
    // means complementary.
    if ground == 2 * b {
        println!(
            "b = {b}, ground {ground}: ceiling C(2b,b)/2 = {}",
            choose(2 * b as u64, b as u64) / 2
        );
    }
    let ahs = 10f64.powf((b as f64 - 1.0) / 2.0);
    println!("  AHS is beaten at iota({b}) >= {:.0}", ahs.ceil());
    std::io::stdout().flush().ok();

    let t = std::time::Instant::now();
    match target {
        Some(tg) => {
            let (reached, fam, done) = iota_decide(ground, b, tg, budget);
            let secs = t.elapsed().as_secs_f64();
            if reached {
                verify(&fam, b, true).expect("witness invalid");
                println!("  FOUND {} >= {tg}  ({secs:.0}s)", fam.len());
            } else if done {
                println!("  no family of {tg}+ -- exhaustive  ({secs:.0}s)");
            } else {
                println!("  inconclusive: budget exhausted  ({secs:.0}s)");
            }
        }
        None => {
            let (n, fam, done) = iota(ground, b, budget, 0);
            let secs = t.elapsed().as_secs_f64();
            if !fam.is_empty() {
                verify(&fam, b, true).expect("witness invalid");
            }
            let rate = (n as f64).powf(1.0 / (b as f64 - 1.0));
            println!(
                "  iota({b},{ground}) {} {n}   rate {rate:.4}  ({secs:.0}s)",
                if done { "=" } else { ">=" }
            );
        }
    }
    std::io::stdout().flush().ok();
}
