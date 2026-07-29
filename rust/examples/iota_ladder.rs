//! Does `iota(4)` climb from 27 at ground 10?
//!
//! `iota(4,9) = 27`. The ground-10 run answered only "is it 32 or more?"
//! (no, 4437s) — the value that would beat Abbott–Hanson–Sauer. The
//! question `IotaGroundBounded` turns on is different and finer: does the
//! row *move at all* past ground 9? If `iota(4,10) = 27` the intersecting
//! row plateaus at `g = 9 = 2.25b`, and the hypothesis
//! `coq/SliceRank.v:IotaGroundBounded` has three plateaus behind it
//! instead of two.
//!
//! Asked as a descending ladder rather than one query, because the cost
//! runs the wrong way. Seeding the incumbent at `target - 1` is what
//! prunes, so a *lower* target searches a *larger* tree: "is it >= 28?"
//! is strictly harder than "is it >= 32?", which already took 74 minutes.
//! Each rung is printed and flushed as it lands, so a run that is killed
//! part-way still reports everything it decided.
//!
//! Usage: `cargo run --release --example iota_ladder [ground] [hi] [lo] [budget]`

use std::io::Write;

use sunflower_formal::intersecting::{iota_decide, verify};

fn main() {
    let mut args = std::env::args().skip(1);
    let ground: u32 = args.next().and_then(|s| s.parse().ok()).unwrap_or(10);
    let hi: usize = args.next().and_then(|s| s.parse().ok()).unwrap_or(31);
    let lo: usize = args.next().and_then(|s| s.parse().ok()).unwrap_or(28);
    let budget: u64 = args
        .next()
        .and_then(|s| s.parse().ok())
        .unwrap_or(20_000_000_000_000);

    println!("b = 4, ground {ground}: is iota(4,{ground}) >= t, for t = {hi} down to {lo}?");
    println!("  iota(4,9) = 27, so a NO at t = 28 means the row plateaus at ground 9.");
    println!("  Descending: each rung is strictly harder than the one above it.");
    std::io::stdout().flush().ok();

    let start = std::time::Instant::now();
    for target in (lo..=hi).rev() {
        let t = std::time::Instant::now();
        let (reached, fam, done) = iota_decide(ground, 4, target, budget);
        let secs = t.elapsed().as_secs_f64();
        if reached {
            verify(&fam, 4, true).expect("witness invalid");
            println!(
                "  t = {target:>2}: FOUND {} members ({secs:.0}s) -- the row climbs",
                fam.len()
            );
            println!(
                "    {:?}",
                fam.iter()
                    .map(|m| (0..16u32).filter(|x| m >> x & 1 == 1).collect::<Vec<_>>())
                    .collect::<Vec<_>>()
            );
            std::io::stdout().flush().ok();
            // A yes at t settles every lower rung too.
            println!("  (a family of {target} settles t < {target}; stopping)");
            break;
        } else if done {
            println!("  t = {target:>2}: NO -- exhaustive ({secs:.0}s), so iota(4,{ground}) <= {}", target - 1);
        } else {
            println!("  t = {target:>2}: inconclusive, budget exhausted ({secs:.0}s) -- STOP");
            std::io::stdout().flush().ok();
            break;
        }
        std::io::stdout().flush().ok();
    }
    println!("total {:.0}s", start.elapsed().as_secs_f64());
    std::io::stdout().flush().ok();
}
