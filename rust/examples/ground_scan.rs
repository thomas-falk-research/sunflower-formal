//! One-off: how N(m, g) grows with the ground set g.
//!
//! Not a CI test -- the searches at m = 3 are minutes each and the last
//! ones do not finish. Run with `cargo run --release --example ground_scan`.
use sunflower_formal::ground::{max_sunflower_free, verify};

fn main() {
    let budget: u64 = std::env::args()
        .nth(1)
        .and_then(|s| s.parse().ok())
        .unwrap_or(4_000_000_000);
    println!("  m   g    N(m,g)   exhaustive");
    for m in 1u32..=3 {
        for g in m..=12 {
            let t = std::time::Instant::now();
            let (n, fam, done) = max_sunflower_free(g, m, budget);
            verify(&fam, m).expect("witness is not sunflower-free");
            println!(
                "  {m}   {g}    {n:>6}   {:<24} ({:.1}s)",
                if done { "yes" } else { "NO (lower bound only)" },
                t.elapsed().as_secs_f64()
            );
            // Deliberately no early exit: a budget-limited run still gives
            // a valid *lower* bound on N(m,g), and whether the sequence is
            // still climbing is the whole question.
            let _ = done;
        }
    }
}
