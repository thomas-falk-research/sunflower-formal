//! Exhaustive `r*(m,3)` search by depth-first enumeration.
//!
//!     cargo run --release --example rstar_dfs -- <m> <r> <g_lo> <g_hi> [nu] [node_limit]

use sunflower_formal::rstar::{dfs, min_ground, degree_ceiling, Outcome, Question};
use sunflower_formal::spread::mask_to_set;

fn main() {
    let a: Vec<String> = std::env::args().skip(1).collect();
    if a.len() < 4 {
        eprintln!("usage: rstar_dfs <m> <r> <g_lo> <g_hi> [nu=2] [node_limit]");
        std::process::exit(2);
    }
    let m: u32 = a[0].parse().unwrap();
    let r: u64 = a[1].parse().unwrap();
    let lo: u32 = a[2].parse().unwrap();
    let hi: u32 = a[3].parse().unwrap();
    let nu: usize = a.get(4).and_then(|s| s.parse().ok()).unwrap_or(2);
    let limit: u64 = a.get(5).and_then(|s| s.parse().ok()).unwrap_or(u64::MAX);

    println!("# m={m} r={r} target={} min_ground={}", (r.pow(m)) + 1, min_ground(m, r));
    for g in lo..=hi {
        let mut q = Question::new(m, r, g);
        q.nu = nu;
        println!(
            "# ground {g}: degree ceiling {} (target {})",
            degree_ceiling(m, r, g),
            q.target()
        );
        let rep = dfs(&q, limit);
        println!("{}", rep.line());
        if let Outcome::Counterexample(f) = &rep.outcome {
            for &c in f {
                println!("  {:?}", mask_to_set(c));
            }
            println!("masks: {:?}", f);
            return;
        }
        // Below the target the run still found *something*, and a
        // truncated run reports no other object at all. Dump it: a size
        // with nothing behind it cannot be checked by anyone.
        if !rep.largest_family.is_empty() {
            println!("  largest family found ({} members):", rep.largest);
            for &c in &rep.largest_family {
                println!("    {:?}", mask_to_set(c));
            }
            println!("  masks: {:?}", rep.largest_family);
        }
        use std::io::Write;
        std::io::stdout().flush().ok();
    }
}
