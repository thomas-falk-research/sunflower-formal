//! The decision questions that would move a record, asked directly.
//!
//!     record_hunt <b> <target> <g_lo> <g_hi> [budget]
//!
//! Unrestricted pool, so this is the strongest available search rather
//! than a hypothesis about shape. `search_orbits` with singleton orbits
//! is a max-clique branch and bound with the ternary condition checked
//! incrementally; its bound is sharp for a *decision*, which is why the
//! question is posed as "does a family of `target` members exist" and
//! never as "what is the maximum".
use std::io::Write;
use sunflower_formal::genprog;

fn main() {
    let a: Vec<String> = std::env::args().skip(1).collect();
    let b: u32 = a[0].parse().unwrap();
    let target: usize = a[1].parse().unwrap();
    let lo: u32 = a[2].parse().unwrap();
    let hi: u32 = a[3].parse().unwrap();
    let budget: u64 = a.get(4).and_then(|s| s.parse().ok()).unwrap_or(u64::MAX);
    for g in lo..=hi {
        let ceil = genprog::size_ceiling(b as u64, g as u64);
        if ceil < target as u64 {
            println!("  b={b} g={g}: ceiling {ceil} < {target} -- impossible, no search");
            let _ = std::io::stdout().flush();
            continue;
        }
        let pool = genprog::all_blocks(g, b);
        let s = genprog::evaluate(&pool, target, budget);
        println!(
            "  b={b} g={g} ceiling={ceil} pool={} -> {} ({} nodes, {:.0}s)",
            s.pool,
            if s.best >= target {
                format!("FOUND {} : {:02x?}", s.best, s.family)
            } else if s.exhaustive {
                format!("no family of {target} exists on {g} points")
            } else {
                "undecided (budget)".into()
            },
            s.nodes,
            s.seconds
        );
        let _ = std::io::stdout().flush();
    }
}
