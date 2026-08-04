//! Run the generator-program search.
//!
//!     cargo run --release --example genprog_run -- <b> <target> [budget]

use std::io::Write;
use sunflower_formal::genprog::{self, Pool};

fn line(s: &str) {
    println!("{s}");
    let _ = std::io::stdout().flush();
}

fn main() {
    let a: Vec<String> = std::env::args().skip(1).collect();
    let b: u32 = a.first().and_then(|s| s.parse().ok()).unwrap_or(5);
    let target: usize = a.get(1).and_then(|s| s.parse().ok()).unwrap_or(101);
    let budget: u64 = a.get(2).and_then(|s| s.parse().ok()).unwrap_or(30_000_000);

    line("=== the counting ceiling, by ground ===");
    for n in b as u64..=20 {
        line(&format!(
            "  n={n:2}  (b-1)-bound {:6}  (b-2)-bound {:6}  ceiling {:6}",
            genprog::top_link_bound(b as u64, n),
            genprog::link_bound(b as u64, n),
            genprog::size_ceiling(b as u64, n)
        ));
    }
    line(&format!(
        "  least ground that could hold {target}: {}",
        genprog::least_ground(b as u64, target as u64)
    ));

    let mut pools: Vec<Pool> = Vec::new();
    // the control: no hypothesis at all, on the grounds small enough to search
    for g in b..=(2 * b + 1).min(12) {
        pools.push(genprog::all_blocks(g, b));
    }
    // transversal grids with the right uniformity
    for m in 2..=4u32 {
        if b * m <= 24 {
            pools.push(genprog::transversals(b, m));
            for q in 2..=4u32 {
                for c in 0..q {
                    pools.push(genprog::twisted_transversals(b, m, q, c));
                }
            }
        }
    }
    // complementary selections on 2b points
    for wm in 2..=5u32 {
        for r in 0..wm {
            pools.push(genprog::complementary_half(b, wm, r));
        }
    }
    // the baselines and the tau = b pools, on the grounds that can hold a record
    let lo = genprog::least_ground(b as u64, target as u64) as u32;
    for g in lo..=(lo + 2).min(16) {
        pools.push(genprog::star(g, b));
        for t in 2..=b {
            pools.push(genprog::cover_pool(g, b, t, 1));
            if t >= 2 {
                pools.push(genprog::cover_pool(g, b, t, 2));
            }
        }
    }

    line("");
    line(&format!(
        "=== pools, asked the decision question: does this one hold {target}? ==="
    ));
    line("   (best=0 means the pool is too small for the bound to even branch)");
    let mut best = 0usize;
    let mut best_fam: Vec<u64> = Vec::new();
    let mut best_name = String::new();
    for p in &pools {
        if p.blocks.is_empty() || p.ground > 24 {
            continue;
        }
        let s = genprog::evaluate(p, target, budget);
        line(&format!("  {}", s.line()));
        if s.best > best {
            best = s.best;
            best_fam = s.family.clone();
            best_name = s.name.clone();
        }
    }
    line("");
    line(&format!("=== best across all generators: {best} from `{best_name}` ==="));
    if !best_fam.is_empty() {
        line(&format!("family: {best_fam:02x?}"));
    }
}
