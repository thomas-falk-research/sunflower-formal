//! Dump the extremal `iota(b,g)` witnesses themselves, one line each.
//!
//! Separated from `iota_structure` because recomputing `iota(4,9)` takes
//! nine minutes and the structural report should not pay that on every
//! run. The lines this prints are pasted into `iota_structure`'s witness
//! table, where each one is re-verified by `intersecting::verify` before
//! anything is computed from it.

use sunflower_formal::{intersecting, structure};

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let max_b: u32 = args
        .iter()
        .position(|a| a == "--max-b")
        .and_then(|i| args.get(i + 1))
        .and_then(|s| s.parse().ok())
        .unwrap_or(4);
    let max_g: u32 = args
        .iter()
        .position(|a| a == "--max-g")
        .and_then(|i| args.get(i + 1))
        .and_then(|s| s.parse().ok())
        .unwrap_or(9);
    let budget: u64 = 4_000_000_000;

    for b in 1..=max_b {
        let mut seed = 0usize;
        for g in b..=max_g {
            let t0 = std::time::Instant::now();
            let (n, w, done) = intersecting::iota(g, b, budget, seed);
            let dt = t0.elapsed().as_secs_f64();
            if n > seed {
                seed = n;
                let check = intersecting::verify(&w, b, true);
                println!(
                    "b={b} g={g} n={n} exhaustive={done} time={dt:.1}s verify={} witness={:?} coq={}",
                    match check {
                        Ok(()) => "OK".to_string(),
                        Err(e) => format!("FAIL:{e}"),
                    },
                    w,
                    structure::fmt_coq(&w)
                );
            } else {
                println!("b={b} g={g} n={n} exhaustive={done} time={dt:.1}s (no improvement)");
            }
        }
    }
}
