//! `iota(5)`: walk the target up with SAT, on the grounds the counting
//! bound says can hold a record.
//!
//! §9 measured what SAT is for here: **transformative on the witness
//! side** (`N(3,10) >= 16` in 0.02 s against a search that never
//! finished) and no free win on the intersecting UNSAT side. This driver
//! only ever asks the witness question — "is there a family of at least
//! `t`" — and walks `t` up until the solver stops finding one.
//!
//! The grounds are chosen by the link counting bound rather than by
//! taste. Sunflower-freeness caps a `(b-2)`-set at degree 6, because its
//! link is a graph with `Δ <= 2` and `ν <= 2` and so is at most two
//! disjoint triangles. At `b = 5` that gives `|F| <= 0.6 * C(n,3)`:
//!
//! ```text
//!   n      10    11    12    13    14    15
//!   bound  72    99   132   171   218   273
//! ```
//!
//! So `iota(5) >= 101` is **impossible below twelve points**, and the
//! previous b = 5 SAT row (§9, `iota(5,10) >= 42`) was run at a ground
//! that provably cannot hold a record. Twelve is the first that can.

use std::io::Write;

use sunflower_formal::intersecting;
use sunflower_formal::sat::{decide_iota, Solver, Verdict};

fn line(s: &str) {
    println!("{s}");
    let _ = std::io::stdout().flush();
}

fn link_bound(b: u64, n: u64) -> u64 {
    fn c(n: u64, k: u64) -> u64 {
        if k > n {
            return 0;
        }
        let mut r: u64 = 1;
        for i in 0..k {
            r = r * (n - i) / (i + 1);
        }
        r
    }
    6 * c(n, b - 2) / c(b, 2)
}

fn main() {
    let a: Vec<String> = std::env::args().skip(1).collect();
    let b: u32 = a.first().and_then(|s| s.parse().ok()).unwrap_or(5);
    let lo: u32 = a.get(1).and_then(|s| s.parse().ok()).unwrap_or(12);
    let hi: u32 = a.get(2).and_then(|s| s.parse().ok()).unwrap_or(13);
    let start: usize = a.get(3).and_then(|s| s.parse().ok()).unwrap_or(79);
    let seconds: u64 = a.get(4).and_then(|s| s.parse().ok()).unwrap_or(900);

    line(&format!(
        "=== iota({b}) by SAT, grounds {lo}..{hi}, walking the target up from {start} ==="
    ));
    let mut best = 0usize;
    let mut best_family: Vec<u32> = Vec::new();
    for g in lo..=hi {
        let bound = link_bound(b as u64, g as u64);
        line(&format!("--- ground {g}: link counting bound {bound} ---"));
        let mut t = start;
        loop {
            if t as u64 > bound {
                line(&format!("  target {t} exceeds the counting bound, stop"));
                break;
            }
            let started = std::time::Instant::now();
            let v = decide_iota(g, b, t, None, Solver::Cadical, seconds).expect("solver");
            let dt = started.elapsed().as_secs_f64();
            match v {
                Verdict::Sat(f) => {
                    intersecting::verify(&f, b, true).expect("model failed verification");
                    line(&format!("  >= {t}: SAT in {dt:.1}s ({} members)", f.len()));
                    if f.len() > best {
                        best = f.len();
                        best_family = f.clone();
                        line(&format!("  BEST SO FAR {best}: {best_family:02x?}"));
                    }
                    t = f.len() + 1;
                }
                Verdict::Unsat => {
                    line(&format!("  >= {t}: UNSAT in {dt:.1}s -- ground {g} caps at {}", t - 1));
                    break;
                }
                Verdict::Unknown => {
                    line(&format!("  >= {t}: undecided in {dt:.1}s, stop this ground"));
                    break;
                }
            }
        }
    }
    line(&format!("=== best found: {best} (record to beat: 78; 1972 threshold: 101) ==="));
    if !best_family.is_empty() {
        line(&format!("family: {best_family:02x?}"));
    }
}
