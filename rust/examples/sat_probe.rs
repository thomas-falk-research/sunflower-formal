//! Does the SAT encoding reproduce the values the branch-and-bound
//! already decided, and how fast?
//!
//! Prints, and asserts nothing. `tests/sat_encoding.rs` pins the
//! agreement; this is the timing run.

use std::time::Instant;

use sunflower_formal::sat::*;

fn iota_exact(ground: u32, b: u32, lo: usize, hi: usize, cap: Option<usize>, s: Solver) -> String {
    // Walk up from `lo`: the largest target that is SAT.
    let mut best = lo;
    for t in (lo + 1)..=hi {
        match decide_iota(ground, b, t, cap, s, 60) {
            Ok(Verdict::Sat(_)) => best = t,
            Ok(Verdict::Unsat) => return format!("{best}"),
            _ => return format!(">={best} (unknown at {t})"),
        }
    }
    format!(">={best}")
}

fn main() {
    let s = Solver::Cadical;
    println!("solver: {} available={}", s.binary(), s.available());

    println!();
    println!("== iota(b, g), against the known row ==");
    println!("   b   g   known   sat      seconds   vars   clauses");
    for (b, g, known) in [
        (2u32, 3u32, 3usize), (2, 5, 3), (2, 8, 3),
        (3, 4, 4), (3, 5, 6), (3, 6, 10), (3, 7, 10), (3, 9, 10), (3, 12, 10),
        (4, 5, 5), (4, 6, 9), (4, 7, 15), (4, 8, 24), (4, 9, 27),
    ] {
        let inst = encode(g, b, known, true, SecondMember::Free, None);
        let t0 = Instant::now();
        let got = iota_exact(g, b, 1, known + 8, None, s);
        println!(
            "   {b}  {g:2}   {known:5}   {got:6}   {:8.2}   {:5}  {:7}",
            t0.elapsed().as_secs_f64(),
            inst.cnf.nvars,
            inst.cnf.clauses.len()
        );
    }

    println!();
    println!("== N(m, g), the general row ==");
    println!("   m   g   known   sat      seconds");
    for (m, g, known) in [
        (2u32, 6u32, 6usize), (2, 8, 6),
        (3, 5, 6), (3, 6, 10), (3, 7, 12), (3, 8, 12), (3, 9, 14),
    ] {
        let t0 = Instant::now();
        let mut best = 1;
        let mut verdict = String::new();
        for t in 2..=(known + 6) {
            match decide_general(g, m, t, None, s, 60) {
                Ok(Verdict::Sat(_)) => best = t,
                Ok(Verdict::Unsat) => {
                    verdict = format!("{best}");
                    break;
                }
                _ => {
                    verdict = format!(">={best} unknown");
                    break;
                }
            }
        }
        if verdict.is_empty() {
            verdict = format!(">={best}");
        }
        println!("   {m}  {g:2}   {known:5}   {verdict:6}   {:8.2}", t0.elapsed().as_secs_f64());
    }
}
