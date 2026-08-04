//! Kramer–Mesner at `b = 5`, **intersecting**, on the grounds §13.3 never
//! reached.
//!
//! §13.3 ran three rows and found nothing: `b = 4` intersecting on
//! grounds 11..16, `b = 3` general on 16..22, and `b = 5` *general* on
//! 15..20. Its diagnosis is that an orbit is usable only if it is itself
//! sunflower-free, and an orbit of a group acting on a ground set much
//! larger than `3b` almost always contains three pairwise disjoint
//! translates — so on large grounds there is nothing to search. It notes
//! that at `b = 5, g = 15`, "where `3b = g` exactly, most of them do"
//! survive.
//!
//! Two facts were never put together.
//!
//! * **`iota(5) >= 101` needs only twelve points.** Sunflower-freeness
//!   caps the degree of a `(b-2)`-set at 6 (the link is a graph with
//!   `Δ <= 2` and `ν <= 2`, so at most two disjoint triangles), giving
//!   `|F| <= (6 / C(b,2)) * C(n, b-2)`. At `b = 5` that is
//!   `0.6 * C(n,3)`, which is 99 at `n = 11` and 132 at `n = 12`.
//! * **Below `3b` the orbits survive.** Grounds 12, 13 and 14 are below
//!   15, so the reason §13.3's rows were empty does not apply there.
//!
//! Nobody looked at grounds 12..14 for `b = 5` intersecting because
//! nobody had the first fact, and the driver in `kramer_mesner.rs` starts
//! its `b = 5` row at 15.
//!
//! Usage: `cargo run --release --example km_five -- [lo] [hi] [budget]`

use std::io::Write;

use sunflower_formal::orbit;

fn line(s: &str) {
    println!("{s}");
    let _ = std::io::stdout().flush();
}

/// `|F| <= (6 / C(b,2)) * C(n, b-2)`, the sharper of the two link
/// counting bounds at every `n` that matters here.
fn link_bound(b: u32, n: u32) -> u64 {
    fn c(n: u32, k: u32) -> u64 {
        if k > n {
            return 0;
        }
        let mut r: u64 = 1;
        for i in 0..k as u64 {
            r = r * (n as u64 - i) / (i + 1);
        }
        r
    }
    // deg of a (b-2)-set is at most 6; each member contains C(b,2) of them
    6 * c(n, b - 2) / c(b, 2)
}

fn main() {
    let a: Vec<String> = std::env::args().skip(1).collect();
    let lo: u32 = a.first().and_then(|s| s.parse().ok()).unwrap_or(12);
    let hi: u32 = a.get(1).and_then(|s| s.parse().ok()).unwrap_or(14);
    let budget: u64 = a.get(2).and_then(|s| s.parse().ok()).unwrap_or(40_000_000);

    let b = 5u32;
    let target = 101usize;
    line("=== b = 5, intersecting, target 101 -- the grounds 13.3 never reached ===");
    line("  the counting bound 0.6*C(n,3), and the best any union of orbits reaches");
    line("   g   bound   group                        orbits  usable   best   exhausted");

    let mut global_best = 0usize;
    let mut global_family: Vec<u64> = Vec::new();
    for g in lo..=hi {
        let bound = link_bound(b, g);
        if bound < target as u64 {
            line(&format!("  {g:2}  {bound:5}   -- below the target, no family fits --"));
            continue;
        }
        for (name, gens) in orbit::standard_groups(g) {
            let Some(group) = orbit::group_closure(g, &gens, 200_000) else {
                continue;
            };
            let orbs = orbit::orbits_on_subsets(g, b, &group);
            // An orbit is usable only if it is itself intersecting and
            // sunflower-free -- 13.3's observation, made explicit.
            let usable: Vec<Vec<u64>> = orbs
                .iter()
                .filter(|o| orbit::verify(o, b, true).is_ok())
                .cloned()
                .collect();
            let res = orbit::search_orbits(&usable, target, true, budget);
            if res.best > global_best {
                global_best = res.best;
                global_family = res.best_family.clone();
            }
            line(&format!(
                "  {g:2}  {bound:5}   {name:28} {:6}  {:6}  {:5}   {}",
                orbs.len(),
                usable.len(),
                res.best,
                if res.exhaustive { "yes" } else { "no" }
            ));
            if res.best >= target {
                line("  *** TARGET REACHED ***");
                line(&format!("  family: {:?}", res.best_family));
                return;
            }
        }
    }
    line(&format!("=== best over the whole sweep: {global_best} ==="));
    if global_best >= 78 {
        line(&format!("  family: {global_family:?}"));
    }
}
