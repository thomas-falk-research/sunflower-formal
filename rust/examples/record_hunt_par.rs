//! The record decision questions, root-split across cores and resumable.
//!
//!     record_hunt_par <b> <target> <g_lo> <g_hi> [budget] [threads] [ckpt_dir]
//!
//! Same question as `record_hunt` and the same answer — `orbit::verify`
//! re-checks anything found — but the search is
//! `orbit::search_orbits_parallel`, so it uses every core and writes its
//! frontier as it goes. With a checkpoint directory, a run killed by a
//! container restart resumes from the root subproblems it had finished
//! instead of starting over. `docs/roadmap.md` §23.3 records a 2h28m
//! attempt at `iota(4,10) >= 28` that was killed twice without a verdict;
//! this is the shape that attempt needed.
//!
//! One question at a time, as `search_orbits` requires: its bound is
//! sharp for a decision and its `best` is not a maximum.
use std::io::Write;
use sunflower_formal::{genprog, orbit};

fn main() {
    let a: Vec<String> = std::env::args().skip(1).collect();
    if a.len() < 4 {
        eprintln!("usage: record_hunt_par <b> <target> <g_lo> <g_hi> [budget] [threads] [ckpt_dir]");
        std::process::exit(2);
    }
    let b: u32 = a[0].parse().unwrap();
    let target: usize = a[1].parse().unwrap();
    let lo: u32 = a[2].parse().unwrap();
    let hi: u32 = a[3].parse().unwrap();
    let budget: u64 = a.get(4).and_then(|s| s.parse().ok()).unwrap_or(u64::MAX);
    let threads: usize = a
        .get(5)
        .and_then(|s| s.parse().ok())
        .unwrap_or_else(|| std::thread::available_parallelism().map(|n| n.get()).unwrap_or(4));
    let ckpt_dir = a.get(6).cloned();

    for g in lo..=hi {
        // The counting precheck first: an instance the ceiling forbids is
        // answered in zero nodes, not in six minutes of search.
        let ceil = genprog::size_ceiling(b as u64, g as u64);
        if ceil < target as u64 {
            println!("  b={b} g={g}: ceiling {ceil} < {target} -- impossible, no search");
            let _ = std::io::stdout().flush();
            continue;
        }
        let pool = genprog::all_blocks(g, b);
        let orbits: Vec<Vec<u64>> = pool.blocks.iter().map(|&x| vec![x]).collect();
        let path = ckpt_dir
            .as_ref()
            .map(|d| std::path::PathBuf::from(d).join(format!("ck-b{b}-t{target}-g{g}.txt")));
        if let Some(p) = &path {
            if let Some(parent) = p.parent() {
                let _ = std::fs::create_dir_all(parent);
            }
            let resumed = std::fs::read_to_string(p)
                .map(|s| s.lines().filter(|l| !l.trim().is_empty()).count())
                .unwrap_or(0);
            if resumed > 0 {
                println!("  b={b} g={g}: resuming, {resumed} root subproblems already done");
            }
        }

        let t0 = std::time::Instant::now();
        let r = orbit::search_orbits_parallel(
            &orbits,
            target,
            true,
            budget,
            threads,
            path.as_deref(),
        );
        let secs = t0.elapsed().as_secs_f64();

        let verdict = if r.best >= target {
            orbit::verify(&r.best_family, b, true).expect("a search produced a family that does not verify");
            format!("FOUND {} : {:02x?}", r.best, r.best_family)
        } else if r.exhaustive {
            format!("no intersecting sunflower-free family of {target} exists on {g} points")
        } else {
            format!("undecided (budget {budget} nodes spent)")
        };
        println!(
            "  b={b} g={g} ceiling={ceil} pool={} threads={threads} -> {verdict} ({} nodes, {secs:.0}s)",
            pool.blocks.len(),
            r.nodes
        );
        let _ = std::io::stdout().flush();
    }
}
