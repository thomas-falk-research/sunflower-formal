//! One SAT query, or a ladder of them, printed as each rung lands.
//!
//! Designed for an environment that reclaims long-running processes:
//! every decision is printed and flushed the moment it is made, so a run
//! that is killed part-way still reports everything it decided.
//!
//! ```text
//!   cargo run --release --example sat_run -- iota   4 10 25 34
//!   cargo run --release --example sat_run -- iota   4 10 25 34 --cap 14
//!   cargo run --release --example sat_run -- general 3 10 13 21
//!   cargo run --release --example sat_run -- iota   5 11 90 110 --solver cryptominisat5
//! ```
//!
//! Arguments: `<iota|general> <b> <ground> <lo> <hi>`, then optional
//! `--cap N` (the degree cap `N(b-1, ground-1)`), `--solver NAME`,
//! `--seconds N` (per-query limit, 0 for none), `--agreed` (require two
//! independent solvers to agree before believing anything).
//!
//! The ladder runs upwards from `lo`: each rung asks "is there a family
//! of at least `t` members?". The first UNSAT settles the exact value.
//! Upwards is deliberate — a SAT rung is cheap and produces a witness
//! that is re-verified independently, so the expensive UNSAT is asked
//! only once.

use std::io::Write;
use std::time::Instant;

use sunflower_formal::intersecting::verify;
use sunflower_formal::sat::*;

fn solver_by_name(name: &str) -> Solver {
    match name {
        "cadical" => Solver::Cadical,
        "cryptominisat5" | "cms" => Solver::CryptoMiniSat,
        "picosat" => Solver::PicoSat,
        "minisat" => Solver::Minisat,
        other => panic!("unknown solver {other}"),
    }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.len() < 5 {
        eprintln!("usage: sat_run <iota|general> <b> <ground> <lo> <hi> [--cap N] [--solver S] [--seconds N] [--agreed]");
        std::process::exit(2);
    }
    let mode = args[0].clone();
    let b: u32 = args[1].parse().unwrap();
    let ground: u32 = args[2].parse().unwrap();
    let lo: usize = args[3].parse().unwrap();
    let hi: usize = args[4].parse().unwrap();

    let mut cap: Option<usize> = None;
    let mut solver = Solver::Cadical;
    let mut second = Solver::CryptoMiniSat;
    let mut seconds: u64 = 0;
    let mut agreed = false;
    let mut i = 5;
    while i < args.len() {
        match args[i].as_str() {
            "--cap" => {
                cap = Some(args[i + 1].parse().unwrap());
                i += 2;
            }
            "--solver" => {
                solver = solver_by_name(&args[i + 1]);
                i += 2;
            }
            "--second" => {
                second = solver_by_name(&args[i + 1]);
                i += 2;
            }
            "--seconds" => {
                seconds = args[i + 1].parse().unwrap();
                i += 2;
            }
            "--agreed" => {
                agreed = true;
                i += 1;
            }
            other => panic!("unknown flag {other}"),
        }
    }

    let intersecting = match mode.as_str() {
        "iota" => true,
        "general" => false,
        other => panic!("mode must be iota or general, not {other}"),
    };

    println!(
        "# {mode}({b}, {ground}), rungs {lo}..={hi}, solver {}{}{}{}",
        solver.binary(),
        if agreed {
            format!(" + {}", second.binary())
        } else {
            String::new()
        },
        cap.map(|c| format!(", degree cap {c}")).unwrap_or_default(),
        if seconds > 0 {
            format!(", {seconds}s per query")
        } else {
            String::new()
        },
    );
    let _ = std::io::stdout().flush();

    let mut best_sat: Option<usize> = None;
    for t in lo..=hi {
        let t0 = Instant::now();
        // Instance sizes, printed once per rung so a killed run still
        // says how big the question was.
        let probe = encode(
            ground,
            b,
            t,
            intersecting,
            SecondMember::Free,
            cap,
        );
        let verdict = if agreed {
            // The orbit split is only sound for intersecting families,
            // so the agreed path uses the single free instance.
            solve_agreed(&probe, solver, second, seconds)
        } else if intersecting {
            decide_iota(ground, b, t, cap, solver, seconds)
        } else {
            decide_general(ground, b, t, cap, solver, seconds)
        };
        let dt = t0.elapsed().as_secs_f64();
        match verdict {
            Ok(Verdict::Sat(fam)) => {
                verify(&fam, b, intersecting).expect("independent re-verification failed");
                best_sat = Some(t);
                println!(
                    "  >= {t:3}  SAT      {dt:9.2}s   vars {:6} clauses {:8}  witness {} members",
                    probe.cnf.nvars,
                    probe.cnf.clauses.len(),
                    fam.len()
                );
                if t == hi {
                    println!("  -- ladder exhausted at {t}; the value is at least {t}");
                }
            }
            Ok(Verdict::Unsat) => {
                println!(
                    "  >= {t:3}  UNSAT    {dt:9.2}s   vars {:6} clauses {:8}",
                    probe.cnf.nvars,
                    probe.cnf.clauses.len()
                );
                match best_sat {
                    Some(v) => println!("  == {mode}({b},{ground}) = {v}   (exhaustive: UNSAT at {t})"),
                    None => println!(
                        "  == {mode}({b},{ground}) < {t}   (no SAT rung was reached in this run)"
                    ),
                }
                let _ = std::io::stdout().flush();
                return;
            }
            Ok(Verdict::Unknown) => {
                println!("  >= {t:3}  UNKNOWN  {dt:9.2}s   (timed out; nothing decided at this rung)");
                let _ = std::io::stdout().flush();
                return;
            }
            Err(e) => {
                println!("  >= {t:3}  ERROR    {e}");
                let _ = std::io::stdout().flush();
                return;
            }
        }
        let _ = std::io::stdout().flush();
    }
}
