//! `iota(b,g) >= t?` under degree-ordered symmetry breaking, split into
//! cubes on `deg(0)` and run one cube per core.
//!
//! ```text
//!   cargo run --release --example iota_sym -- 4 10 32
//!   cargo run --release --example iota_sym -- 4 11 32 --ladder --threads 4
//! ```
//!
//! Arguments: `<b> <ground> <target>`, then optional `--seconds N` (per
//! cube, 0 for none), `--threads T`, `--kmax K`, `--solver NAME`,
//! `--seqprefix N` (fix only the first `N` degrees when re-splitting, so
//! the granularity of the second phase is tunable: at `g = 11, b = 4,
//! deg(0) = 13` the split is 6 cubes at `N = 2`, 27 at 3, 167 at 4 and
//! 1939 at 11 — and 1939 sub-cubes each still costing minutes is a worse
//! trade than a few dozen that are merely hard),
//! `--checkpoint PATH` (append each degree-sequence sub-cube's verdict as
//! it lands, and skip the ones already recorded there — what makes a cube
//! with thousands of sub-cubes survivable across restarts, and what lets
//! a cheap pass harvest the easy ones before an expensive pass re-runs
//! only the stragglers),
//! `--plain` (drop the symmetry constraints, keeping the cube split — the
//! control that says what the constraints are worth), and `--ladder`.
//!
//! # The ladder
//!
//! `--ladder` asks the question one support size at a time: for each `s`
//! from `b` to `ground`, "is there such a family whose support is
//! **exactly** `[s]`?". Any family on at most `ground` points has a
//! support of some size `s <= ground` and relabels onto `[s]`, so the
//! rungs cover the question and the run is UNSAT exactly when every rung
//! is. Each rung is a strictly smaller instance than the flat question at
//! `ground`, and — this is the point — it has far less symmetry, because
//! unused points are interchangeable and a rung has none.
//!
//! Every cube's verdict and wall time is printed and flushed as it lands,
//! so a run reclaimed part-way still reports what it decided. The summary
//! line distinguishes the three outcomes that matter:
//!
//! ```text
//!   SAT     a family exists; it has already been re-verified
//!   UNSAT   every cube came back UNSAT -- exhausted
//!   UNKNOWN at least one cube hit its limit -- the budget is the result
//! ```

use std::collections::HashMap;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;
use std::time::Instant;

use sunflower_formal::sat::{Solver, Verdict};
use sunflower_formal::symbreak::{
    degree_cubes, encode, sequence_cubes, solve_cube, SymInstance, SymOptions,
};

fn solver_by_name(name: &str) -> Solver {
    match name {
        "cadical" => Solver::Cadical,
        "cryptominisat5" | "cms" => Solver::CryptoMiniSat,
        "picosat" => Solver::PicoSat,
        "minisat" => Solver::Minisat,
        other => panic!("unknown solver {other}"),
    }
}

/// Verdicts already recorded for this question, by cube label.
///
/// A cube is skipped only when the checkpoint says `UNSAT` or `SAT`.
/// `UNKNOWN` is a budget, not a verdict, so a stalled cube is re-run --
/// the same rule `tools/rung.sh` learned the hard way when an `ERROR`
/// row was mistaken for a decision.
fn load_checkpoint(path: &Path) -> HashMap<String, String> {
    let mut out = HashMap::new();
    let Ok(text) = std::fs::read_to_string(path) else {
        return out;
    };
    for line in text.lines() {
        if line.starts_with('#') || line.trim().is_empty() {
            continue;
        }
        let mut it = line.split('\t');
        let (Some(label), Some(verdict)) = (it.next(), it.next()) else {
            continue;
        };
        if verdict == "UNSAT" || verdict == "SAT" {
            out.insert(label.to_string(), verdict.to_string());
        }
    }
    out
}

fn append_checkpoint(path: &Path, label: &str, verdict: &str, secs: f64) {
    use std::io::Write as _;
    if let Ok(mut f) = std::fs::OpenOptions::new().create(true).append(true).open(path) {
        let _ = writeln!(f, "{label}\t{verdict}\t{secs:.1}");
        let _ = f.flush();
    }
}

/// Solve a list of cubes across `threads` cores, printing each verdict as
/// it lands. Returns the witness if one turned up, and the labels of the
/// cubes that hit their limit.
///
/// With `checkpoint` set, every landed verdict is appended to that file
/// as it happens and cubes already recorded there are skipped. A
/// nineteen-hour cube on a container that is reclaimed without warning
/// is otherwise all-or-nothing; this makes it resumable.
fn solve_all(
    inst: &SymInstance,
    cubes: &[(String, Vec<i32>)],
    solver: Solver,
    seconds: u64,
    threads: usize,
    tagbase: &str,
    checkpoint: Option<&Path>,
) -> (Option<Vec<u32>>, Vec<String>) {
    let done = checkpoint.map(load_checkpoint).unwrap_or_default();
    if !done.is_empty() {
        println!("# checkpoint: {} of {} cubes already decided", done.len(), cubes.len());
        let _ = std::io::stdout().flush();
    }
    let next = AtomicUsize::new(0);
    let found: Mutex<Option<Vec<u32>>> = Mutex::new(None);
    let stalled: Mutex<Vec<String>> = Mutex::new(Vec::new());
    let out = Mutex::new(());

    std::thread::scope(|scope| {
        for _ in 0..threads.max(1) {
            scope.spawn(|| loop {
                if found.lock().unwrap().is_some() {
                    return;
                }
                let idx = next.fetch_add(1, Ordering::Relaxed);
                if idx >= cubes.len() {
                    return;
                }
                let (ref label, ref cube) = cubes[idx];
                if let Some(v) = done.get(label) {
                    // Recorded SAT would mean a witness this process does
                    // not hold; refuse to report UNSAT over it.
                    assert_ne!(v, "SAT", "checkpoint records SAT for {label}; rerun without it");
                    continue;
                }
                let start = Instant::now();
                let tag = format!("{tagbase}-c{idx}");
                let v = solve_cube(inst, cube, solver, seconds, &tag)
                    .unwrap_or_else(|e| panic!("solver failed: {e}"));
                let secs = start.elapsed().as_secs_f64();
                {
                    let _g = out.lock().unwrap();
                    println!("    {label:<34} {:<8} {secs:8.1}s", v.label());
                    let _ = std::io::stdout().flush();
                }
                if let Some(p) = checkpoint {
                    let _g = out.lock().unwrap();
                    append_checkpoint(p, label, v.label(), secs);
                }
                match v {
                    Verdict::Sat(f) => {
                        *found.lock().unwrap() = Some(f);
                    }
                    Verdict::Unknown => stalled.lock().unwrap().push(label.clone()),
                    Verdict::Unsat => {}
                }
            });
        }
    });
    let w = found.lock().unwrap().clone();
    let st = stalled.lock().unwrap().clone();
    (w, st)
}

/// One (ground, target) question. The `deg(0)` split first, with a time
/// slice; whatever has not landed inside the slice is re-split by its
/// **degree sequence** and run again with the full budget.
///
/// The two-phase shape is the point. The degree-sequence split is much
/// finer — with `sum_x deg(x) = b*t` pinned, a near-regular `deg(0)`
/// splits into a handful of exact sequences — but it costs a solver
/// process per cube, and on the easy cubes that overhead is most of the
/// run. Slicing spends the fine split only where the coarse one stalls.
fn run_one(
    b: u32,
    ground: u32,
    target: usize,
    opts: SymOptions,
    solver: Solver,
    seconds: u64,
    threads: usize,
    slice: u64,
    seqsplit: bool,
    cubecap: usize,
    only_deg: Option<usize>,
    checkpoint: Option<&Path>,
    seqprefix: usize,
) -> Verdict {
    let t0 = Instant::now();
    let inst = encode(ground, b, target, opts);
    let coarse: Vec<(String, Vec<i32>)> = degree_cubes(&inst)
        .into_iter()
        .filter(|(d, _)| only_deg.is_none_or(|k| *d == k))
        .map(|(d, l)| (format!("g={ground} deg(0)={d}"), l))
        .collect();
    if let Some(k) = only_deg {
        println!(
            "# ONE CUBE ONLY: deg(0) = {k}. This decides that cube and \
             nothing else; the rung is UNSAT only when every cube is."
        );
        assert_eq!(coarse.len(), 1, "deg(0) = {k} is not a cube of this instance");
    }
    println!(
        "# g = {ground}: {} vars, {} clauses, {} deg(0) cubes ({}..={}), slice {}s",
        inst.cnf.nvars,
        inst.cnf.clauses.len(),
        coarse.len(),
        inst.floor,
        inst.kmax,
        if slice == 0 { "no".to_string() } else { slice.to_string() }
    );
    let _ = std::io::stdout().flush();

    let tagbase = format!("sym-{ground}-{b}-{target}");
    let (witness, stalled) = solve_all(
        &inst,
        &coarse,
        solver,
        if slice == 0 { seconds } else { slice },
        threads,
        &tagbase,
        None,
    );
    if let Some(f) = witness {
        return Verdict::Sat(f);
    }
    if stalled.is_empty() {
        println!(
            "# g = {ground}: UNSAT after {:.1}s ({} cubes)",
            t0.elapsed().as_secs_f64(),
            coarse.len()
        );
        return Verdict::Unsat;
    }

    // Phase two: the sequences of the cubes that stalled.
    let stalled_d0: Vec<usize> = stalled
        .iter()
        .filter_map(|s| s.rsplit('=').next().and_then(|t| t.parse().ok()))
        .collect();
    println!(
        "# g = {ground}: {} cube(s) past the slice at deg(0) in {stalled_d0:?}; \
         re-splitting by degree sequence",
        stalled.len()
    );
    // Per stalled cube, not all of them at once: the sequences for a
    // large deg(0) are numerous and for the small ones -- which is where
    // the solver actually stalls -- they are a handful. A cube whose
    // enumeration is too large keeps its coarse form and the full budget.
    let mut fine: Vec<(String, Vec<i32>)> = Vec::new();
    let mut refined = 0usize;
    for d0 in &stalled_d0 {
        // Refine only when the *full* degree-sequence split is small.
        // Measured at `g = 10`: `deg(0) = 13` has a deficiency of two and
        // splits into five sequences, each of which lands in under two
        // minutes against more than twenty for the cube whole -- a clear
        // win. `deg(0) = 14` has a deficiency of twelve and splits into
        // 684, and paying 684 solver startups for an instance that solves
        // whole in ten minutes is a clear loss. The cap is the line
        // between them, and a cube past it keeps its coarse form and the
        // full budget.
        let best = if seqsplit {
            sequence_cubes(&inst, opts, &[*d0], seqprefix.min(ground as usize), cubecap)
        } else {
            None
        };
        match best {
            Some(cs) if cs.len() > 1 => {
                refined += 1;
                for (seq, l) in cs {
                    fine.push((format!("g={ground} {seq:?}"), l));
                }
            }
            _ => {
                if let Some((lab, lits)) =
                    coarse.iter().find(|(lab, _)| lab.ends_with(&format!("={d0}")))
                {
                    fine.push((lab.clone(), lits.clone()));
                }
            }
        }
    }
    if fine.is_empty() {
        println!("# g = {ground}: no finer split available -- UNKNOWN");
        return Verdict::Unknown;
    }
    println!("# g = {ground}: {refined} of {} cubes refined", stalled_d0.len());
    println!("# g = {ground}: {} degree-sequence cubes", fine.len());
    let _ = std::io::stdout().flush();
    let (witness, stalled) = solve_all(&inst, &fine, solver, seconds, threads, &format!("{tagbase}-seq"), checkpoint);
    if let Some(f) = witness {
        return Verdict::Sat(f);
    }
    println!(
        "# g = {ground}: {} after {:.1}s ({} sequence cubes, {} at the limit)",
        if stalled.is_empty() { "UNSAT" } else { "UNKNOWN" },
        t0.elapsed().as_secs_f64(),
        fine.len(),
        stalled.len()
    );
    let _ = std::io::stdout().flush();
    if stalled.is_empty() {
        Verdict::Unsat
    } else {
        Verdict::Unknown
    }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.len() < 3 {
        eprintln!(
            "usage: iota_sym <b> <ground> <target> [--seconds N] [--threads T] \
             [--kmax K] [--solver S] [--plain] [--ladder]"
        );
        std::process::exit(2);
    }
    let b: u32 = args[0].parse().unwrap();
    let ground: u32 = args[1].parse().unwrap();
    let target: usize = args[2].parse().unwrap();

    let mut seconds: u64 = 0;
    let mut threads: usize = 4;
    let mut solver = Solver::Cadical;
    let mut ladder = false;
    let mut seqsplit = true;
    let mut slice: u64 = 120;
    let mut cubecap: usize = 48;
    let mut from: Option<u32> = None;
    let mut only_deg: Option<usize> = None;
    let mut checkpoint: Option<PathBuf> = None;
    let mut seqprefix: Option<usize> = None;
    let mut opts = SymOptions::default();
    let mut i = 3;
    while i < args.len() {
        match args[i].as_str() {
            "--seconds" => {
                seconds = args[i + 1].parse().unwrap();
                i += 2;
            }
            "--threads" => {
                threads = args[i + 1].parse().unwrap();
                i += 2;
            }
            "--kmax" => {
                opts.kmax = args[i + 1].parse().unwrap();
                i += 2;
            }
            "--solver" => {
                solver = solver_by_name(&args[i + 1]);
                i += 2;
            }
            "--plain" => {
                opts.max_at_zero = false;
                opts.sorted_blocks = false;
                opts.degree_floor = false;
                opts.exact_size = false;
                opts.lex_ties = false;
                i += 1;
            }
            "--from" => {
                from = Some(args[i + 1].parse().unwrap());
                i += 2;
            }
            "--cubecap" => {
                cubecap = args[i + 1].parse().unwrap();
                i += 2;
            }
            "--slice" => {
                slice = args[i + 1].parse().unwrap();
                i += 2;
            }
            "--noseq" => {
                seqsplit = false;
                i += 1;
            }
            "--nolex" => {
                opts.lex_ties = false;
                i += 1;
            }
            "--ladder" => {
                ladder = true;
                i += 1;
            }
            // One deg(0) cube, by name, so a rung can be run across
            // container restarts: each invocation decides one cube and
            // the caller records the verdict. See `docs/roadmap.md` §36.
            "--seqprefix" => {
                seqprefix = Some(args[i + 1].parse().unwrap());
                i += 2;
            }
            "--checkpoint" => {
                checkpoint = Some(PathBuf::from(&args[i + 1]));
                i += 2;
            }
            "--only-deg" => {
                only_deg = Some(args[i + 1].parse().unwrap());
                i += 2;
            }
            other => panic!("unknown flag {other}"),
        }
    }

    let t0 = Instant::now();
    println!(
        "# iota({b}, {ground}) >= {target}?  solver {}, {threads} threads, \
         {} s per cube, ladder={ladder}",
        solver.binary(),
        if seconds == 0 {
            "no".to_string()
        } else {
            seconds.to_string()
        }
    );
    println!(
        "# symmetry: max_at_zero={} sorted_blocks={} degree_floor={} exact_size={} \
         lex_ties={} kmax={}",
        opts.max_at_zero,
        opts.sorted_blocks,
        opts.degree_floor,
        opts.exact_size,
        opts.lex_ties,
        opts.kmax
    );
    let _ = std::io::stdout().flush();

    let grounds: Vec<u32> = if ladder {
        (from.unwrap_or(b)..=ground).collect()
    } else {
        vec![ground]
    };
    if let Some(f) = from {
        println!(
            "# RESUMED at g = {f}: the rungs below it are NOT re-decided here, and \
             the ladder is a cover only if they were decided elsewhere. \
             docs/roadmap.md 33.5 records where."
        );
    }
    let mut any_unknown = false;
    let mut witness: Option<Vec<u32>> = None;
    for g in grounds {
        let mut o = opts;
        o.all_points_used = ladder;
        let v = run_one(
            b, g, target, o, solver, seconds, threads, slice, seqsplit, cubecap, only_deg,
            checkpoint.as_deref(), seqprefix.unwrap_or(g as usize),
        );
        match v {
            Verdict::Sat(f) => {
                witness = Some(f);
                break;
            }
            Verdict::Unknown => {
                any_unknown = true;
            }
            Verdict::Unsat => {}
        }
    }

    let elapsed = t0.elapsed().as_secs_f64();
    if let Some(f) = witness {
        println!("VERDICT SAT   iota({b},{ground}) >= {target}   ({elapsed:.1}s)");
        let mut sorted = f.clone();
        sorted.sort_unstable();
        println!("# family ({} members), as point lists:", sorted.len());
        for s in &sorted {
            let pts: Vec<u32> = (0..ground).filter(|x| s >> x & 1 == 1).collect();
            println!("#   {pts:?}");
        }
        println!("# bitmasks: {sorted:?}");
    } else if any_unknown {
        println!("VERDICT UNKNOWN  a rung hit the limit ({elapsed:.1}s)");
    } else {
        println!(
            "VERDICT UNSAT  iota({b},{ground}) <= {}   ({elapsed:.1}s)",
            target - 1
        );
    }
}
