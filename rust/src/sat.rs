//! A SAT encoding of the extremal questions, and a driver for external
//! solvers.
//!
//! The homegrown branch-and-bound is out of road: `iota(4,10) >= 32?`
//! took 4437 seconds and `>= 31?` did not finish in an hour, a factor of
//! 89 for one extra ground point. Every reduction it can carry is
//! already in it. The questions themselves, though, are tiny by SAT
//! standards:
//!
//! * one boolean per `b`-subset of `[g]` — `C(11,4) = 330`,
//!   `C(12,5) = 792`;
//! * **intersecting** is binary clauses, one per disjoint pair;
//! * **sunflower-free** is *ternary* clauses, one per sunflower triple —
//!   and the ternary constraint is exactly what the branch-and-bound's
//!   bound cannot see;
//! * **at least `t` members** is a sequential counter.
//!
//! Three things keep this honest.
//!
//! **Symmetry.** A family may be relabelled so that a chosen member is
//! `{0,...,b-1}` — `DirectSum.relabel_preserves` is the theorem — so the
//! anchor is forced by a unit clause. For an intersecting family the
//! stabiliser of the anchor acts on the possible second members with
//! `b-1` orbits, one per `|B ∩ anchor|`, so the query splits into `b-1`
//! independent instances. That is the reduction `intersecting::iota_decide`
//! already carries, moved across.
//!
//! **The degree cap.** `IotaGround.link_degree_ground_bound` proves
//! `deg(x) <= N(b-1, g-1)` for every point of a sunflower-free
//! `b`-uniform family. It is implied by the ternary clauses, so adding it
//! changes no answer — but it is a *global* consequence a CDCL solver
//! would have to rediscover, and it is the bound `docs/roadmap.md` §7
//! names as the missing ingredient. It is optional here so that its
//! effect can be measured rather than assumed.
//!
//! **Never trust the model.** A satisfying assignment is decoded to a
//! family and handed to `intersecting::verify`, which shares no code with
//! this module. An UNSAT verdict is checked by running a second,
//! independent solver: `solve_agreed` returns a verdict only when two
//! solvers agree, which is the same discipline `Reflect.rao_witness_agrees`
//! applies to the two search procedures on the Coq side.

use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

use crate::ground::m_subsets;

/// A CNF in DIMACS numbering: variables are `1..=nvars`, a literal is
/// `+v` or `-v`.
#[derive(Debug, Clone, Default)]
pub struct Cnf {
    pub nvars: usize,
    pub clauses: Vec<Vec<i32>>,
}

impl Cnf {
    pub fn new() -> Self {
        Cnf::default()
    }

    pub fn new_var(&mut self) -> i32 {
        self.nvars += 1;
        self.nvars as i32
    }

    pub fn add(&mut self, clause: Vec<i32>) {
        self.clauses.push(clause);
    }

    pub fn to_dimacs(&self) -> String {
        let mut s = String::with_capacity(16 * self.clauses.len());
        let _ = writeln!(s, "p cnf {} {}", self.nvars, self.clauses.len());
        for c in &self.clauses {
            for l in c {
                let _ = write!(s, "{l} ");
            }
            s.push_str("0\n");
        }
        s
    }

    /// Assert that at least `t` of `lits` hold.
    ///
    /// Sequential counter: `c[i][j]` reads "at least `j` of the first
    /// `i` literals". Only the *only-if* direction is encoded, which is
    /// all an assertion needs — the solver may leave counters false, but
    /// it cannot make `c[n][t]` true without `t` genuine witnesses.
    ///
    /// `O(n*t)` variables and clauses. `t = 0` is vacuous; `t > n` is
    /// unsatisfiable and is encoded as the empty clause.
    pub fn at_least(&mut self, lits: &[i32], t: usize) {
        let n = lits.len();
        if t == 0 {
            return;
        }
        if t > n {
            self.add(vec![]);
            return;
        }
        // c[i][j] for 1 <= i <= n, 1 <= j <= min(i, t); index j-1.
        let mut c: Vec<Vec<i32>> = Vec::with_capacity(n + 1);
        c.push(Vec::new()); // c[0]: nothing is at least 1 of zero literals
        for i in 1..=n {
            let jmax = i.min(t);
            let row: Vec<i32> = (0..jmax).map(|_| self.new_var()).collect();
            c.push(row);
        }
        for i in 1..=n {
            let jmax = i.min(t);
            for j in 1..=jmax {
                let cij = c[i][j - 1];
                let prev_same = if j <= c[i - 1].len() {
                    Some(c[i - 1][j - 1])
                } else {
                    None
                };
                // c[i][j] -> c[i-1][j] \/ x_i
                let mut cl = vec![-cij];
                if let Some(p) = prev_same {
                    cl.push(p);
                }
                cl.push(lits[i - 1]);
                self.add(cl);
                // c[i][j] -> c[i-1][j] \/ c[i-1][j-1]     (j >= 2)
                if j >= 2 {
                    let mut cl = vec![-cij];
                    if let Some(p) = prev_same {
                        cl.push(p);
                    }
                    cl.push(c[i - 1][j - 2]);
                    self.add(cl);
                }
            }
        }
        let top = c[n][t - 1];
        self.add(vec![top]);
    }

    /// Assert that at most `k` of `lits` hold, as "at least `n - k` of
    /// the negations".
    pub fn at_most(&mut self, lits: &[i32], k: usize) {
        let n = lits.len();
        if k >= n {
            return;
        }
        let neg: Vec<i32> = lits.iter().map(|l| -l).collect();
        self.at_least(&neg, n - k);
    }
}

/// Do `a`, `b`, `c` form a 3-sunflower?
#[inline]
fn is_sunflower(a: u32, b: u32, c: u32) -> bool {
    let ab = a & b;
    ab == (a & c) && ab == (b & c)
}

/// One encoded question, with the dictionary needed to read a model back
/// as a family.
#[derive(Debug, Clone)]
pub struct Instance {
    /// The candidate `b`-sets, in variable order.
    pub sets: Vec<u32>,
    /// `vars[i]` is the DIMACS variable for `sets[i]`.
    pub vars: Vec<i32>,
    pub cnf: Cnf,
    pub ground: u32,
    pub b: u32,
    pub target: usize,
    pub intersecting: bool,
}

/// How to break symmetry beyond the forced anchor.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SecondMember {
    /// No constraint on the second member.
    Free,
    /// Force a second member meeting the anchor in exactly `j` points.
    /// Only sound for intersecting families, where the stabiliser of the
    /// anchor has exactly one orbit per value of `j`.
    Orbit(u32),
}

/// Encode "is there a `b`-uniform 3-sunflower-free family of at least
/// `target` members on `[ground]`?", optionally intersecting.
///
/// The anchor `{0,...,b-1}` is forced. That is sound for **either**
/// question: relabelling the ground set preserves uniformity,
/// distinctness and sunflower-freeness, so a family with at least one
/// member may be assumed to contain it.
///
/// `degree_cap` adds `deg(x) <= cap` for every point. Pass the measured
/// `N(b-1, ground-1)`; the constraint is implied by the ternary clauses,
/// so it cannot change the answer, and `sat_degree_cap_changes_no_answer`
/// checks that on every small case.
pub fn encode(
    ground: u32,
    b: u32,
    target: usize,
    intersecting: bool,
    second: SecondMember,
    degree_cap: Option<usize>,
) -> Instance {
    assert!(ground >= b, "ground set smaller than the uniformity");
    assert!(target >= 1, "the anchor makes target 0 trivial");
    let anchor: u32 = (1u32 << b) - 1;

    // Candidates: everything except the anchor, and — when intersecting
    // — only what meets it. The anchor itself is asserted separately, so
    // it is not a variable.
    let sets: Vec<u32> = m_subsets(ground, b)
        .into_iter()
        .map(u32::from)
        .filter(|s| *s != anchor && (!intersecting || s & anchor != 0))
        .collect();
    let mut cnf = Cnf::new();
    let vars: Vec<i32> = sets.iter().map(|_| cnf.new_var()).collect();

    // Pairwise: intersecting.
    if intersecting {
        for i in 0..sets.len() {
            for j in (i + 1)..sets.len() {
                if sets[i] & sets[j] == 0 {
                    cnf.add(vec![-vars[i], -vars[j]]);
                }
            }
        }
    }

    // Ternary: no 3-sunflower. Triples involving the anchor collapse to
    // binary clauses, since the anchor is forced.
    for i in 0..sets.len() {
        for j in (i + 1)..sets.len() {
            if is_sunflower(anchor, sets[i], sets[j]) {
                cnf.add(vec![-vars[i], -vars[j]]);
            }
            for l in (j + 1)..sets.len() {
                if is_sunflower(sets[i], sets[j], sets[l]) {
                    cnf.add(vec![-vars[i], -vars[j], -vars[l]]);
                }
            }
        }
    }

    // Second member, up to the stabiliser of the anchor.
    if let SecondMember::Orbit(j) = second {
        let mut rep: u32 = (1u32 << j) - 1;
        for t in 0..(b - j) {
            rep |= 1 << (b + t);
        }
        let idx = sets
            .iter()
            .position(|&s| s == rep)
            .expect("the orbit representative is not a candidate");
        cnf.add(vec![vars[idx]]);
    }

    // Degree cap, one cardinality constraint per point. The anchor
    // occupies one unit of the cap on each of its own points.
    if let Some(cap) = degree_cap {
        for x in 0..ground {
            let lits: Vec<i32> = sets
                .iter()
                .zip(vars.iter())
                .filter(|(s, _)| *s >> x & 1 == 1)
                .map(|(_, v)| *v)
                .collect();
            let used = usize::from(anchor >> x & 1 == 1);
            if cap > used {
                cnf.at_most(&lits, cap - used);
            } else {
                for l in lits {
                    cnf.add(vec![-l]);
                }
            }
        }
    }

    // At least `target` members, one of which is the anchor.
    cnf.at_least(&vars, target - 1);

    Instance {
        sets,
        vars,
        cnf,
        ground,
        b,
        target,
        intersecting,
    }
}

/// What a solver said.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Verdict {
    /// Satisfiable, with the decoded family (the anchor included).
    Sat(Vec<u32>),
    Unsat,
    /// The solver gave up, or was killed by the timeout.
    Unknown,
}

impl Verdict {
    pub fn label(&self) -> &'static str {
        match self {
            Verdict::Sat(_) => "SAT",
            Verdict::Unsat => "UNSAT",
            Verdict::Unknown => "UNKNOWN",
        }
    }
}

/// Solvers this driver knows how to talk to. All read DIMACS; only
/// `Minisat` writes its answer to a file rather than to stdout.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Solver {
    Cadical,
    CryptoMiniSat,
    PicoSat,
    Minisat,
}

impl Solver {
    pub fn binary(self) -> &'static str {
        match self {
            Solver::Cadical => "cadical",
            Solver::CryptoMiniSat => "cryptominisat5",
            Solver::PicoSat => "picosat",
            Solver::Minisat => "minisat",
        }
    }

    pub fn available(self) -> bool {
        Command::new("sh")
            .arg("-c")
            .arg(format!("command -v {}", self.binary()))
            .output()
            .map(|o| o.status.success())
            .unwrap_or(false)
    }
}

fn scratch_dir() -> PathBuf {
    std::env::var("SUNFLOWER_SAT_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|_| std::env::temp_dir())
}

/// Run one solver on one instance. `seconds` of 0 means no limit.
///
/// A SAT verdict is decoded **and re-verified** with
/// `intersecting::verify`, which shares no code with this module; a model
/// that does not check out is a hard error rather than a result.
pub fn solve(inst: &Instance, solver: Solver, seconds: u64) -> std::io::Result<Verdict> {
    // The name has to be unique per call, not per question: two
    // instances of the same shape are solved concurrently by the test
    // suite, and sharing a path silently corrupts both.
    static SEQ: AtomicU64 = AtomicU64::new(0);
    let dir = scratch_dir();
    let stamp = format!(
        "sf-{}-{}-{}-{}-{}-{}",
        inst.ground,
        inst.b,
        inst.target,
        solver.binary(),
        std::process::id(),
        SEQ.fetch_add(1, Ordering::Relaxed)
    );
    let cnf_path = dir.join(format!("{stamp}.cnf"));
    std::fs::write(&cnf_path, inst.cnf.to_dimacs())?;
    let out_path = dir.join(format!("{stamp}.out"));

    let mut cmd = Command::new(solver.binary());
    match solver {
        Solver::Cadical => {
            if seconds > 0 {
                cmd.arg("-t").arg(seconds.to_string());
            }
            cmd.arg(&cnf_path);
        }
        Solver::CryptoMiniSat => {
            cmd.arg("--verb").arg("0");
            if seconds > 0 {
                cmd.arg("--maxtime").arg(seconds.to_string());
            }
            cmd.arg(&cnf_path);
        }
        Solver::PicoSat => {
            if seconds > 0 {
                cmd.arg("-T").arg(seconds.to_string());
            }
            cmd.arg(&cnf_path);
        }
        Solver::Minisat => {
            if seconds > 0 {
                cmd.arg(format!("-cpu-lim={seconds}"));
            }
            cmd.arg(&cnf_path).arg(&out_path);
        }
    }
    let output = cmd.output()?;
    let text = if solver == Solver::Minisat {
        std::fs::read_to_string(&out_path).unwrap_or_default()
    } else {
        String::from_utf8_lossy(&output.stdout).into_owned()
    };
    let _ = std::fs::remove_file(&cnf_path);
    let _ = std::fs::remove_file(&out_path);

    let verdict = parse_output(&text, inst, solver);
    if let Verdict::Sat(ref fam) = verdict {
        crate::intersecting::verify(fam, inst.b, inst.intersecting)
            .unwrap_or_else(|e| panic!("{} returned a bad model: {e}", solver.binary()));
        assert!(
            fam.len() >= inst.target,
            "{} returned a model of size {} below the target {}",
            solver.binary(),
            fam.len(),
            inst.target
        );
    }
    Ok(verdict)
}

fn parse_output(text: &str, inst: &Instance, solver: Solver) -> Verdict {
    let sat = if solver == Solver::Minisat {
        // minisat's result file is "SAT" / "UNSAT" then the assignment.
        match text.lines().next().map(str::trim) {
            Some("SAT") => true,
            Some("UNSAT") => return Verdict::Unsat,
            _ => return Verdict::Unknown,
        }
    } else if text.contains("s UNSATISFIABLE") {
        return Verdict::Unsat;
    } else if text.contains("s SATISFIABLE") {
        true
    } else {
        return Verdict::Unknown;
    };
    if !sat {
        return Verdict::Unknown;
    }

    // Collect the true variables.
    let mut positive: Vec<i32> = Vec::new();
    for line in text.lines() {
        let body = if solver == Solver::Minisat {
            if line.trim() == "SAT" {
                continue;
            }
            line
        } else if let Some(rest) = line.strip_prefix("v ") {
            rest
        } else {
            continue;
        };
        for tok in body.split_whitespace() {
            if let Ok(v) = tok.parse::<i32>() {
                if v > 0 {
                    positive.push(v);
                }
            }
        }
    }
    positive.sort_unstable();
    let anchor: u32 = (1u32 << inst.b) - 1;
    let mut fam = vec![anchor];
    for (i, v) in inst.vars.iter().enumerate() {
        if positive.binary_search(v).is_ok() {
            fam.push(inst.sets[i]);
        }
    }
    Verdict::Sat(fam)
}

/// Run two independent solvers and return the verdict only if they
/// agree. A disagreement is a hard error: one of them is wrong, and
/// which one is not something this code can decide.
///
/// This is the SAT-side version of `Reflect.rao_witness_agrees`, which
/// pits two independent searches against each other on the Coq side. An
/// UNSAT verdict is the one that carries mathematical weight here, and
/// it is the one no witness can confirm, so it is the one that most
/// needs a second opinion.
pub fn solve_agreed(
    inst: &Instance,
    a: Solver,
    b: Solver,
    seconds: u64,
) -> std::io::Result<Verdict> {
    let va = solve(inst, a, seconds)?;
    let vb = solve(inst, b, seconds)?;
    match (&va, &vb) {
        (Verdict::Unknown, _) | (_, Verdict::Unknown) => Ok(Verdict::Unknown),
        (Verdict::Unsat, Verdict::Unsat) => Ok(Verdict::Unsat),
        (Verdict::Sat(_), Verdict::Sat(_)) => Ok(va),
        _ => panic!(
            "solvers disagree on (ground {}, b {}, target {}): {} says {}, {} says {}",
            inst.ground,
            inst.b,
            inst.target,
            a.binary(),
            va.label(),
            b.binary(),
            vb.label()
        ),
    }
}

/// The full decision for an intersecting family, split over the `b-1`
/// orbits of the second member. SAT on any orbit decides yes; UNSAT
/// needs all of them.
///
/// With `target = 1` there is no second member to constrain, so the
/// split does not apply and a single free instance is used.
pub fn decide_iota(
    ground: u32,
    b: u32,
    target: usize,
    degree_cap: Option<usize>,
    solver: Solver,
    seconds: u64,
) -> std::io::Result<Verdict> {
    if target <= 1 {
        let inst = encode(ground, b, target.max(1), true, SecondMember::Free, degree_cap);
        return solve(&inst, solver, seconds);
    }
    let mut any_unknown = false;
    for j in 1..b {
        if b + (b - j) > ground {
            continue;
        }
        let inst = encode(ground, b, target, true, SecondMember::Orbit(j), degree_cap);
        match solve(&inst, solver, seconds)? {
            Verdict::Sat(f) => return Ok(Verdict::Sat(f)),
            Verdict::Unsat => {}
            Verdict::Unknown => any_unknown = true,
        }
    }
    Ok(if any_unknown {
        Verdict::Unknown
    } else {
        Verdict::Unsat
    })
}

/// The general question `N(m, g) >= target`, with the anchor forced and
/// no intersecting hypothesis.
pub fn decide_general(
    ground: u32,
    b: u32,
    target: usize,
    degree_cap: Option<usize>,
    solver: Solver,
    seconds: u64,
) -> std::io::Result<Verdict> {
    let inst = encode(ground, b, target, false, SecondMember::Free, degree_cap);
    solve(&inst, solver, seconds)
}

/// Write an instance to a file, for handing to a solver by hand.
pub fn write_dimacs(inst: &Instance, path: &Path) -> std::io::Result<()> {
    std::fs::write(path, inst.cnf.to_dimacs())
}
