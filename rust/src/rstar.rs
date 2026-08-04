//! `r*(m,3)`: the sharp spread threshold, as a SAT question.
//!
//! `SpreadReduction.SpreadYieldsDisjoint n k r` says every `r`-spread
//! `m`-uniform family (`1 <= m <= n`) of more than `r^m` distinct sets
//! has `k` pairwise disjoint members. `r*(m,k)` is the least `r` making
//! it true, and `spread_reduction` turns a bound on `r*(m,3)` into
//! `f(m,3) <= r^m + 1`. So **whether `r*(m,3)` is bounded in `m` is the
//! sunflower conjecture at `k = 3`**, and the sequence is the problem
//! written as integers.
//!
//! `testbed.rs` decides the same question by enumerating every family
//! over a ground set. That search is complete but its tree is the whole
//! downward-closed set of spread families, and §3.6 records where it
//! stops: ground 9 at uniformity 3, which is one point short of the
//! first ground set that could hold a counterexample. This module asks
//! the same question of a SAT solver, and adds the structure that the
//! enumeration cannot see.
//!
//! # What a counterexample must look like
//!
//! Let `F` be `m`-uniform, `RaoSpread m F r`, `|F| > r^m`, with no three
//! pairwise disjoint members — that is, matching number `nu(F) <= 2`.
//!
//! * **`nu(F) = 1` needs `r < m`.** An intersecting family is covered by
//!   any one of its members, so `|F| <= m * r^(m-1)`, and that is at most
//!   `r^m` once `r >= m`.
//! * **Otherwise fix a maximum matching `{A, B}`.** Relabelling makes
//!   `A = {0..m-1}` and `B = {m..2m-1}`; maximality makes every member
//!   meet `T = A ∪ B`, so `|F| <= 2m * r^(m-1)` and `r < 2m`.
//! * **`{C ∈ F : C ∩ B = ∅}` is intersecting**, for `B` *any* member:
//!   two disjoint members missing `B` would be three pairwise disjoint
//!   sets with `B`. With `A` and `B` forced this is a family of binary
//!   clauses, and binary clauses are what a CDCL solver propagates.
//!
//! In the Coq layer the first two are the branches of
//! `SpreadThreshold.quadratic_no_three_disjoint_bound` and the cover is
//! `SpreadThreshold.no_three_disjoint_cover_bound`; the third is
//! `SpreadThreshold.miss_member_intersecting`, and the piece bound it
//! feeds is `SpreadThreshold.intersecting_piece_bound`.
//!
//! # Symmetry
//!
//! After the anchors are forced the residual group is
//! `(Sym(A) x Sym(B)) ⋊ swap x Sym(U)` on the `U = [2m..ground)` tail.
//! Each generator gets a lex-leader constraint `X >=_lex g(X)`: the
//! lex-greatest member of every orbit satisfies all of them at once, so
//! imposing them for a generating set is sound even though it is not the
//! full lex-leader constraint. Sorting `U` this way also packs the used
//! points to the front, so a search at `ground = n` covers every support
//! of size at most `n`.

use crate::sat::{solve_cnf, solve_cnf_agreed, Cnf, RawVerdict, Solver};
use crate::spread::{has_k_disjoint, is_distinct, is_rao_spread, is_uniform, pow_sat, Mask};

/// How the "no `k` pairwise disjoint members" constraint is encoded.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Ternary {
    /// Every pairwise-disjoint triple gets its clause up front.
    Eager,
    /// Only the binary consequences up front; violated triples are added
    /// as they are found, and the solver is re-run. Refutation rounds are
    /// counted in [`Report::rounds`].
    Lazy,
}

/// One `(m, k, r, ground)` question.
#[derive(Debug, Clone)]
pub struct Question {
    pub m: u32,
    pub k: usize,
    pub r: u64,
    pub ground: u32,
    /// Matching number assumed for the counterexample: 1 (intersecting,
    /// one anchor) or 2 (two anchors and a cover). Both must be asked
    /// when `r < m`; only 2 when `r >= m`.
    pub nu: usize,
    pub ternary: Ternary,
    /// Break the residual symmetry with lex-leader constraints.
    pub symmetry: bool,
}

impl Question {
    pub fn new(m: u32, r: u64, ground: u32) -> Self {
        Question {
            m,
            k: 3,
            r,
            ground,
            nu: 2,
            ternary: Ternary::Eager,
            symmetry: true,
        }
    }

    /// `r^m + 1`: the number of members a counterexample needs.
    pub fn target(&self) -> u64 {
        pow_sat(self.r, self.m) + 1
    }

    pub fn tag(&self) -> String {
        format!("rstar-m{}-r{}-g{}-nu{}", self.m, self.r, self.ground, self.nu)
    }
}

/// The candidate members: `m`-subsets of `[ground]` that meet the cover
/// `[nu*m]`. Members missing the cover are ruled out by maximality of the
/// anchor matching, so they are left out of the encoding entirely.
pub fn candidates(q: &Question) -> Vec<Mask> {
    let cover: Mask = ((1u64 << (q.nu as u32 * q.m)) - 1) as Mask;
    let mut out = Vec::new();
    for s in 0u32..(1u32 << q.ground) {
        if s.count_ones() == q.m && s & cover != 0 {
            out.push(s);
        }
    }
    out
}

/// Sinz's sequential counter for "at most `k` of `lits`", `O(n*k)`
/// clauses. The crate's [`Cnf::at_most`] encodes the same thing as
/// "at least `n-k` of the negations", which is `O(n*(n-k))` — the wrong
/// way round when `k` is a degree cap and `n` is every set through a
/// point.
fn at_most_seq(cnf: &mut Cnf, lits: &[i32], k: usize) {
    let n = lits.len();
    if k >= n {
        return;
    }
    if k == 0 {
        for &l in lits {
            cnf.add(vec![-l]);
        }
        return;
    }
    // s[i][j] reads "at least j+1 of lits[0..=i]".
    let mut s: Vec<Vec<i32>> = Vec::with_capacity(n);
    for _ in 0..n {
        let row: Vec<i32> = (0..k).map(|_| cnf.new_var()).collect();
        s.push(row);
    }
    cnf.add(vec![-lits[0], s[0][0]]);
    for j in 1..k {
        cnf.add(vec![-s[0][j]]);
    }
    for i in 1..n {
        cnf.add(vec![-lits[i], s[i][0]]);
        for j in 0..k {
            cnf.add(vec![-s[i - 1][j], s[i][j]]);
        }
        for j in 1..k {
            cnf.add(vec![-lits[i], -s[i - 1][j - 1], s[i][j]]);
        }
        cnf.add(vec![-lits[i], -s[i - 1][k - 1]]);
    }
}

/// `a >=_lex b`, with `a` and `b` literal vectors of equal length.
///
/// `e[i]` reads "the first `i` positions agree". The lex-greatest element
/// of an orbit satisfies this for *every* group element, so asserting it
/// for a generating set keeps at least one representative per orbit.
fn lex_geq(cnf: &mut Cnf, a: &[i32], b: &[i32]) {
    assert_eq!(a.len(), b.len());
    let mut eq: Option<i32> = None; // None means "true" (prefix empty)
    for i in 0..a.len() {
        // prefix equal -> a[i] >= b[i]
        match eq {
            None => cnf.add(vec![a[i], -b[i]]),
            Some(e) => cnf.add(vec![-e, a[i], -b[i]]),
        }
        if i + 1 == a.len() {
            break;
        }
        let e2 = cnf.new_var();
        match eq {
            None => {
                cnf.add(vec![-a[i], -b[i], e2]);
                cnf.add(vec![a[i], b[i], e2]);
            }
            Some(e) => {
                cnf.add(vec![-e, -a[i], -b[i], e2]);
                cnf.add(vec![-e, a[i], b[i], e2]);
            }
        }
        eq = Some(e2);
    }
}

/// Apply a permutation of `[ground]` to a mask.
fn permute(a: Mask, perm: &[u32]) -> Mask {
    let mut out = 0;
    let mut x = a;
    while x != 0 {
        let i = x.trailing_zeros();
        out |= 1u32 << perm[i as usize];
        x &= x - 1;
    }
    out
}

/// The encoded instance, plus the dictionary to read a model back.
pub struct Instance {
    pub q: Question,
    pub sets: Vec<Mask>,
    pub vars: Vec<i32>,
    pub cnf: Cnf,
    /// Clauses added up front for pairwise-disjoint triples.
    pub ternary_clauses: usize,
    /// Clauses added up front for pairwise-disjoint pairs inside an
    /// anchor's complement.
    pub binary_clauses: usize,
}

/// Build the CNF.
pub fn encode(q: &Question) -> Instance {
    assert!(q.k == 3, "only k = 3 is encoded");
    assert!(q.nu == 1 || q.nu == 2);
    assert!(q.ground >= q.nu as u32 * q.m);
    let sets = candidates(q);
    let mut cnf = Cnf::new();
    let vars: Vec<i32> = sets.iter().map(|_| cnf.new_var()).collect();
    let index = |a: Mask| sets.binary_search(&a).ok();
    let var_of = |a: Mask| index(a).map(|i| vars[i]);

    // The anchors. A = [0,m); for nu = 2 also B = [m,2m).
    let a_mask: Mask = ((1u64 << q.m) - 1) as Mask;
    let b_mask: Mask = if q.nu == 2 { a_mask << q.m } else { 0 };
    cnf.add(vec![var_of(a_mask).expect("anchor A is a candidate")]);
    if q.nu == 2 {
        cnf.add(vec![var_of(b_mask).expect("anchor B is a candidate")]);
    }

    // Size: at least r^m + 1 members.
    let target = q.target() as usize;
    cnf.at_least(&vars, target);

    // RaoSpread: deg(S) <= r^(m - |S|) for every nonempty S. |S| >= m is
    // the distinctness the variables already carry.
    for s in 1u32..(1u32 << q.ground) {
        let t = s.count_ones();
        if t >= q.m {
            continue;
        }
        let cap = pow_sat(q.r, q.m - t) as usize;
        let lits: Vec<i32> = sets
            .iter()
            .zip(vars.iter())
            .filter(|(&a, _)| a & s == s)
            .map(|(_, &v)| v)
            .collect();
        if lits.len() > cap {
            at_most_seq(&mut cnf, &lits, cap);
        }
    }

    // nu <= 2, part one: for each anchor E, {C : C ∩ E = ∅} is
    // intersecting. Binary clauses.
    let mut binary_clauses = 0;
    let mut anchors = vec![a_mask];
    if q.nu == 2 {
        anchors.push(b_mask);
    }
    for &e in &anchors {
        for i in 0..sets.len() {
            if sets[i] & e != 0 {
                continue;
            }
            for j in (i + 1)..sets.len() {
                if sets[j] & e != 0 || sets[i] & sets[j] != 0 {
                    continue;
                }
                cnf.add(vec![-vars[i], -vars[j]]);
                binary_clauses += 1;
            }
        }
    }

    // nu <= 2, part two: every pairwise-disjoint triple. A triple with
    // two members missing the same anchor already has a binary clause.
    let mut ternary_clauses = 0;
    if q.ternary == Ternary::Eager {
        for i in 0..sets.len() {
            for j in (i + 1)..sets.len() {
                if sets[i] & sets[j] != 0 {
                    continue;
                }
                let ij = sets[i] | sets[j];
                let subsumed_ij = anchors.iter().any(|&e| sets[i] & e == 0 && sets[j] & e == 0);
                for l in (j + 1)..sets.len() {
                    if sets[l] & ij != 0 {
                        continue;
                    }
                    if subsumed_ij
                        || anchors
                            .iter()
                            .any(|&e| sets[l] & e == 0 && (sets[i] & e == 0 || sets[j] & e == 0))
                    {
                        continue;
                    }
                    cnf.add(vec![-vars[i], -vars[j], -vars[l]]);
                    ternary_clauses += 1;
                }
            }
        }
    }

    // Symmetry: lex-leader for the generators of the residual group.
    if q.symmetry {
        let mut gens: Vec<Vec<u32>> = Vec::new();
        let g = q.ground as usize;
        // adjacent transpositions inside A, inside B, and inside the tail
        let mut blocks: Vec<(usize, usize)> = vec![(0, q.m as usize)];
        if q.nu == 2 {
            blocks.push((q.m as usize, 2 * q.m as usize));
        }
        blocks.push((q.nu * q.m as usize, g));
        for (lo, hi) in blocks {
            for x in lo..hi.saturating_sub(1) {
                let mut p: Vec<u32> = (0..g as u32).collect();
                p.swap(x, x + 1);
                gens.push(p);
            }
        }
        // the swap A <-> B
        if q.nu == 2 {
            let mut p: Vec<u32> = (0..g as u32).collect();
            for x in 0..q.m as usize {
                p.swap(x, x + q.m as usize);
            }
            gens.push(p);
        }
        for p in gens {
            let img: Vec<i32> = sets
                .iter()
                .map(|&a| var_of(permute(a, &p)).expect("generator preserves the candidate set"))
                .collect();
            lex_geq(&mut cnf, &vars, &img);
        }
    }

    Instance {
        q: q.clone(),
        sets,
        vars,
        cnf,
        ternary_clauses,
        binary_clauses,
    }
}

/// Decode a raw assignment into the family it names.
pub fn decode(inst: &Instance, assign: &[bool]) -> Vec<Mask> {
    inst.sets
        .iter()
        .zip(inst.vars.iter())
        .filter(|(_, &v)| assign.get((v - 1) as usize).copied().unwrap_or(false))
        .map(|(&a, _)| a)
        .collect()
}

/// Check a decoded family against the hypotheses, sharing no code with
/// the encoder. Every SAT answer goes through this.
pub fn verify(f: &[Mask], q: &Question) -> Result<(), String> {
    if !is_uniform(q.m, f) {
        return Err(format!("not {}-uniform", q.m));
    }
    if !is_distinct(f) {
        return Err("not distinct".into());
    }
    if (f.len() as u64) <= pow_sat(q.r, q.m) {
        return Err(format!("only {} members, need > {}", f.len(), pow_sat(q.r, q.m)));
    }
    if !is_rao_spread(q.m, f, q.r, q.ground) {
        return Err(format!("not {}-spread", q.r));
    }
    if has_k_disjoint(f, q.k) {
        return Err(format!("has {} pairwise disjoint members", q.k));
    }
    Ok(())
}

/// What one question decided.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Outcome {
    /// A verified counterexample: `r` is refuted at this uniformity.
    Counterexample(Vec<Mask>),
    /// No counterexample on this ground set.
    None,
    /// Timeout, or the two solvers disagreed.
    Unknown,
}

#[derive(Debug, Clone)]
pub struct Report {
    pub q: Question,
    pub outcome: Outcome,
    pub vars: usize,
    pub clauses: usize,
    pub rounds: usize,
    pub seconds: f64,
}

impl Report {
    pub fn line(&self) -> String {
        let verdict = match &self.outcome {
            Outcome::Counterexample(f) => format!("COUNTEREXAMPLE ({} members)", f.len()),
            Outcome::None => "none".into(),
            Outcome::Unknown => "unknown".into(),
        };
        format!(
            "m={} r={} ground={} nu={} target={} | {} vars {} clauses {} rounds {:.1}s | {}",
            self.q.m,
            self.q.r,
            self.q.ground,
            self.q.nu,
            self.q.target(),
            self.vars,
            self.clauses,
            self.rounds,
            self.seconds,
            verdict
        )
    }
}

/// Every pairwise-disjoint triple in `f`, as index triples, capped.
fn violations(f: &[Mask], cap: usize) -> Vec<(usize, usize, usize)> {
    let mut out = Vec::new();
    'outer: for i in 0..f.len() {
        for j in (i + 1)..f.len() {
            if f[i] & f[j] != 0 {
                continue;
            }
            for l in (j + 1)..f.len() {
                if f[l] & (f[i] | f[j]) != 0 {
                    continue;
                }
                out.push((i, j, l));
                if out.len() >= cap {
                    break 'outer;
                }
            }
        }
    }
    out
}

/// Decide one question. UNSAT is only reported when two independent
/// solvers agree; SAT is only reported when [`verify`] accepts the model.
pub fn decide(q: &Question, seconds: u64) -> std::io::Result<Report> {
    let started = std::time::Instant::now();
    let mut inst = encode(q);
    let vars0 = inst.cnf.nvars;
    let mut rounds = 0usize;
    let outcome;
    loop {
        rounds += 1;
        let tag = format!("{}-r{}", q.tag(), rounds);
        let v = if q.ternary == Ternary::Eager {
            solve_cnf_agreed(&inst.cnf, Solver::Cadical, Solver::CryptoMiniSat, seconds, &tag)?
        } else {
            // In lazy mode only a *verified* SAT model ends the loop, so a
            // single solver is enough until the final UNSAT.
            solve_cnf(&inst.cnf, Solver::Cadical, seconds, &tag)?
        };
        match v {
            RawVerdict::Unsat => {
                if q.ternary == Ternary::Lazy {
                    // Confirm with a second solver before believing it.
                    let v2 = solve_cnf(&inst.cnf, Solver::CryptoMiniSat, seconds, &tag)?;
                    if v2 != RawVerdict::Unsat {
                        outcome = Outcome::Unknown;
                        break;
                    }
                }
                outcome = Outcome::None;
                break;
            }
            RawVerdict::Unknown => {
                outcome = Outcome::Unknown;
                break;
            }
            RawVerdict::Sat(assign) => {
                let f = decode(&inst, &assign);
                match verify(&f, q) {
                    Ok(()) => {
                        outcome = Outcome::Counterexample(f);
                        break;
                    }
                    Err(_) if q.ternary == Ternary::Lazy => {
                        let bad = violations(&f, 4096);
                        if bad.is_empty() {
                            // The model fails for a reason the loop cannot
                            // repair: an encoding bug, not a refinement.
                            outcome = Outcome::Unknown;
                            break;
                        }
                        let idx = |a: Mask| inst.sets.binary_search(&a).unwrap();
                        for (i, j, l) in bad {
                            let c = vec![
                                -inst.vars[idx(f[i])],
                                -inst.vars[idx(f[j])],
                                -inst.vars[idx(f[l])],
                            ];
                            inst.cnf.add(c);
                            inst.ternary_clauses += 1;
                        }
                    }
                    Err(e) => panic!("eager model failed verification: {e}"),
                }
            }
        }
    }
    Ok(Report {
        q: q.clone(),
        outcome,
        vars: vars0.max(inst.cnf.nvars),
        clauses: inst.cnf.clauses.len(),
        rounds,
        seconds: started.elapsed().as_secs_f64(),
    })
}

/// The elementary upper bound on `r*(m,3)` this module's structure
/// argument gives, computed rather than recalled:
/// a counterexample needs `r^2 < 2r + 3m^2 - 4m + 2` (see
/// `SpreadReduction.quadratic_spread_disjoint`), so the least `r`
/// failing that is an upper bound for `r*(m,3)`.
pub fn quadratic_bound(m: u64) -> u64 {
    let rhs = 3 * m * m - 4 * m + 2;
    let mut r = 1u64;
    while r * r < 2 * r + rhs {
        r += 1;
    }
    r
}

/// The cover bound `r*(m,3) <= 2m`, likewise computed.
pub fn cover_bound(m: u64) -> u64 {
    2 * m
}

/// The degree-sum split bound of `SpreadThreshold.split_spread_disjoint`:
/// splitting on a single member `A` gives `|F| <= m·r^(m-1)` for the part
/// meeting `A` (the `m` points of `A` cover it, and each carries at most
/// `r^(m-1)` members) plus `intersecting_piece_bound` for the part missing
/// it, so a counterexample needs `r^2 < (m+1)r + (m-1)^2`.
///
/// Asymptotically this is `m·(1+√5)/2 = φ·m` against the `√3·m` of
/// `quadratic_bound`; `split_bound_is_never_worse` pins that it dominates
/// pointwise as well.
pub fn split_bound(m: u64) -> u64 {
    let rhs = (m - 1) * (m - 1);
    let mut r = 1u64;
    while r * r < (m + 1) * r + rhs {
        r += 1;
    }
    r
}

/// The best upper bound on `r*(m,3)` the development proves: both
/// `quadratic_spread_disjoint` and `split_spread_disjoint` are theorems, so
/// the smaller of the two is available at every `m`.
pub fn best_bound(m: u64) -> u64 {
    quadratic_bound(m).min(split_bound(m))
}

/* ------------------------------------------------------------------ */
/* An exhaustive depth-first search, for the instances whose crux is
   counting rather than structure.                                      */
/* ------------------------------------------------------------------ */

/// The counting floor on the ground set: `m * |F| = sum_x deg(x) <=
/// ground * r^(m-1)`, so no counterexample fits below
/// `ceil(m * (r^m + 1) / r^(m-1))` points. At `(m,r) = (3,3)` that is 10,
/// which is exactly where §3.6's enumeration ran out.
pub fn min_ground(m: u32, r: u64) -> u32 {
    let target = pow_sat(r, m) + 1;
    let cap = pow_sat(r, m - 1);
    (((m as u64) * target).div_ceil(cap)) as u32
}

/// The largest family the degree cap allows on `ground` points:
/// `|F| <= floor(ground * r^(m-1) / m)`. Below the target there is
/// nothing to search.
pub fn degree_ceiling(m: u32, r: u64, ground: u32) -> u64 {
    (ground as u64) * pow_sat(r, m - 1) / (m as u64)
}

struct Dfs {
    m: u32,
    ground: u32,
    target: usize,
    sets: Vec<Mask>,
    /// `cap[t] = r^(m-t)` for a set of size `t`.
    cap: Vec<u64>,
    /// degree of every subset mask
    degs: Vec<u32>,
    cover: Mask,
    /// `c | d` for every disjoint pair already in `current`.
    unions: Vec<Mask>,
    current: Vec<Mask>,
    best: Vec<Mask>,
    nodes: u64,
    node_limit: u64,
    hit_limit: bool,
}

impl Dfs {
    /// Degrees only ever rise, so the bound is monotone along a branch:
    /// each further member spends `m` units of point capacity and at
    /// least one unit of *cover* capacity.
    fn slack(&self, x: u32) -> u64 {
        self.cap[1].saturating_sub(self.degs[1usize << x] as u64)
    }

    fn bound(&self, remaining: usize) -> usize {
        let total: u64 = (0..self.ground).map(|x| self.slack(x)).sum();
        let by_degree = (total / self.m as u64) as usize;
        let by_cover: u64 = (0..self.ground)
            .filter(|x| self.cover >> x & 1 == 1)
            .map(|x| self.slack(x))
            .sum();
        self.current.len() + remaining.min(by_degree).min(by_cover as usize)
    }

    fn add(&mut self, a: Mask) -> bool {
        let mut ok = true;
        let mut t = a;
        loop {
            if t != 0 {
                let d = &mut self.degs[t as usize];
                *d += 1;
                if *d as u64 > self.cap[t.count_ones() as usize] {
                    ok = false;
                }
            }
            if t == 0 {
                break;
            }
            t = (t - 1) & a;
        }
        ok
    }

    fn remove(&mut self, a: Mask) {
        let mut t = a;
        loop {
            if t != 0 {
                self.degs[t as usize] -= 1;
            }
            if t == 0 {
                break;
            }
            t = (t - 1) & a;
        }
    }

    /// Would adding `a` complete three pairwise disjoint members?
    ///
    /// `unions` carries `c | d` for every disjoint pair `{c,d}` already
    /// in the family, so the test is one mask AND per pair rather than a
    /// rescan of the family.
    fn creates_disjoint(&self, a: Mask) -> bool {
        self.unions.iter().any(|&u| u & a == 0)
    }

    /// Can `a` be added without breaking a degree cap?
    fn fits(&self, a: Mask) -> bool {
        let mut t = a;
        loop {
            if t != 0 && self.degs[t as usize] as u64 >= self.cap[t.count_ones() as usize] {
                return false;
            }
            if t == 0 {
                return true;
            }
            t = (t - 1) & a;
        }
    }

    fn push_unions(&mut self, a: Mask) -> usize {
        let before = self.unions.len();
        for i in 0..self.current.len() {
            let c = self.current[i];
            if c & a == 0 {
                self.unions.push(c | a);
            }
        }
        before
    }

    /// The candidate list is filtered at every node, so a branch only
    /// ever looks at sets that are still addable. That plus the
    /// degree-slack bound is what the SAT encoding cannot do: the
    /// counting is native here and needs an exponential resolution proof
    /// there.
    fn go(&mut self, cands: &[Mask]) {
        self.nodes += 1;
        if self.nodes > self.node_limit {
            self.hit_limit = true;
            return;
        }
        if self.current.len() > self.best.len() {
            self.best = self.current.clone();
            if self.best.len() >= self.target {
                return;
            }
        }
        for idx in 0..cands.len() {
            if self.hit_limit {
                return;
            }
            if self.bound(cands.len() - idx) < self.target {
                return;
            }
            let a = cands[idx];
            if self.creates_disjoint(a) || !self.fits(a) {
                continue;
            }
            let mark = self.push_unions(a);
            assert!(self.add(a));
            self.current.push(a);
            let next: Vec<Mask> = cands[idx + 1..]
                .iter()
                .copied()
                .filter(|&b| self.fits(b) && !self.creates_disjoint(b))
                .collect();
            self.go(&next);
            self.current.pop();
            self.remove(a);
            self.unions.truncate(mark);
        }
    }
}

/// The verdict of one exhaustive DFS.
#[derive(Debug, Clone)]
pub struct DfsReport {
    pub q: Question,
    pub outcome: Outcome,
    /// Largest family found satisfying every hypothesis but the size one.
    pub largest: usize,
    pub nodes: u64,
    pub seconds: f64,
    /// True when the node limit stopped the search: `largest` is then a
    /// lower bound and `Outcome::None` must be read as `Unknown`.
    pub truncated: bool,
}

impl DfsReport {
    pub fn line(&self) -> String {
        format!(
            "DFS m={} r={} ground={} nu={} target={} | largest={} nodes={} {:.1}s{} | {}",
            self.q.m,
            self.q.r,
            self.q.ground,
            self.q.nu,
            self.q.target(),
            self.largest,
            self.nodes,
            self.seconds,
            if self.truncated { " TRUNCATED" } else { "" },
            match &self.outcome {
                Outcome::Counterexample(f) => format!("COUNTEREXAMPLE ({} members)", f.len()),
                Outcome::None => "none".into(),
                Outcome::Unknown => "unknown".into(),
            }
        )
    }
}

/// Exhaustive search for a counterexample on `[ground]`, with the anchor
/// matching forced. Complete for families of support at most `ground`.
pub fn dfs(q: &Question, node_limit: u64) -> DfsReport {
    // `unions` tracks disjoint *pairs*, so the incremental check is
    // specific to k = 3. Nothing else here is.
    assert!(q.k == 3, "the depth-first search is specialised to k = 3");
    let started = std::time::Instant::now();
    let target = q.target() as usize;
    let cover: Mask = ((1u64 << (q.nu as u32 * q.m)) - 1) as Mask;

    // Two counting prechecks, either of which settles the question with
    // no search at all.
    if degree_ceiling(q.m, q.r, q.ground) < q.target() {
        return DfsReport {
            q: q.clone(),
            outcome: Outcome::None,
            largest: degree_ceiling(q.m, q.r, q.ground) as usize,
            nodes: 0,
            seconds: 0.0,
            truncated: false,
        };
    }

    let sets = candidates(q);
    let cap: Vec<u64> = (0..=q.ground + 1)
        .map(|t| pow_sat(q.r, q.m.saturating_sub(t)))
        .collect();
    let mut s = Dfs {
        m: q.m,
        ground: q.ground,
        target,
        sets,
        cap: cap.clone(),
        degs: vec![0; 1usize << q.ground],
        cover,
        unions: Vec::new(),
        current: Vec::new(),
        best: Vec::new(),
        nodes: 0,
        node_limit,
        hit_limit: false,
    };

    // Force the anchors, then search from the first candidate after them.
    let a_mask: Mask = ((1u64 << q.m) - 1) as Mask;
    assert!(s.add(a_mask));
    s.current.push(a_mask);
    if q.nu == 2 {
        let b_mask: Mask = a_mask << q.m;
        s.push_unions(b_mask);
        assert!(s.add(b_mask));
        s.current.push(b_mask);
    }
    let start: Vec<Mask> = s
        .sets
        .clone()
        .into_iter()
        .filter(|&b| s.fits(b) && !s.creates_disjoint(b))
        .collect();
    s.go(&start);

    let largest = s.best.len();
    let truncated = s.hit_limit;
    let outcome = if largest >= target {
        let f = s.best.clone();
        match verify(&f, q) {
            Ok(()) => Outcome::Counterexample(f),
            Err(e) => panic!("dfs produced an invalid family: {e}"),
        }
    } else if truncated {
        Outcome::Unknown
    } else {
        Outcome::None
    };
    DfsReport {
        q: q.clone(),
        outcome,
        largest,
        nodes: s.nodes,
        seconds: started.elapsed().as_secs_f64(),
        truncated,
    }
}
