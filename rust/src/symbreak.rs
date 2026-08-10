//! Degree-ordered symmetry breaking for the intersecting question, and
//! the cube split that goes with it.
//!
//! `docs/roadmap.md` §9 diagnosed the wall and named the fix in the same
//! paragraph: the intersecting instances are *tiny* — `C(11,4) = 330`
//! booleans — and hard, which is the signature of symmetry, and the
//! stabiliser of the forced anchor still has order `b! (g-b)!`. §9's
//! "named next step" was to spend that stabiliser on a **sorted degree
//! sequence**. This module is that step, plus one more turn of the same
//! screw that §9 did not name.
//!
//! # What is sound, and why
//!
//! Let `F` be a non-empty intersecting `b`-uniform family on `[g]`.
//! Relabelling the ground set preserves uniformity, distinctness,
//! intersecting-ness and sunflower-freeness (`DirectSum.relabel_preserves`
//! is the theorem), so `F` may be replaced by any relabelling of itself.
//! Choose one as follows.
//!
//! 1. Let `z` be a point of **maximum degree**. It has degree at least
//!    one, so some member contains it; call that member `A`. Send `z` to
//!    `0` and the rest of `A` to `1..b`. So `A = {0,...,b-1}` is a
//!    member — the anchor the old encoding already forced — and *in
//!    addition* `deg(0) >= deg(y)` for every point `y`.
//! 2. What is left of the relabelling freedom is
//!    `Sym({1,...,b-1}) x Sym({b,...,g-1})`, which fixes `0` and fixes
//!    `A` setwise. Use it to sort each block by degree:
//!    `deg(1) >= ... >= deg(b-1)` and `deg(b) >= ... >= deg(g-1)`.
//!
//! Both steps are available simultaneously — step 2 moves nothing step 1
//! constrained — so a family with at least one member may be assumed to
//! satisfy all of it. Nothing here is implied by the clauses already in
//! the encoding, which is what separates it from the degree cap §9
//! measured and found worthless: that one was a *consequence* of the
//! ternary clauses, and a clause learner derives its own consequences.
//!
//! One more, and it is not a symmetry argument. Every member of an
//! intersecting family meets `A`, so
//! `sum_{x in A} deg(x) = sum_{B in F} |B ∩ A| >= |F|`, and the maximum
//! over `A` is at most the maximum over everything:
//!
//! ```text
//!     deg(0)  >=  ceil(|F| / b)
//! ```
//!
//! At `(b, |F|) = (4, 32)` that is `deg(0) >= 8`, and it is the floor the
//! cube split starts from.
//!
//! # The cube split
//!
//! `deg(0)` is now pinned between that floor and the counter's ceiling,
//! and the cases are disjoint, so
//!
//! ```text
//!     cube_d  :=  deg(0) >= d  /\  ~(deg(0) >= d+1)
//! ```
//!
//! partitions the search space into independent instances that can be run
//! on separate cores and reported as they land. The top cube is
//! `deg(0) >= kmax` with no upper half, so the split stays a cover even
//! though the counter saturates.
//!
//! # What the counters do and do not assert
//!
//! `order_counter` encodes "at least `k` of these literals" in **both**
//! directions, so a comparison between two points is a real constraint
//! rather than a one-way hint. It **saturates** at `kmax` rather than
//! asserting `deg(x) <= kmax`: at saturation two degrees become
//! incomparable and the ordering constraint simply stops biting. That is
//! a loss of pruning and never a loss of solutions, so no proved bound on
//! the maximum degree is being relied on here. `kmax` is a performance
//! knob, not a hypothesis.

use crate::ground::m_subsets;
use crate::sat::{Cnf, Solver};

/// An encoded instance, with the degree literals kept so that a caller
/// can build cubes out of them.
#[derive(Debug, Clone)]
pub struct SymInstance {
    /// The candidate `b`-sets, in variable order. The anchor is *not*
    /// among them; it is forced.
    pub sets: Vec<u32>,
    /// `vars[i]` is the DIMACS variable for `sets[i]`.
    pub vars: Vec<i32>,
    pub cnf: Cnf,
    /// `deg_ge[x][k-1]` is a literal equivalent to "`deg(x) >= k`", for
    /// `1 <= k <= kmax`, with the anchor's own contribution folded in.
    pub deg_ge: Vec<Vec<i32>>,
    pub ground: u32,
    pub b: u32,
    pub target: usize,
    pub kmax: usize,
    /// The least value of `deg(0)` the encoding rules in. It is the
    /// intersecting floor when [`SymOptions::degree_floor`] is on and 1
    /// when it is off — and it is stored rather than recomputed because
    /// [`degree_cubes`] must start where the encoding does or the split
    /// stops being a cover.
    pub floor: usize,
}

/// Which of the sound restrictions to switch on. All default to on; the
/// point of the switches is that `sat_symbreak.rs` can turn each off and
/// check the answer does not move.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SymOptions {
    /// `deg(0) >= deg(y)` for every point `y`.
    pub max_at_zero: bool,
    /// `deg(1) >= ... >= deg(b-1)` and `deg(b) >= ... >= deg(g-1)`.
    pub sorted_blocks: bool,
    /// `deg(0) >= max(ceil(target/b), ceil(b*target/ground))`, from the
    /// intersecting hypothesis and from the incidence count.
    pub degree_floor: bool,
    /// Ask for **exactly** `target` members rather than at least.
    ///
    /// Sound because everything in the question passes to subfamilies:
    /// a family of `t' > t` members contains one of exactly `t`. It
    /// pins the incidence count `sum_x deg(x) = b*t` rather than
    /// bounding it, which is what makes the degree floor sharp.
    pub exact_size: bool,
    /// Require every point of `[ground]` to lie in some member.
    ///
    /// **This one is conditional**, and it is the only option here that
    /// is not sound on its own: a family using at most `ground-1` points
    /// is a family on `ground-1` points, so switching this on asks a
    /// strictly smaller question and is legitimate only once the same
    /// target has come back UNSAT at `ground-1`. `examples/iota_sym.rs`
    /// runs the ladder from the bottom for exactly that reason.
    pub all_points_used: bool,
    /// Lexicographic tie-breaking between adjacent points of equal
    /// degree.
    ///
    /// Sorting by degree spends the stabiliser only down to the
    /// *equal-degree runs*, and at the parameters that matter the
    /// extremal candidates are nearly regular — at `(b,g,t) = (4,10,32)`
    /// the incidence count forces every degree into `{11,12,13}` — so
    /// almost all of the group survives the sort. This spends the rest
    /// of it, one adjacent transposition at a time.
    ///
    /// Let `H` be the subgroup of `Sym({1..b-1}) x Sym({b..g-1})` that
    /// preserves the degree sequence: a product of symmetric groups, one
    /// per equal-degree run, generated by the adjacent transpositions
    /// *within* runs. Take the lexicographically largest family in the
    /// `H`-orbit. It still has the anchor, still has `deg(0)` maximal,
    /// still has sorted degrees — `H` moves none of that — and it
    /// satisfies `F >=_lex (p q)F` for every adjacent `p, q` with
    /// `deg(p) = deg(q)`. That conjunction is what is encoded.
    ///
    /// **It forces `kmax >= target`.** The equality test is read off the
    /// degree literals, and a *saturated* counter cannot tell two
    /// degrees apart — which would impose a lex constraint between
    /// points of different degree, and that is unsound rather than
    /// merely weak. A point lies in at most `|F| = target` members, so
    /// `kmax = target` makes the counters exact and the test faithful.
    pub lex_ties: bool,
    /// Ceiling of the degree counters. Pruning only unless `lex_ties` is
    /// on, which raises it to `target`; see the module note.
    pub kmax: usize,
}

impl Default for SymOptions {
    fn default() -> Self {
        SymOptions {
            max_at_zero: true,
            sorted_blocks: true,
            degree_floor: true,
            exact_size: true,
            all_points_used: false,
            lex_ties: true,
            kmax: 24,
        }
    }
}

/// Do `a`, `b`, `c` form a 3-sunflower?
#[inline]
fn is_sunflower(a: u32, b: u32, c: u32) -> bool {
    let ab = a & b;
    ab == (a & c) && ab == (b & c)
}

/// The image of a set under the transposition `(p q)`.
#[inline]
pub fn swap_points(s: u32, p: u32, q: u32) -> u32 {
    let hp = s >> p & 1;
    let hq = s >> q & 1;
    if hp == hq {
        return s;
    }
    (s & !(1 << p) & !(1 << q)) | (hq << p) | (hp << q)
}

/// "At least `k` of `lits`", for every `k` in `1..=kmax`, encoded in both
/// directions and saturating at `kmax`.
///
/// `s[i][k]` reads "at least `k` of the first `i` literals" and satisfies
/// `s[i][k] <-> s[i-1][k] \/ (x_i /\ s[i-1][k-1])`, with `s[i][0]` true
/// and `s[i][k]` false for `k > i`. Both implications are emitted, which
/// is what a *comparison* needs: a one-directional counter lets the
/// solver leave an output false and dodge the constraint.
fn order_counter(cnf: &mut Cnf, lits: &[i32], kmax: usize) -> Vec<i32> {
    let n = lits.len();
    let kmax = kmax.min(n);
    if kmax == 0 {
        return Vec::new();
    }
    // s[i] holds the outputs for i literals; s[i][k-1] is "at least k".
    let mut s: Vec<Vec<i32>> = Vec::with_capacity(n + 1);
    s.push(Vec::new());
    for i in 1..=n {
        let jmax = i.min(kmax);
        let row: Vec<i32> = (0..jmax).map(|_| cnf.new_var()).collect();
        s.push(row);
    }
    for i in 1..=n {
        let jmax = i.min(kmax);
        for k in 1..=jmax {
            let sik = s[i][k - 1];
            // s[i-1][k], present only when k <= i-1.
            let prev = if k <= s[i - 1].len() {
                Some(s[i - 1][k - 1])
            } else {
                None
            };
            // ==>  s[i][k] -> s[i-1][k] \/ x_i
            let mut cl = vec![-sik];
            if let Some(p) = prev {
                cl.push(p);
            }
            cl.push(lits[i - 1]);
            cnf.add(cl);
            // ==>  s[i][k] -> s[i-1][k] \/ s[i-1][k-1]; vacuous at k = 1,
            // where s[i-1][0] is true.
            if k >= 2 {
                let mut cl = vec![-sik];
                if let Some(p) = prev {
                    cl.push(p);
                }
                cl.push(s[i - 1][k - 2]);
                cnf.add(cl);
            }
            // <==  s[i-1][k] -> s[i][k]
            if let Some(p) = prev {
                cnf.add(vec![-p, sik]);
            }
            // <==  x_i /\ s[i-1][k-1] -> s[i][k]
            if k >= 2 {
                cnf.add(vec![-lits[i - 1], -s[i - 1][k - 2], sik]);
            } else {
                cnf.add(vec![-lits[i - 1], sik]);
            }
        }
    }
    s[n].clone()
}

/// The counter, exposed so that `tests/symbreak.rs` can check it against
/// a brute-force count. It is the one piece of this module whose
/// failure mode is silent: a counter that is only a one-way implication
/// still compiles, still solves, and turns every degree comparison into
/// a no-op.
pub fn order_counter_for_tests(cnf: &mut Cnf, lits: &[i32], kmax: usize) -> Vec<i32> {
    order_counter(cnf, lits, kmax)
}

/// Encode "is there an intersecting `b`-uniform 3-sunflower-free family
/// of at least `target` members on `[ground]`?", with the anchor forced
/// and the degree order broken as the module note describes.
pub fn encode(ground: u32, b: u32, target: usize, opts: SymOptions) -> SymInstance {
    assert!(ground >= b, "ground set smaller than the uniformity");
    assert!(target >= 1, "the anchor makes target 0 trivial");
    assert!(ground <= 32, "the bitmask representation stops at 32 points");
    let anchor: u32 = (1u32 << b) - 1;

    let sets: Vec<u32> = m_subsets(ground, b)
        .into_iter()
        .map(u32::from)
        .filter(|s| *s != anchor && s & anchor != 0)
        .collect();
    let mut cnf = Cnf::new();
    let vars: Vec<i32> = sets.iter().map(|_| cnf.new_var()).collect();

    // A literal that is always true, so that "deg(x) >= k" can be a
    // constant for the anchor's own points at small k.
    let top = cnf.new_var();
    cnf.add(vec![top]);

    // Intersecting: binary clauses, one per disjoint pair.
    for i in 0..sets.len() {
        for j in (i + 1)..sets.len() {
            if sets[i] & sets[j] == 0 {
                cnf.add(vec![-vars[i], -vars[j]]);
            }
        }
    }

    // Sunflower-free: binary against the forced anchor, ternary otherwise.
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

    // At least `target` members, one of which is the anchor -- and, when
    // asked, at most that many too.
    cnf.at_least(&vars, target - 1);
    if opts.exact_size {
        cnf.at_most(&vars, target - 1);
    }

    // Degree counters, with the anchor's contribution folded in. The
    // ceiling is raised to the floor when it would otherwise sit below
    // it: a floor past the ceiling cannot be asserted, and a cube list
    // that starts past its ceiling would be *empty*, which `decide`
    // would read as "every cube came back UNSAT".
    let floor = if opts.degree_floor {
        // Every member meets the anchor, so the anchor's b degrees sum
        // to at least |F|; and every member has b points, so all g
        // degrees sum to exactly b|F|. The maximum degree beats both
        // averages, and point 0 carries the maximum.
        target
            .div_ceil(b as usize)
            .max((b as usize * target).div_ceil(ground as usize))
            .max(1)
    } else {
        1
    };
    let kmax = if opts.lex_ties {
        opts.kmax.max(target)
    } else {
        opts.kmax
    }
    .max(floor)
    .max(1);
    let mut deg_ge: Vec<Vec<i32>> = Vec::with_capacity(ground as usize);
    for x in 0..ground {
        let lits: Vec<i32> = sets
            .iter()
            .zip(vars.iter())
            .filter(|(s, _)| *s >> x & 1 == 1)
            .map(|(_, v)| *v)
            .collect();
        let cnt = order_counter(&mut cnf, &lits, kmax);
        let off = usize::from(anchor >> x & 1 == 1);
        let row: Vec<i32> = (1..=kmax)
            .map(|k| {
                if k <= off {
                    top
                } else if k - off <= cnt.len() {
                    cnt[k - off - 1]
                } else {
                    -top
                }
            })
            .collect();
        deg_ge.push(row);
    }

    // deg(0) >= deg(y) for every y.
    if opts.max_at_zero {
        for y in 1..ground as usize {
            for k in 0..kmax {
                cnf.add(vec![-deg_ge[y][k], deg_ge[0][k]]);
            }
        }
    }

    // Sorted inside the anchor, and sorted outside it.
    if opts.sorted_blocks {
        let mut chains: Vec<Vec<usize>> = Vec::new();
        chains.push((1..b as usize).collect());
        chains.push((b as usize..ground as usize).collect());
        for chain in chains {
            for w in chain.windows(2) {
                for k in 0..kmax {
                    cnf.add(vec![-deg_ge[w[1]][k], deg_ge[w[0]][k]]);
                }
            }
        }
    }

    // deg(0) >= the floor above.
    if opts.degree_floor && floor >= 1 {
        cnf.add(vec![deg_ge[0][floor - 1]]);
    }

    // Lexicographic tie-breaking on adjacent equal-degree points.
    if opts.lex_ties {
        let index: std::collections::HashMap<u32, usize> =
            sets.iter().enumerate().map(|(i, s)| (*s, i)).collect();
        let mut chains: Vec<Vec<usize>> = Vec::new();
        chains.push((1..b as usize).collect());
        chains.push((b as usize..ground as usize).collect());
        for chain in chains {
            for w in chain.windows(2) {
                let (p, q) = (w[0], w[1]);
                // `same` holds exactly when deg(p) = deg(q). Sorting
                // already gives deg(p) >= deg(q), so inequality is
                // witnessed by some level p has and q does not.
                let same = cnf.new_var();
                let mut witness = vec![same];
                for k in 0..kmax {
                    // same -> not a witness at level k
                    cnf.add(vec![-same, -deg_ge[p][k], deg_ge[q][k]]);
                    let d = cnf.new_var();
                    cnf.add(vec![-d, deg_ge[p][k]]);
                    cnf.add(vec![-d, -deg_ge[q][k]]);
                    witness.push(d);
                }
                // Not the same => some level witnesses it.
                cnf.add(witness);
                // same -> F >=_lex (p q)F, over the candidate sets in
                // their fixed order. The transposition maps candidates
                // to candidates: it fixes the anchor setwise, so it
                // preserves "meets the anchor".
                let mut eq = top;
                for i in 0..sets.len() {
                    let img = swap_points(sets[i], p as u32, q as u32);
                    let j = index[&img];
                    let (x, y) = (vars[i], vars[j]);
                    // eq /\ y -> x
                    cnf.add(vec![-same, -eq, -y, x]);
                    if i + 1 < sets.len() {
                        let next = cnf.new_var();
                        // eq /\ (x <-> y) -> next
                        cnf.add(vec![-eq, -x, -y, next]);
                        cnf.add(vec![-eq, x, y, next]);
                        eq = next;
                    }
                }
            }
        }
    }

    // Every point used. Conditional: see `SymOptions::all_points_used`.
    // With `sorted_blocks` on, the last point of each block implies the
    // rest of its block, but the clause is emitted for every point so
    // that the two options stay independent.
    if opts.all_points_used {
        for x in 0..ground as usize {
            cnf.add(vec![deg_ge[x][0]]);
        }
    }

    SymInstance {
        sets,
        vars,
        cnf,
        deg_ge,
        ground,
        b,
        target,
        kmax,
        floor,
    }
}

/// The disjoint cubes on `deg(0)`, from the floor to the counter's
/// ceiling. Each is a list of unit literals to append to the CNF; the
/// union of the cubes covers every model, so a verdict is UNSAT exactly
/// when every cube is.
pub fn degree_cubes(inst: &SymInstance) -> Vec<(usize, Vec<i32>)> {
    let mut out = Vec::new();
    for d in inst.floor..=inst.kmax {
        let mut lits = vec![inst.deg_ge[0][d - 1]];
        if d < inst.kmax {
            lits.push(-inst.deg_ge[0][d]);
        }
        out.push((d, lits));
    }
    out
}

/// Every degree sequence the encoding admits, as an exact cube each.
///
/// The `deg(0)` split leaves the near-regular cases in one lump, and at
/// the parameters that matter that lump is the whole problem: with
/// `exact_size` on, `sum_x deg(x) = b*t` exactly, so at
/// `(b,g,t) = (4,10,32)` and `deg(0) = 13` the ten degrees sum to 128
/// against a ceiling of 130 — a total deficiency of **two**, and the
/// sortedness inside the two blocks then leaves five sequences. Splitting
/// on them turns one hard instance into five, in parallel, each with its
/// degree vector pinned.
///
/// The enumeration is exactly the constraint set the encoding asserts —
/// `d_0` maximal, each block non-increasing, `sum = b*t`, and `d_x >= 1`
/// when `all_points_used` is on — so the cubes partition the models.
/// `d0s` restricts the enumeration to those values of `deg(0)`; an empty
/// slice means all of them. **Restricting matters**: the sequences for a
/// large `deg(0)` are numerous — the deficiency `g*deg(0) - b*t` is what
/// gets partitioned, and it grows linearly in `deg(0)` — while the
/// sequences for the *smallest* `deg(0)`, which is where the near-regular
/// families live and where the solver stalls, are a handful. Asking for
/// all of them at once overflows `cap` at every parameter that matters.
///
/// It returns `None` when a hypothesis it needs is switched off, or when
/// the enumeration exceeds `cap`; the caller then falls back to
/// [`degree_cubes`], which needs less.
pub fn sequence_cubes(
    inst: &SymInstance,
    opts: SymOptions,
    d0s: &[usize],
    prefix: usize,
    cap: usize,
) -> Option<Vec<(Vec<usize>, Vec<i32>)>> {
    if !(opts.exact_size && opts.max_at_zero && opts.sorted_blocks) {
        return None;
    }
    let g = inst.ground as usize;
    let b = inst.b as usize;
    let total = b * inst.target;
    let lo = usize::from(opts.all_points_used);
    let prefix = prefix.clamp(1, g);
    let mut out: Vec<Vec<usize>> = Vec::new();

    // A block is a non-increasing run; `fill` walks the whole sequence
    // left to right, resetting the ceiling at the block boundary.
    // The most the positions from `pos` on can carry, given that the one
    // before them was `prev` and the block boundary is at `b`.
    fn most_from(pos: usize, g: usize, b: usize, top: usize, prev: usize) -> usize {
        if pos >= g {
            0
        } else if pos < b {
            (b - pos) * prev + (g - b) * top
        } else {
            (g - pos) * prev.min(top)
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn fill(
        pos: usize,
        g: usize,
        b: usize,
        top: usize,
        prev: usize,
        left: usize,
        lo: usize,
        prefix: usize,
        cur: &mut Vec<usize>,
        out: &mut Vec<Vec<usize>>,
        cap: usize,
    ) -> bool {
        if out.len() > cap {
            return false;
        }
        if pos == prefix {
            // The rest is left free; it only has to be *fillable*.
            let rest = g - pos;
            let ceiling = if pos == b { top } else { prev };
            if left >= rest * lo && left <= most_from(pos, g, b, top, ceiling) {
                out.push(cur.clone());
            }
            return true;
        }
        // At the start of the second block the chain restarts at `top`.
        let ceiling = if pos == b { top } else { prev };
        for d in (lo..=ceiling).rev() {
            if d > left {
                continue;
            }
            let next_ceiling = if pos + 1 == b { top } else { d };
            let most = most_from(pos + 1, g, b, top, next_ceiling);
            let rest = g - pos - 1;
            if left - d > most || left - d < rest * lo {
                continue;
            }
            cur.push(d);
            let ok = fill(pos + 1, g, b, top, d, left - d, lo, prefix, cur, out, cap);
            cur.pop();
            if !ok {
                return false;
            }
        }
        true
    }

    for d0 in inst.floor..=inst.kmax.min(total) {
        if !d0s.is_empty() && !d0s.contains(&d0) {
            continue;
        }
        let mut cur = vec![d0];
        if prefix == 1 {
            out.push(cur.clone());
            continue;
        }
        if !fill(1, g, b, d0, d0, total - d0, lo, prefix, &mut cur, &mut out, cap) {
            return None;
        }
    }
    if out.len() > cap {
        return None;
    }
    Some(
        out.into_iter()
            .map(|seq| {
                let mut lits = Vec::with_capacity(2 * seq.len());
                for (x, d) in seq.iter().enumerate() {
                    if *d >= 1 {
                        lits.push(inst.deg_ge[x][*d - 1]);
                    }
                    if *d < inst.kmax {
                        lits.push(-inst.deg_ge[x][*d]);
                    }
                }
                (seq, lits)
            })
            .collect(),
    )
}

/// Decode a satisfying assignment into a family, anchor included.
pub fn decode(inst: &SymInstance, assign: &[bool]) -> Vec<u32> {
    let anchor: u32 = (1u32 << inst.b) - 1;
    let mut fam = vec![anchor];
    for (i, v) in inst.vars.iter().enumerate() {
        let idx = (*v as usize) - 1;
        if idx < assign.len() && assign[idx] {
            fam.push(inst.sets[i]);
        }
    }
    fam
}

/// Solve one cube. The model, if any, is decoded and handed to
/// `intersecting::verify`, which shares no code with this encoder.
pub fn solve_cube(
    inst: &SymInstance,
    cube: &[i32],
    solver: Solver,
    seconds: u64,
    tag: &str,
) -> std::io::Result<crate::sat::Verdict> {
    let mut cnf = inst.cnf.clone();
    for l in cube {
        cnf.add(vec![*l]);
    }
    match crate::sat::solve_cnf(&cnf, solver, seconds, tag)? {
        crate::sat::RawVerdict::Unsat => Ok(crate::sat::Verdict::Unsat),
        crate::sat::RawVerdict::Unknown => Ok(crate::sat::Verdict::Unknown),
        crate::sat::RawVerdict::Sat(a) => {
            let fam = decode(inst, &a);
            crate::intersecting::verify(&fam, inst.b, true)
                .unwrap_or_else(|e| panic!("{} returned a bad model: {e}", solver.binary()));
            assert!(
                fam.len() >= inst.target,
                "{} returned a model of size {} below the target {}",
                solver.binary(),
                fam.len(),
                inst.target
            );
            Ok(crate::sat::Verdict::Sat(fam))
        }
    }
}

/// The same question in one instance, with no cube split. Kept so that
/// `tests/symbreak.rs` can check the split answers what it splits.
pub fn decide_whole(
    ground: u32,
    b: u32,
    target: usize,
    opts: SymOptions,
    solver: Solver,
    seconds: u64,
) -> std::io::Result<crate::sat::Verdict> {
    let inst = encode(ground, b, target, opts);
    let tag = format!("whole-{ground}-{b}-{target}");
    solve_cube(&inst, &[], solver, seconds, &tag)
}

/// The whole question, cube by cube, sequentially. `examples/iota_sym.rs`
/// is the parallel driver; this is the one the tests use.
pub fn decide(
    ground: u32,
    b: u32,
    target: usize,
    opts: SymOptions,
    solver: Solver,
    seconds: u64,
) -> std::io::Result<crate::sat::Verdict> {
    let inst = encode(ground, b, target, opts);
    let mut any_unknown = false;
    for (d, cube) in degree_cubes(&inst) {
        let tag = format!("sym-{ground}-{b}-{target}-{d}");
        match solve_cube(&inst, &cube, solver, seconds, &tag)? {
            crate::sat::Verdict::Sat(f) => return Ok(crate::sat::Verdict::Sat(f)),
            crate::sat::Verdict::Unsat => {}
            crate::sat::Verdict::Unknown => any_unknown = true,
        }
    }
    Ok(if any_unknown {
        crate::sat::Verdict::Unknown
    } else {
        crate::sat::Verdict::Unsat
    })
}
