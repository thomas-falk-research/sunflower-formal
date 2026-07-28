//! Exhaustive falsification testbed for the spread hypothesis.
//!
//! The one axiom of the Coq development, `ALWZ.Rao20_lemma2`, has the
//! shape of `SpreadReduction.SpreadYieldsDisjoint n k r`:
//!
//! > every `r`-spread `m`-uniform family (`1 <= m <= n`) of more than
//! > `r^m` distinct sets contains `k` pairwise disjoint members.
//!
//! Nothing in the kernel can tell whether that statement says what
//! Rao's Lemma 2 says. What *can* be checked is whether it is true at
//! small parameters: enumerate every family of `m`-subsets of a ground
//! set of size `ground`, keep the ones satisfying all the hypotheses,
//! and ask whether each really does have `k` pairwise disjoint
//! members. A misstatement that makes the hypothesis weaker than
//! intended — a dropped `NoDup`, an exponent off by one, a `<` that
//! should be `<=` — shows up here as a counterexample at parameters
//! where the true lemma has plenty of room.
//!
//! What the search proves and what it does not: it is complete for
//! families drawn from the given ground set, and says nothing about
//! larger ones. That is the right trade. Counterexamples to a
//! misstated finite combinatorial hypothesis are small; the published
//! lemma's own threshold is `Theta(k log(km))`, so any statement error
//! large enough to matter shows up well within reach.
//!
//! # Structure of the search
//!
//! Both constraints that define a counterexample are *hereditary*:
//!
//! * `RaoSpread m F r` — degrees only grow when members are added, so
//!   once violated it stays violated;
//! * "no `k` pairwise disjoint members" — likewise monotone.
//!
//! So the families satisfying both form a downward-closed set, and a
//! depth-first search that adds members in increasing index order and
//! backtracks the moment either constraint breaks visits exactly that
//! set, with no wasted nodes. The remaining hypothesis, `r^m < |F|`,
//! is upward closed, so it becomes the target: a counterexample is a
//! family in the search tree with more than `r^m` members.

use crate::spread::{
    family_to_coq, has_k_disjoint, is_fractionally_spread, is_rao_spread, mask_to_set, pow_sat,
    rao_witness_cands, rao_witness_ground, subsets_of_size, Mask,
};

/// The outcome of one exhaustive search at fixed `(ground, m, k, r)`.
#[derive(Debug, Clone)]
pub struct SearchOutcome {
    pub ground: u32,
    pub m: u32,
    pub k: usize,
    pub r: u64,
    /// `r^m` — the size a family must exceed to be a counterexample.
    pub threshold: u64,
    /// The largest family found that is `r`-spread and has fewer than
    /// `k` pairwise disjoint members.
    pub largest: Vec<Mask>,
    /// Search tree nodes visited.
    pub nodes: u64,
}

impl SearchOutcome {
    /// A counterexample exists exactly when the largest such family
    /// also clears the size hypothesis.
    pub fn is_counterexample(&self) -> bool {
        self.largest.len() as u64 > self.threshold
    }
}

struct Search {
    sets: Vec<Mask>,
    ground: u32,
    m: u32,
    k: usize,
    /// `cap[t] = r^(m - t)`, the degree bound for a set of size `t`.
    cap: Vec<u64>,
    /// `deg[t]` for every subset mask `t` of the ground set.
    degs: Vec<u32>,
    /// Degrees of the singletons, kept separately for the counting bound.
    vertex_deg: Vec<u32>,
    current: Vec<Mask>,
    best: Vec<Mask>,
    nodes: u64,
}

impl Search {
    fn new(ground: u32, m: u32, k: usize, r: u64) -> Self {
        let cap: Vec<u64> = (0..=ground + 1).map(|t| pow_sat(r, m.saturating_sub(t))).collect();
        Search {
            sets: subsets_of_size(ground, m),
            ground,
            m,
            k,
            cap,
            degs: vec![0; 1usize << ground],
            vertex_deg: vec![0; ground as usize],
            current: Vec::new(),
            best: Vec::new(),
            nodes: 0,
        }
    }

    /// Add `a`, bumping the degree of every nonempty subset of it.
    /// Returns `false` (having undone nothing yet — the caller always
    /// removes) if some degree exceeded its cap.
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
        for v in 0..self.ground {
            if a >> v & 1 == 1 {
                self.vertex_deg[v as usize] += 1;
            }
        }
        self.current.push(a);
        ok
    }

    fn remove(&mut self, a: Mask) {
        self.current.pop();
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
        for v in 0..self.ground {
            if a >> v & 1 == 1 {
                self.vertex_deg[v as usize] -= 1;
            }
        }
    }

    /// How many further members the vertex-degree caps still allow.
    /// Each member uses `m` vertex slots and each vertex has at most
    /// `cap[1] = r^(m-1)` of them, so `sum_v (cap1 - deg v) / m` is an
    /// upper bound on the number of additions still possible.
    fn slack(&self) -> usize {
        let cap1 = self.cap[1];
        let total: u64 = self
            .vertex_deg
            .iter()
            .map(|&d| cap1.saturating_sub(d as u64))
            .sum();
        (total / self.m as u64) as usize
    }

    /// Would adding `a` create `k` pairwise disjoint members? Any new
    /// such collection must contain `a`, so it suffices to look for
    /// `k-1` pairwise disjoint members among those already chosen that
    /// avoid `a`.
    fn creates_k_disjoint(&self, a: Mask) -> bool {
        fn go(f: &[Mask], used: Mask, need: usize) -> bool {
            if need == 0 {
                return true;
            }
            for i in 0..f.len() {
                if f[i] & used == 0 && go(&f[i + 1..], used | f[i], need - 1) {
                    return true;
                }
            }
            false
        }
        if self.k == 0 {
            return true;
        }
        go(&self.current, a, self.k - 1)
    }

    fn dfs(&mut self, start: usize, target: usize, stop_early: bool) {
        self.nodes += 1;
        if self.current.len() > self.best.len() {
            self.best = self.current.clone();
        }
        if stop_early && self.best.len() > target {
            return;
        }
        for i in start..self.sets.len() {
            // Can the branch still beat what we have?
            let reachable = self.current.len()
                + std::cmp::min(self.sets.len() - i, self.slack());
            if reachable <= self.best.len() || (stop_early && reachable <= target) {
                return;
            }
            let a = self.sets[i];
            if self.creates_k_disjoint(a) {
                continue;
            }
            if self.add(a) {
                self.dfs(i + 1, target, stop_early);
                if stop_early && self.best.len() > target {
                    self.remove(a);
                    return;
                }
            }
            self.remove(a);
        }
    }
}

/// Exhaustively search for the largest `r`-spread family of
/// `m`-subsets of `{0..ground-1}` with fewer than `k` pairwise
/// disjoint members.
///
/// `stop_early` returns as soon as the size hypothesis `r^m < |F|` is
/// cleared; that is all the pass/fail gates need, and it is much
/// faster. Pass `false` to get the true maximum, which the reported
/// tables use.
pub fn search(ground: u32, m: u32, k: usize, r: u64, stop_early: bool) -> SearchOutcome {
    assert!(ground <= 20, "ground set too large for a 2^ground degree table");
    let threshold = pow_sat(r, m);
    let mut s = Search::new(ground, m, k, r);
    let target = std::cmp::min(threshold, usize::MAX as u64) as usize;
    s.dfs(0, target, stop_early);
    SearchOutcome {
        ground,
        m,
        k,
        r,
        threshold,
        largest: s.best.clone(),
        nodes: s.nodes,
    }
}

/// A counterexample to `SpreadYieldsDisjoint` at these parameters, if
/// one exists within the ground set.
pub fn find_counterexample(ground: u32, m: u32, k: usize, r: u64) -> Option<Vec<Mask>> {
    let out = search(ground, m, k, r, true);
    if out.is_counterexample() {
        Some(out.largest)
    } else {
        None
    }
}

/// Re-check a claimed counterexample against every hypothesis, using
/// the definitions in `spread.rs` directly rather than the incremental
/// state the search maintains. A search bug that mis-tracked degrees
/// would be caught here.
pub fn verify_counterexample(f: &[Mask], ground: u32, m: u32, k: usize, r: u64) -> Result<(), String> {
    if !crate::spread::is_uniform(m, f) {
        return Err(format!("not {}-uniform: {}", m, family_to_coq(f)));
    }
    if !crate::spread::is_distinct(f) {
        return Err(format!("not distinct: {}", family_to_coq(f)));
    }
    if (f.len() as u64) <= pow_sat(r, m) {
        return Err(format!(
            "size hypothesis fails: |F| = {} is not > r^m = {}",
            f.len(),
            pow_sat(r, m)
        ));
    }
    if !is_rao_spread(m, f, r, ground) {
        return Err(format!("not {}-spread: {}", r, family_to_coq(f)));
    }
    if has_k_disjoint(f, k) {
        return Err(format!("conclusion holds after all: {}", family_to_coq(f)));
    }
    Ok(())
}

/// The largest `r` at which a counterexample exists, plus one: the
/// empirical threshold at which the spread hypothesis becomes true
/// over this ground set. `r` is scanned up to the point where the size
/// hypothesis `r^m < C(ground, m)` becomes unsatisfiable, beyond which
/// no counterexample can exist for trivial reasons.
pub fn empirical_threshold(ground: u32, m: u32, k: usize) -> (u64, Vec<u64>) {
    let total = subsets_of_size(ground, m).len() as u64;
    let mut failing = Vec::new();
    let mut r = 1u64;
    while pow_sat(r, m) < total {
        if find_counterexample(ground, m, k, r).is_some() {
            failing.push(r);
        }
        r += 1;
    }
    let threshold = failing.iter().copied().max().map(|x| x + 1).unwrap_or(1);
    (threshold, failing)
}

/// Every subset `T` of the ground set, as a sanity cross-check that
/// `deg` agrees with a naive count over the element lists.
pub fn deg_naive(t: Mask, f: &[Mask]) -> usize {
    let t_elts = mask_to_set(t);
    f.iter()
        .filter(|&&a| {
            let a_elts = mask_to_set(a);
            t_elts.iter().all(|x| a_elts.contains(x))
        })
        .count()
}

/// Differential check of the two spread decision procedures on one
/// family: `Spread.rao_witness` (member sublists) against
/// `Reflect.rao_spreadb` (ground-set subsets). The Coq theorem
/// `Reflect.rao_witness_agrees` says these always agree; this is the
/// same claim, checked by evaluation over an exhaustive enumeration.
pub fn witnesses_agree(m: u32, f: &[Mask], r: u64, ground: u32) -> bool {
    rao_witness_cands(m, f, r).is_some() == rao_witness_ground(m, f, r, ground).is_some()
}

/// `Spread.RaoSpread_Spread`: Rao's absolute condition together with
/// the size hypothesis implies the fractional (ALWZ / FKNP) one.
/// Returns `Ok(())` if the implication holds on this family.
pub fn rao_implies_fractional(m: u32, f: &[Mask], r: u64, ground: u32) -> Result<(), String> {
    if is_rao_spread(m, f, r, ground) && (f.len() as u64) > pow_sat(r, m) {
        if !is_fractionally_spread(f, r, ground) {
            return Err(format!(
                "RaoSpread_Spread refuted at r = {} on {}",
                r,
                family_to_coq(f)
            ));
        }
    }
    Ok(())
}

/// Enumerate *all* families over a ground set — not just the ones the
/// pruned search visits — for the small parameters where that is
/// affordable. Used by the differential tests, which must not inherit
/// the search's own pruning assumptions.
pub fn for_each_family<F: FnMut(&[Mask])>(ground: u32, m: u32, mut visit: F) {
    let sets = subsets_of_size(ground, m);
    let n = sets.len();
    assert!(n <= 22, "2^{} families is too many to enumerate", n);
    let mut buf: Vec<Mask> = Vec::with_capacity(n);
    for mask in 0u32..(1u32 << n) {
        buf.clear();
        for (i, &s) in sets.iter().enumerate() {
            if mask >> i & 1 == 1 {
                buf.push(s);
            }
        }
        visit(&buf);
    }
}

/// A human-readable report of the empirical thresholds, for the build
/// log. `elementary` is the parameter at which
/// `SpreadReduction.spread_disjoint_above_elementary` proves the
/// hypothesis outright; the empirical threshold must never exceed it.
pub fn threshold_report(cases: &[(u32, u32, usize)]) -> String {
    let mut out = String::new();
    out.push_str("  ground  m   k   empirical r*   proved sufficient   refuted r\n");
    for &(ground, m, k) in cases {
        let (thr, failing) = empirical_threshold(ground, m, k);
        let elementary = m as u64 * (k as u64 - 1) + 1;
        let fs: Vec<String> = failing.iter().map(|r| r.to_string()).collect();
        out.push_str(&format!(
            "  {:>6}  {:>1}   {:>1}   {:>12}   {:>17}   {}\n",
            ground,
            m,
            k,
            thr,
            elementary,
            if fs.is_empty() { "-".to_string() } else { fs.join(",") }
        ));
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::spread::deg;

    #[test]
    fn deg_agrees_with_naive_count() {
        for_each_family(5, 2, |f| {
            for t in 0..(1u32 << 5) {
                assert_eq!(deg(t, f), deg_naive(t, f));
            }
        });
    }

    #[test]
    fn five_cycle_is_found_at_2_3_2() {
        let f = find_counterexample(5, 2, 3, 2).expect("C5 should be a counterexample");
        assert!(verify_counterexample(&f, 5, 2, 3, 2).is_ok());
        assert_eq!(f.len(), 5);
    }
}
