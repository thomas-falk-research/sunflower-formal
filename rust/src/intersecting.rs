//! Intersecting sunflower-free families, and what they build.
//!
//! Write `iota(b)` for the largest *intersecting* 3-sunflower-free
//! `b`-uniform family, and `g(m) = f(m,3) - 1` as usual. Two
//! constructions turn `iota` into lower bounds on `g`:
//!
//! * **Doubling.** Two disjoint copies of an intersecting sunflower-free
//!   family are sunflower-free: any three members put two in the same
//!   copy, and those two meet, while a member of the other copy meets
//!   neither. So `g(b) >= 2 * iota(b)`. At `b = 2` the intersecting
//!   family is the triangle, `iota(2) = 3`, and this *is* `two_triangles`.
//!
//! * **Substitution.** Given `G` a-uniform sunflower-free and `H`
//!   b-uniform sunflower-free *and intersecting*, blow up each point of
//!   each member of `G` into a member of `H`: ground set `V x W`, member
//!   `union over v in A of {v} x phi(v)` for `A` in `G` and
//!   `phi : A -> H`. That is `ab`-uniform, sunflower-free, and has
//!   `|G| * |H|^a` members, so `g(ab) >= g(a) * iota(b)^a`.
//!
//!   The intersecting hypothesis is what makes the projection to `V`
//!   a delta-system: `phi_i(v)` and `phi_j(v)` always meet, so
//!   `pi(C_i ∩ C_j) = A_i ∩ A_j` exactly. Without it the projection
//!   loses points and the argument fails.
//!
//! Iterating the substitution has fixed point `c^b = c * iota(b)`, i.e.
//! a rate of **`iota(b)^(1/(b-1))`** per point. At `b = 2` that is 3; at
//! `b = 3` with `iota(3) = 10` it is `10^(1/2) = 3.162...`, which is
//! exactly the Abbott-Hanson-Sauer bound of 1972. So `iota(3) = 10` is,
//! on this reading, the whole content of that paper — and the record
//! moves the moment some `b` has `iota(b) > 10^((b-1)/2)`:
//!
//! ```text
//!     b = 4   needs iota(4) >=  32
//!     b = 5   needs iota(5) >= 101
//!     b = 6   needs iota(6) >= 317
//! ```
//!
//! The reconstruction is ours, not read from the source; that it
//! reproduces both `g(2) = 6` and the published `3.162` exactly is the
//! evidence for it. `substitution_is_sunflower_free` in the tests checks
//! the construction itself against the brute-force detector, which is
//! what the claim actually rests on here.

use crate::ground::m_subsets;

/// Do `a`, `b`, `c` form a 3-sunflower?
#[inline]
fn is_sunflower(a: u32, b: u32, c: u32) -> bool {
    let ab = a & b;
    ab == (a & c) && ab == (b & c)
}

/// Whether `x` may be added to `cur`: it must meet every member (when
/// `intersecting`) and complete no 3-sunflower.
#[inline]
fn admissible(cur: &[u32], x: u32, intersecting: bool) -> bool {
    if intersecting && cur.iter().any(|a| a & x == 0) {
        return false;
    }
    for i in 0..cur.len() {
        for j in (i + 1)..cur.len() {
            if is_sunflower(cur[i], cur[j], x) {
                return false;
            }
        }
    }
    true
}

struct Search {
    sets: Vec<u32>,
    intersecting: bool,
    best: usize,
    best_family: Vec<u32>,
    nodes: u64,
    budget: u64,
}

impl Search {
    fn rec(&mut self, i: usize, cur: &mut Vec<u32>) {
        self.nodes += 1;
        if self.nodes > self.budget {
            return;
        }
        if cur.len() > self.best {
            self.best = cur.len();
            self.best_family = cur.clone();
        }
        if cur.len() + (self.sets.len() - i) <= self.best || i == self.sets.len() {
            return;
        }
        let x = self.sets[i];
        if admissible(cur, x, self.intersecting) {
            cur.push(x);
            self.rec(i + 1, cur);
            cur.pop();
            if self.nodes > self.budget {
                return;
            }
        }
        self.rec(i + 1, cur);
    }
}

/// `iota(b)` restricted to a ground set of size `ground`.
///
/// Symmetry reduction, and it is the reason this is tractable at all:
/// an intersecting family may be relabelled so that a chosen member is
/// `{0, ..., b-1}`. That member is forced in, and the universe shrinks
/// to the `b`-sets meeting it — which for `b = 4, ground = 12` cuts 495
/// candidates to 209.
///
/// Returns `(size, witness, exhaustive)`; when `exhaustive` is false the
/// budget ran out and the size is only a lower bound.
pub fn max_intersecting(ground: u32, b: u32, budget: u64) -> (usize, Vec<u32>, bool) {
    max_intersecting_from(ground, b, budget, 0)
}

/// As `max_intersecting`, but starting from a known incumbent.
///
/// `iota(b, g)` is non-decreasing in `g`, so the answer at `g - 1` is a
/// valid seed at `g` — and seeding is not just bookkeeping, it is the
/// pruning. With `best` already at the previous row's value the search
/// discards every branch that cannot beat it, which is most of them.
///
/// When nothing beats `seed` the returned witness is empty and the
/// returned size is `seed`; the caller must not treat that as a family.
pub fn max_intersecting_from(
    ground: u32,
    b: u32,
    budget: u64,
    seed: usize,
) -> (usize, Vec<u32>, bool) {
    if ground < b {
        return (seed, Vec::new(), true);
    }
    let anchor: u32 = (1u32 << b) - 1;
    let sets: Vec<u32> = m_subsets(ground, b)
        .into_iter()
        .map(u32::from)
        .filter(|s| *s != anchor && s & anchor != 0)
        .collect();
    let mut s = Search {
        sets,
        intersecting: true,
        best: seed,
        best_family: Vec::new(),
        nodes: 0,
        budget,
    };
    let mut cur = vec![anchor];
    s.rec(0, &mut cur);
    let done = s.nodes <= s.budget;
    (s.best, s.best_family, done)
}

/// Candidate-set search: the same problem, but the branching set is
/// carried explicitly and filtered at every step instead of being
/// indexed into.
///
/// The index-based bound is "everything left could be added", which for
/// an intersecting family is wildly optimistic — most remaining sets are
/// already dead because they miss something in the partial family.
/// Filtering makes the bound `|cur| + |cands|` over the sets still
/// genuinely addable, which prunes near the root rather than at the
/// leaves.
///
/// Every pair is still checked: when `x` is added the survivors are
/// filtered against every pair `(c, x)` for `c` in the partial family,
/// and pairs internal to that family were filtered when their later
/// element was added.
struct CandSearch {
    best: usize,
    best_family: Vec<u32>,
    nodes: u64,
    budget: u64,
}

impl CandSearch {
    fn rec(&mut self, cands: &[u32], cur: &mut Vec<u32>) {
        self.nodes += 1;
        if self.nodes > self.budget {
            return;
        }
        if cur.len() > self.best {
            self.best = cur.len();
            self.best_family = cur.clone();
        }
        for idx in 0..cands.len() {
            if cur.len() + (cands.len() - idx) <= self.best {
                return;
            }
            let x = cands[idx];
            let next: Vec<u32> = cands[idx + 1..]
                .iter()
                .copied()
                .filter(|&y| y & x != 0 && !cur.iter().any(|&a| is_sunflower(a, x, y)))
                .collect();
            cur.push(x);
            self.rec(&next, cur);
            cur.pop();
            if self.nodes > self.budget {
                return;
            }
        }
    }
}

/// `iota(b, ground)` by candidate-set search. Same answer as
/// `max_intersecting_from`; `iota_searches_agree` checks that wherever
/// both finish.
pub fn iota(ground: u32, b: u32, budget: u64, seed: usize) -> (usize, Vec<u32>, bool) {
    if ground < b {
        return (seed, Vec::new(), true);
    }
    let anchor: u32 = (1u32 << b) - 1;
    let cands: Vec<u32> = m_subsets(ground, b)
        .into_iter()
        .map(u32::from)
        .filter(|s| *s != anchor && s & anchor != 0)
        .collect();
    let mut s = CandSearch {
        best: seed,
        best_family: Vec::new(),
        nodes: 0,
        budget,
    };
    let mut cur = vec![anchor];
    s.rec(&cands, &mut cur);
    let done = s.nodes <= s.budget;
    (s.best, s.best_family, done)
}

/// Is there an intersecting sunflower-free `b`-uniform family of at
/// least `target` members on `ground` points?
///
/// Two reductions beyond `iota`, and together they are the difference
/// between hours and minutes.
///
/// **The decision framing.** Seeding the incumbent at `target - 1` makes
/// the bound `|cur| + |cands| <= target - 1` kill every branch that
/// cannot reach the target. Asking for the exact maximum wastes all of
/// that.
///
/// **The second member, up to symmetry.** The stabiliser of the anchor
/// `A = {0,...,b-1}` is `Sym(A) x Sym(rest)`, and it acts on the other
/// `b`-sets with exactly `b - 1` orbits — one per value of
/// `|B ∩ A| = 1, ..., b-1`. So instead of branching over every candidate
/// for the second member, branch over one representative each. At
/// `b = 4, ground = 10` that is 3 branches rather than 195.
///
/// Correct because any family containing `A` with two or more members
/// has *some* second member, and a stabiliser element carries it to a
/// representative while fixing `A` and preserving both intersecting-ness
/// and sunflower-freeness. The branches overlap, which costs nothing for
/// a maximum.
///
/// Returns `(reached, witness, exhaustive)`.
pub fn iota_decide(
    ground: u32,
    b: u32,
    target: usize,
    budget: u64,
) -> (bool, Vec<u32>, bool) {
    if ground < b || target < 2 {
        return (false, Vec::new(), true);
    }
    let anchor: u32 = (1u32 << b) - 1;
    let all: Vec<u32> = m_subsets(ground, b)
        .into_iter()
        .map(u32::from)
        .filter(|s| *s != anchor && s & anchor != 0)
        .collect();

    let mut exhaustive = true;
    for j in 1..b {
        // Representative with |rep ∩ anchor| = j: the first j points of
        // the anchor, then the first b-j points outside it.
        if b + (b - j) > ground {
            continue;
        }
        let mut rep: u32 = (1u32 << j) - 1;
        for t in 0..(b - j) {
            rep |= 1 << (b + t);
        }
        let cands: Vec<u32> = all
            .iter()
            .copied()
            .filter(|&y| {
                y != rep && y & rep != 0 && !is_sunflower(anchor, rep, y)
            })
            .collect();
        let mut s = CandSearch {
            best: target - 1,
            best_family: Vec::new(),
            nodes: 0,
            budget,
        };
        let mut cur = vec![anchor, rep];
        s.rec(&cands, &mut cur);
        if s.nodes > s.budget {
            exhaustive = false;
        }
        if !s.best_family.is_empty() {
            return (true, s.best_family, true);
        }
    }
    (false, Vec::new(), exhaustive)
}

/// Verify a family is `b`-uniform, distinct, sunflower-free, and
/// (optionally) intersecting. Independent of the search.
pub fn verify(f: &[u32], b: u32, intersecting: bool) -> Result<(), String> {
    for (i, a) in f.iter().enumerate() {
        if a.count_ones() != b {
            return Err(format!("member {i} has size {}", a.count_ones()));
        }
        for (j, y) in f.iter().enumerate().skip(i + 1) {
            if a == y {
                return Err(format!("members {i} and {j} are equal"));
            }
            if intersecting && a & y == 0 {
                return Err(format!("members {i} and {j} are disjoint"));
            }
            for (l, c) in f.iter().enumerate().skip(j + 1) {
                if is_sunflower(*a, *y, *c) {
                    return Err(format!("members {i},{j},{l} are a 3-sunflower"));
                }
            }
        }
    }
    Ok(())
}

/// Two disjoint copies, on `2 * ground` points. Sunflower-free whenever
/// the input is intersecting and sunflower-free.
pub fn doubled(f: &[u32], ground: u32) -> Vec<u32> {
    let mut out: Vec<u32> = f.to_vec();
    out.extend(f.iter().map(|s| s << ground));
    out
}

/// The substitution construction, as sets of `(v, w)` pairs encoded at
/// bit `v * wground + w`.
///
/// `g` is `a`-uniform on `vground` points, `h` is `b`-uniform on
/// `wground` points. Returns an `a*b`-uniform family of `|g| * |h|^a`
/// members on `vground * wground` points.
pub fn substitute(
    g: &[u32],
    vground: u32,
    h: &[u32],
    wground: u32,
) -> Vec<u128> {
    assert!(vground * wground <= 128, "encoding needs <= 128 bits");
    let mut out = Vec::new();
    for &a in g {
        let pts: Vec<u32> = (0..vground).filter(|v| a >> v & 1 == 1).collect();
        // Every assignment of a member of `h` to each point of `a`.
        let mut choice = vec![0usize; pts.len()];
        loop {
            let mut member: u128 = 0;
            for (idx, &v) in pts.iter().enumerate() {
                let hw = h[choice[idx]];
                for w in 0..wground {
                    if hw >> w & 1 == 1 {
                        member |= 1u128 << (v * wground + w);
                    }
                }
            }
            out.push(member);

            let mut k = 0;
            loop {
                if k == pts.len() {
                    break;
                }
                choice[k] += 1;
                if choice[k] < h.len() {
                    break;
                }
                choice[k] = 0;
                k += 1;
            }
            if k == pts.len() {
                break;
            }
        }
    }
    out
}

/// Sunflower-freeness for the 128-bit encoding used by `substitute`.
/// Returns the offending triple if there is one.
pub fn find_sunflower_128(f: &[u128]) -> Option<(usize, usize, usize)> {
    for i in 0..f.len() {
        for j in (i + 1)..f.len() {
            let ab = f[i] & f[j];
            for l in (j + 1)..f.len() {
                if ab == (f[i] & f[l]) && ab == (f[j] & f[l]) {
                    return Some((i, j, l));
                }
            }
        }
    }
    None
}
