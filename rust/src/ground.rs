//! How much ground set does an extremal sunflower-free family need?
//!
//! `N(m, g)` is the largest `m`-uniform 3-sunflower-free family on `g`
//! points. It is non-decreasing in `g` and bounded above by `f(m,3) - 1`,
//! so it plateaus. *Where* it plateaus is the question the polynomial
//! method turns on: Naslund-Sawin bound any sunflower-free family of
//! subsets of `[g]` by `3(g+1)C^g` with `C = 3/2^(2/3) < 1.89`, a bound
//! in the **ground set**. If `N(m, g)` plateaus at `g = O(m)`, that
//! bound becomes `constant^m` and settles the sunflower conjecture at
//! `k = 3`. If it keeps climbing, the polynomial method cannot see the
//! uniform problem at all, and this measures how fast.
//!
//! Sets are bitmasks, so `ground <= 16`.

/// All `m`-subsets of `[ground]`, as bitmasks.
pub fn m_subsets(ground: u32, m: u32) -> Vec<u16> {
    (0u32..(1 << ground))
        .filter(|x| x.count_ones() == m)
        .map(|x| x as u16)
        .collect()
}

/// Do `a`, `b`, `c` form a 3-sunflower? (Distinctness is the caller's.)
#[inline]
fn is_sunflower(a: u16, b: u16, c: u16) -> bool {
    let ab = a & b;
    ab == (a & c) && ab == (b & c)
}

/// Whether adding `x` to `cur` creates a 3-sunflower.
#[inline]
fn creates_sunflower(cur: &[u16], x: u16) -> bool {
    for i in 0..cur.len() {
        for j in (i + 1)..cur.len() {
            if is_sunflower(cur[i], cur[j], x) {
                return true;
            }
        }
    }
    false
}

struct Search {
    sets: Vec<u16>,
    best: usize,
    best_family: Vec<u16>,
    nodes: u64,
    node_budget: u64,
    exhausted: bool,
}

impl Search {
    fn rec(&mut self, i: usize, cur: &mut Vec<u16>) {
        self.nodes += 1;
        if self.nodes > self.node_budget {
            self.exhausted = false;
            return;
        }
        if cur.len() > self.best {
            self.best = cur.len();
            self.best_family = cur.clone();
        }
        // Nothing left can beat the incumbent.
        if cur.len() + (self.sets.len() - i) <= self.best {
            return;
        }
        if i == self.sets.len() {
            return;
        }
        let x = self.sets[i];
        if !creates_sunflower(cur, x) {
            cur.push(x);
            self.rec(i + 1, cur);
            cur.pop();
            if self.nodes > self.node_budget {
                return;
            }
        }
        self.rec(i + 1, cur);
    }
}

/// `N(m, ground)` by exhaustive branch and bound.
///
/// Returns `(size, witness, exhaustive)`. When `exhaustive` is false the
/// node budget ran out and `size` is only a **lower** bound — the caller
/// must say so rather than report it as a maximum.
pub fn max_sunflower_free(ground: u32, m: u32, node_budget: u64) -> (usize, Vec<u16>, bool) {
    let mut s = Search {
        sets: m_subsets(ground, m),
        best: 0,
        best_family: Vec::new(),
        nodes: 0,
        node_budget,
        exhausted: true,
    };
    let mut cur = Vec::new();
    s.rec(0, &mut cur);
    (s.best, s.best_family, s.exhausted && s.nodes <= s.node_budget)
}

/// Check a family really is `m`-uniform, distinct and 3-sunflower-free.
pub fn verify(f: &[u16], m: u32) -> Result<(), String> {
    for (i, a) in f.iter().enumerate() {
        if a.count_ones() != m {
            return Err(format!("member {i} has size {}", a.count_ones()));
        }
        for (j, b) in f.iter().enumerate().skip(i + 1) {
            if a == b {
                return Err(format!("members {i} and {j} are equal"));
            }
            for (l, c) in f.iter().enumerate().skip(j + 1) {
                if is_sunflower(*a, *b, *c) {
                    return Err(format!("members {i},{j},{l} are a 3-sunflower"));
                }
            }
        }
    }
    Ok(())
}
