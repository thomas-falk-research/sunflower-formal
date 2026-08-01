//! Exact `iota` decisions on ground sets too large for a bitmask scan.
//!
//! `intersecting::iota_decide` enumerates the `b`-subsets of `[g]` by
//! walking `0 .. 2^g` and filtering on popcount, so it stops at `g = 16`.
//! That was never a limitation on the *search*, only on the enumeration —
//! and it is the enumeration that stands between this development and a
//! statement about `iota(b)` rather than `iota(b, g)`.
//!
//! ## Why a bounded ground set is enough
//!
//! `iota(b)` quantifies over every ground set, so no single search decides
//! it — unless the ground set can be bounded in terms of the answer, and
//! it can, trivially:
//!
//! > If some intersecting `b`-uniform family has `N` members, some
//! > `N`-member subfamily does too (both conditions are inherited by
//! > subfamilies), and in that subfamily every member meets a fixed
//! > member `A_0`, so contributes at most `b - 1` new points. Hence its
//! > support is at most `b + (b-1)(N-1)`.
//!
//! So `iota(b) >= N` iff `iota(b, b + (b-1)(N-1)) >= N`, and the question
//! becomes one finite search. At `b = 3, N = 11` the bound is 23 points —
//! `Ground.iota_support_bound` is the Coq statement, and this module is
//! what answers the resulting query.
//!
//! Sets are `u64`, so `ground <= 64`; the `b`-subsets are generated
//! combinatorially rather than by scanning masks, which is the whole
//! point.

/// Do `a`, `b`, `c` form a 3-sunflower?
#[inline]
fn is_sunflower(a: u64, b: u64, c: u64) -> bool {
    let ab = a & b;
    ab == (a & c) && ab == (b & c)
}

/// The `b`-subsets of `[ground]`, as `u64` bitmasks, in colex order.
pub fn subsets(ground: u32, b: u32) -> Vec<u64> {
    assert!(ground <= 64, "ground {ground} exceeds u64");
    let mut out = Vec::new();
    if b > ground {
        return out;
    }
    let mut idx: Vec<u32> = (0..b).collect();
    loop {
        out.push(idx.iter().fold(0u64, |m, &i| m | 1u64 << i));
        // Next combination in lexicographic order.
        let mut i = b as i64 - 1;
        while i >= 0 && idx[i as usize] == ground - b + i as u32 {
            i -= 1;
        }
        if i < 0 {
            break;
        }
        idx[i as usize] += 1;
        for j in (i as usize + 1)..b as usize {
            idx[j] = idx[j - 1] + 1;
        }
    }
    out
}

/// Verify a family independently of any search: `b`-uniform, distinct,
/// sunflower-free, and optionally intersecting.
pub fn verify(f: &[u64], b: u32, intersecting: bool) -> Result<(), String> {
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

struct CandSearch {
    best: usize,
    best_family: Vec<u64>,
    nodes: u64,
    budget: u64,
}

impl CandSearch {
    fn rec(&mut self, cands: &[u64], cur: &mut Vec<u64>) {
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
            let next: Vec<u64> = cands[idx + 1..]
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

/// Is there an intersecting sunflower-free `b`-uniform family of at least
/// `target` members on `ground` points?
///
/// Same two reductions as `intersecting::iota_decide`, and sound for the
/// same reasons: the anchor `{0, ..., b-1}` is forced because relabelling
/// preserves everything, and the second member is taken up to the action
/// of the anchor's stabiliser, which has one orbit per value of
/// `|B ∩ A| = 1, ..., b-1`.
///
/// Returns `(reached, witness, exhaustive)`.
pub fn iota_decide(ground: u32, b: u32, target: usize, budget: u64) -> (bool, Vec<u64>, bool) {
    if ground < b || target < 2 {
        return (false, Vec::new(), true);
    }
    let anchor: u64 = (1u64 << b) - 1;
    let all: Vec<u64> = subsets(ground, b)
        .into_iter()
        .filter(|s| *s != anchor && s & anchor != 0)
        .collect();

    let mut exhaustive = true;
    for j in 1..b {
        if b + (b - j) > ground {
            continue;
        }
        let mut rep: u64 = (1u64 << j) - 1;
        for t in 0..(b - j) {
            rep |= 1u64 << (b + t);
        }
        let cands: Vec<u64> = all
            .iter()
            .copied()
            .filter(|&y| y != rep && y & rep != 0 && !is_sunflower(anchor, rep, y))
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

/// The support bound: an `n`-member intersecting `b`-uniform family needs
/// at most `b + (b-1)(n-1)` points. Mirrors `Ground.iota_support_bound`.
pub fn support_bound(b: u32, n: u32) -> u32 {
    if n == 0 {
        0
    } else {
        b + (b - 1) * (n - 1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn subsets_are_the_right_count_and_shape() {
        for (g, b, want) in [(6u32, 3u32, 20usize), (9, 4, 126), (23, 3, 1771), (40, 2, 780)] {
            let s = subsets(g, b);
            assert_eq!(s.len(), want, "C({g},{b})");
            assert!(s.iter().all(|m| m.count_ones() == b));
            let mut sorted = s.clone();
            sorted.sort_unstable();
            sorted.dedup();
            assert_eq!(sorted.len(), want, "duplicates at C({g},{b})");
            assert!(s.iter().all(|m| m >> g == 0), "point outside [{g}]");
        }
    }

    /// The wide search and the 16-bit one must give the same verdicts
    /// wherever both run. Neither shares code with the other.
    #[test]
    fn wide_agrees_with_the_narrow_search() {
        for (b, g) in [(2u32, 5u32), (2, 6), (3, 6), (3, 8), (3, 9), (4, 8), (4, 9)] {
            for target in 2..=12 {
                let (wide, wfam, wdone) = iota_decide(g, b, target, 2_000_000_000);
                let (narrow, nfam, ndone) =
                    crate::intersecting::iota_decide(g, b, target, 2_000_000_000);
                assert!(wdone && ndone, "budget ran out at b={b} g={g} t={target}");
                assert_eq!(wide, narrow, "verdicts differ at b={b} g={g} target={target}");
                if wide {
                    verify(&wfam, b, true).expect("wide witness invalid");
                    crate::intersecting::verify(&nfam, b, true).expect("narrow witness invalid");
                    assert!(wfam.len() >= target);
                }
            }
        }
    }

    /// `iota(3) = 10`, from the support bound plus one exhaustive search.
    ///
    /// An eleven-member intersecting 3-uniform sunflower-free family would
    /// live on at most `3 + 2*10 = 23` points, and there is none there.
    #[test]
    fn iota_three_is_exactly_ten() {
        assert_eq!(support_bound(3, 11), 23);
        let (found, _, done) = iota_decide(23, 3, 11, 20_000_000_000);
        assert!(done, "the ground-23 search did not finish");
        assert!(!found, "an 11-member family exists on 23 points");
        // And ten is attained, on six points.
        let (found10, fam, _) = iota_decide(6, 3, 10, 2_000_000_000);
        assert!(found10);
        verify(&fam, 3, true).expect("witness invalid");
        assert!(fam.len() >= 10);
    }
}
