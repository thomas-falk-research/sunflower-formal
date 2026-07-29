//! Concrete families used in the Coq theorems.

use crate::sunflower::{Family, Set};

/// The k-1 disjoint blocks of n consecutive integers, matching
/// `LowerBound.disjoint_blocks` in the Coq proof. Returns a family
/// of size `count`, with the i-th set being `[i*n, i*n+1, ..., i*n+n-1]`.
pub fn disjoint_blocks(count: usize, n: usize) -> Family {
    (0..count)
        .map(|i| {
            let start = (i * n) as u32;
            (0..n as u32).map(|j| start + j).collect()
        })
        .collect()
}

/// The product family used in the standard (k-1)^n lower bound: all
/// "systems of representatives" of [n] rows, each of width [kk = k-1].
/// Returns a family of size kk^n, each set of size n, members sorted
/// strictly increasing.
pub fn product_family(kk: usize, n: usize) -> Family {
    if n == 0 {
        return vec![vec![]];
    }
    let inner = product_family(kk, n - 1);
    let offset = ((n - 1) * kk) as u32;
    let mut result = Vec::with_capacity(kk * inner.len());
    for set in &inner {
        for c in 0..kk as u32 {
            let mut new_set: Set = set.clone();
            new_set.push(offset + c);
            new_set.sort_unstable();
            result.push(new_set);
        }
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn disjoint_blocks_correct_size() {
        let f = disjoint_blocks(3, 2);
        assert_eq!(f.len(), 3);
        assert_eq!(f[0], vec![0, 1]);
        assert_eq!(f[1], vec![2, 3]);
        assert_eq!(f[2], vec![4, 5]);
    }

    #[test]
    fn product_family_correct_size() {
        // |product_family(2, 3)| = 2^3 = 8
        let f = product_family(2, 3);
        assert_eq!(f.len(), 8);
        // each member has length 3
        for s in &f {
            assert_eq!(s.len(), 3);
        }
        // all members distinct
        for i in 0..f.len() {
            for j in (i + 1)..f.len() {
                assert_ne!(f[i], f[j]);
            }
        }
    }

    #[test]
    fn product_family_no_k_sunflower() {
        // (k-1)^n = 2^3 = 8 with k=3, n=3: no 3-sunflower.
        let f = product_family(2, 3);
        assert!(crate::sunflower::find_k_sunflower(&f, 3).is_none());
        // And one extra set should suffice to force a sunflower — but
        // we'd need to verify Erdős-Rado bound, which is large.
    }
}

/// The direct sum of two families on disjoint ground sets, matching
/// `DirectSum.sum_family` in the Coq proof: every union of a member of
/// `f1` with a member of `f2`.
///
/// The caller is responsible for the ground sets being disjoint;
/// `direct_sum_shifted` does that by construction.
pub fn direct_sum(f1: &[Set], f2: &[Set]) -> Family {
    let mut out = Family::with_capacity(f1.len() * f2.len());
    for a in f1 {
        for b in f2 {
            let mut s: Set = a.clone();
            s.extend_from_slice(b);
            s.sort_unstable();
            out.push(s);
        }
    }
    out
}

/// The largest point of a family, or `None` for the empty family.
fn max_point(f: &[Set]) -> Option<u32> {
    f.iter().flat_map(|s| s.iter().copied()).max()
}

/// `direct_sum` after moving `f2` clear of `f1`'s ground set. This is
/// the operation `DirectSum.lower_bound_sum` performs; the Coq version
/// relabels by parity (`x -> 2x` and `x -> 2x+1`) to avoid computing a
/// maximum, but any injection into a disjoint range does the same job,
/// and a shift keeps the families readable.
pub fn direct_sum_shifted(f1: &[Set], f2: &[Set]) -> Family {
    let shift = max_point(f1).map_or(0, |m| m + 1);
    let moved: Family = f2
        .iter()
        .map(|s| s.iter().map(|x| x + shift).collect())
        .collect();
    direct_sum(f1, &moved)
}

/// The Coq relabellings themselves, so the test can check the parity
/// encoding rather than only the shift one.
pub fn relabel(f: &[Set], odd: bool) -> Family {
    f.iter()
        .map(|s| s.iter().map(|x| 2 * x + u32::from(odd)).collect())
        .collect()
}

/// Root-to-leaf paths in a rooted binary tree of depth `k`, as sets of
/// edges — the construction [FPPTZ24] uses to show that the *ground set*
/// of a sunflower-free `k`-uniform family can be exponentially large.
///
/// Edges are labelled by the binary string of the child they lead to, so
/// there are `2^(k+1) - 2` of them, and a root-to-leaf path is the `k`
/// prefixes of a leaf's string. That is `2^k` members, `k`-uniform, on an
/// exponentially large ground set.
///
/// It is sunflower-free for a reason worth stating: two paths meet in the
/// path to the least common ancestor of their leaves, and among any three
/// leaves of a binary tree two are strictly closer than the third pair,
/// so of the three pairwise intersections two coincide and one is
/// strictly longer. Never all three equal.
///
/// Returned as `u128` bitmasks, so `k <= 6` (126 edges).
pub fn tree_paths(k: u32) -> Vec<u128> {
    assert!(k >= 1 && k <= 6, "the 128-bit encoding needs 1 <= k <= 6");
    // Edge index for the node whose binary string is `s` of length `len`:
    // strings of length 1 occupy 0..2, length 2 occupy 2..6, and so on.
    let index = |len: u32, s: u32| -> u32 { (1u32 << len) - 2 + s };
    (0..(1u32 << k))
        .map(|leaf| {
            let mut m: u128 = 0;
            for len in 1..=k {
                // the length-`len` prefix of `leaf`, read from the top
                let s = leaf >> (k - len);
                m |= 1u128 << index(len, s);
            }
            m
        })
        .collect()
}

/// How many edges `tree_paths(k)` uses: `2^(k+1) - 2`, every one of them.
pub fn tree_paths_ground(k: u32) -> u32 {
    (1u32 << (k + 1)) - 2
}
