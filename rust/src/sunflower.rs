//! Brute-force k-sunflower detector.
//!
//! A k-sunflower in a family F is a sub-collection of k distinct sets
//! A_1, ..., A_k such that A_i ∩ A_j is the same set Y (the "core")
//! for every pair i != j.
//!
//! This module:
//!   - Represents finite sets as sorted `Vec<u32>` with no duplicates
//!     (canonical form).
//!   - Searches for a k-sunflower by enumerating all k-subsets and
//!     checking the pairwise-intersection condition.
//!
//! Runtime is O(|F|^k * k * |universe|), which is fine for the small
//! parameters this crate aims at (n, k ≤ 5 or so).

use std::collections::BTreeSet;

pub type Set = Vec<u32>;
pub type Family = Vec<Set>;

/// A witnessed k-sunflower.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Sunflower {
    /// Indices into the family identifying the k petals.
    pub indices: Vec<usize>,
    /// The common core of the sunflower.
    pub core: Set,
}

/// Set intersection on canonical sets (sorted, deduped).
pub fn intersect(a: &[u32], b: &[u32]) -> Set {
    let bset: BTreeSet<u32> = b.iter().copied().collect();
    a.iter().filter(|x| bset.contains(x)).copied().collect()
}

/// Check that `family` is a valid family: every member is a canonical
/// (sorted strictly-increasing) set, every two members are distinct
/// (set-distinct, which equals literal-distinct for canonical sets).
pub fn is_valid_family(family: &[Set]) -> bool {
    for s in family {
        if !is_canonical(s) {
            return false;
        }
    }
    for i in 0..family.len() {
        for j in (i + 1)..family.len() {
            if family[i] == family[j] {
                return false;
            }
        }
    }
    true
}

fn is_canonical(s: &[u32]) -> bool {
    s.windows(2).all(|w| w[0] < w[1])
}

/// Canonicalize a set: sort and dedup.
pub fn canon(mut s: Set) -> Set {
    s.sort_unstable();
    s.dedup();
    s
}

/// Test whether the sub-family at `indices` forms a k-sunflower.
pub fn is_k_sunflower(family: &[Set], indices: &[usize]) -> Option<Set> {
    if indices.len() < 2 {
        return None;
    }
    // Compute proposed core from the first two intersection.
    let core = intersect(&family[indices[0]], &family[indices[1]]);
    // Check pairwise.
    for i in 0..indices.len() {
        for j in (i + 1)..indices.len() {
            let cij = intersect(&family[indices[i]], &family[indices[j]]);
            if cij != core {
                return None;
            }
        }
    }
    Some(core)
}

/// Brute-force search: returns Some(sunflower) if `family` contains a
/// k-sunflower, None otherwise. Search is over all k-subsets of the
/// family's index set.
pub fn find_k_sunflower(family: &[Set], k: usize) -> Option<Sunflower> {
    if family.len() < k || k < 2 {
        return None;
    }
    let n = family.len();
    let mut idx = vec![0usize; k];
    for i in 0..k {
        idx[i] = i;
    }
    loop {
        if let Some(core) = is_k_sunflower(family, &idx) {
            return Some(Sunflower {
                indices: idx.clone(),
                core,
            });
        }
        // Advance to next k-subset (lexicographic).
        let mut i = k;
        while i > 0 {
            i -= 1;
            if idx[i] < n - (k - i) {
                idx[i] += 1;
                for j in (i + 1)..k {
                    idx[j] = idx[j - 1] + 1;
                }
                break;
            }
            if i == 0 {
                return None;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn intersect_basic() {
        assert_eq!(intersect(&[1, 2, 3], &[2, 3, 4]), vec![2, 3]);
        assert_eq!(intersect(&[1, 2], &[3, 4]), Vec::<u32>::new());
    }

    #[test]
    fn three_disjoint_singletons_form_3_sunflower() {
        let family: Family = vec![vec![1], vec![2], vec![3]];
        let res = find_k_sunflower(&family, 3).unwrap();
        assert_eq!(res.core, Vec::<u32>::new());
        assert_eq!(res.indices, vec![0, 1, 2]);
    }

    #[test]
    fn no_sunflower_when_family_too_small() {
        let family: Family = vec![vec![1, 2], vec![1, 3]];
        assert!(find_k_sunflower(&family, 3).is_none());
    }

    #[test]
    fn shared_core_sunflower() {
        // Three sets all containing 1, with pairwise intersection {1}.
        let family: Family = vec![vec![1, 2], vec![1, 3], vec![1, 4]];
        let res = find_k_sunflower(&family, 3).unwrap();
        assert_eq!(res.core, vec![1]);
    }
}
