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
