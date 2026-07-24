//! Bound computation and exact f(n, k) tabulation.

/// Erdős–Rado upper bound: f(n, k) <= (k-1)^n * n! + 1.
pub fn erdos_rado_bound(n: usize, k: usize) -> u64 {
    if k < 2 || n == 0 {
        return 0;
    }
    let mut result: u64 = 1;
    let base = (k - 1) as u64;
    for _ in 0..n {
        result = result.saturating_mul(base);
    }
    let mut factorial: u64 = 1;
    for i in 1..=n {
        factorial = factorial.saturating_mul(i as u64);
    }
    result.saturating_mul(factorial).saturating_add(1)
}

/// Compute the exact value of f(n, k) by exhaustive search:
/// the minimum m such that every distinct n-uniform family of size m
/// over [0, universe) contains a k-sunflower.
///
/// This is exponential and only works for tiny inputs (n, k, universe
/// all small).
///
/// Returns `(m, witness)` where m = f(n,k) bounded by the search
/// universe, and `witness` is a maximum-size family with no
/// k-sunflower (so |witness| = m - 1).
pub fn f_nk_exact(n: usize, k: usize, universe: usize) -> (u64, crate::sunflower::Family) {
    use crate::sunflower::{find_k_sunflower, Family, Set};

    // Enumerate all n-subsets of [0, universe).
    fn n_subsets(universe: usize, n: usize) -> Vec<Set> {
        let mut acc: Vec<Set> = Vec::new();
        fn aux(universe: usize, n: usize, start: u32, current: &mut Set, acc: &mut Vec<Set>) {
            if current.len() == n {
                acc.push(current.clone());
                return;
            }
            for x in start..universe as u32 {
                if (universe as u32 - x) < (n - current.len()) as u32 {
                    break;
                }
                current.push(x);
                aux(universe, n, x + 1, current, acc);
                current.pop();
            }
        }
        aux(universe, n, 0, &mut Vec::new(), &mut acc);
        acc
    }

    let all_sets = n_subsets(universe, n);
    let total = all_sets.len();

    // Try every subfamily by bitmask (only feasible for small total).
    let max_mask: u64 = 1u64 << total;
    let mut best_no_sunflower: Family = Vec::new();
    for mask in 0..max_mask {
        let family: Family = (0..total)
            .filter(|i| (mask >> i) & 1 == 1)
            .map(|i| all_sets[i].clone())
            .collect();
        if find_k_sunflower(&family, k).is_none() {
            if family.len() > best_no_sunflower.len() {
                best_no_sunflower = family;
            }
        }
    }
    let m = (best_no_sunflower.len() + 1) as u64;
    (m, best_no_sunflower)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn er_bound_values() {
        // (k-1)^n * n! + 1
        assert_eq!(erdos_rado_bound(1, 2), 1 * 1 + 1); // 2
        assert_eq!(erdos_rado_bound(1, 3), 2 * 1 + 1); // 3
        assert_eq!(erdos_rado_bound(2, 2), 1 * 2 + 1); // 3
        assert_eq!(erdos_rado_bound(2, 3), 4 * 2 + 1); // 9
        assert_eq!(erdos_rado_bound(3, 3), 8 * 6 + 1); // 49
    }

    #[test]
    fn f_n_2_is_2() {
        // f(1, 2) = 2 — any two distinct singletons form a 2-sunflower.
        let (m, _) = f_nk_exact(1, 2, 3);
        assert_eq!(m, 2);
    }

    #[test]
    fn f_1_3_is_3() {
        // f(1, 3) = 3 — three distinct singletons needed for a 3-sunflower.
        let (m, _) = f_nk_exact(1, 3, 4);
        assert_eq!(m, 3);
    }
}
