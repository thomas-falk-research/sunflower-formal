//! Rust mirrors of the Coq spread definitions, on bitmask sets.
//!
//! Every function here is a deliberate re-implementation of a Coq
//! definition from `coq/Spread.v`, written against a different data
//! representation (a set is a bitmask over a ground set `0..ground`,
//! not a `list nat` with a `NoDup` side condition). The point of the
//! duplication is that a misreading of the Coq definition is unlikely
//! to be reproduced independently here: `testbed.rs` runs both against
//! exhaustive enumerations and against statements the kernel has
//! already proved, and a disagreement is a signal that one of the two
//! readings is wrong.
//!
//! Correspondence with the Coq source:
//!
//! | Coq (`coq/Spread.v`)      | here                       |
//! |---------------------------|----------------------------|
//! | `deg T F`                 | [`deg`]                    |
//! | `RaoSpread m F r`         | [`is_rao_spread`]          |
//! | `Spread F r`              | [`is_fractionally_spread`] |
//! | `rao_witness m F r`       | [`rao_witness_cands`]      |
//! | `Reflect.rao_spreadb`     | [`rao_witness_ground`]     |
//! | `PairwiseDisjoint`, size k | [`has_k_disjoint`]        |

/// A finite set, as a bitmask over the ground set `{0, ..., 31}`.
pub type Mask = u32;

/// `r^e`, saturating rather than wrapping. Coq's `r ^ e` on `nat` is
/// unbounded; saturation only ever makes the spread condition *easier*
/// to satisfy, and the parameters used here never come close.
pub fn pow_sat(r: u64, e: u32) -> u64 {
    let mut acc: u64 = 1;
    for _ in 0..e {
        acc = acc.saturating_mul(r);
    }
    acc
}

/// `deg T F`: how many members of `F` contain `T`.
pub fn deg(t: Mask, f: &[Mask]) -> usize {
    f.iter().filter(|&&a| a & t == t).count()
}

/// Rao's absolute spread condition (`Spread.RaoSpread`): every
/// *nonempty* `T` satisfies `deg T F <= r^(m - |T|)`, with `m - |T|`
/// truncated at zero exactly as Coq's `nat` subtraction is.
///
/// Sets `T` not contained in the ground set have degree 0 and satisfy
/// the inequality trivially, so quantifying over subsets of the ground
/// set loses nothing.
pub fn is_rao_spread(m: u32, f: &[Mask], r: u64, ground: u32) -> bool {
    rao_witness_ground(m, f, r, ground).is_none()
}

/// The fractional (ALWZ / FKNP) spread condition (`Spread.Spread`):
/// `r^|T| * deg T F <= |F|` for every `T`, including the empty one.
pub fn is_fractionally_spread(f: &[Mask], r: u64, ground: u32) -> bool {
    for t in 0..(1u32 << ground) {
        let lhs = pow_sat(r, t.count_ones()).saturating_mul(deg(t, f) as u64);
        if lhs > f.len() as u64 {
            return false;
        }
    }
    true
}

/// `Spread.rao_witness`: search for a violating `T` among the
/// *sublists of members* of `F` — the enumeration `cands F` that the
/// Coq decision procedure uses.
pub fn rao_witness_cands(m: u32, f: &[Mask], r: u64) -> Option<Mask> {
    for &a in f {
        let mut t = a;
        loop {
            if t != 0 {
                let cap = pow_sat(r, m.saturating_sub(t.count_ones()));
                if deg(t, f) as u64 > cap {
                    return Some(t);
                }
            }
            if t == 0 {
                break;
            }
            t = (t - 1) & a;
        }
    }
    None
}

/// `Reflect.rao_spreadb`: search for a violating `T` among *all*
/// nonempty subsets of the ground set. Independent of the family's
/// own structure, and generally a much larger enumeration.
pub fn rao_witness_ground(m: u32, f: &[Mask], r: u64, ground: u32) -> Option<Mask> {
    for t in 1..(1u32 << ground) {
        let cap = pow_sat(r, m.saturating_sub(t.count_ones()));
        if deg(t, f) as u64 > cap {
            return Some(t);
        }
    }
    None
}

/// Are there `k` pairwise disjoint members? This is the conclusion of
/// `SpreadReduction.SpreadYieldsDisjoint`.
pub fn has_k_disjoint(f: &[Mask], k: usize) -> bool {
    fn go(f: &[Mask], used: Mask, need: usize, start: usize) -> bool {
        if need == 0 {
            return true;
        }
        if f.len() < start + need {
            return false;
        }
        for i in start..f.len() {
            if f[i] & used == 0 && go(f, used | f[i], need - 1, i + 1) {
                return true;
            }
        }
        false
    }
    go(f, 0, k, 0)
}

/// The matching number: the largest number of pairwise disjoint members.
pub fn matching_number(f: &[Mask]) -> usize {
    let mut k = 0;
    while has_k_disjoint(f, k + 1) {
        k += 1;
    }
    k
}

/// Every member has exactly `m` elements (`Sunflower.Uniform`).
pub fn is_uniform(m: u32, f: &[Mask]) -> bool {
    f.iter().all(|a| a.count_ones() == m)
}

/// No two members are equal. On bitmasks, set-equality and literal
/// equality coincide, so this is `Sunflower.Distinct`.
pub fn is_distinct(f: &[Mask]) -> bool {
    for i in 0..f.len() {
        for j in (i + 1)..f.len() {
            if f[i] == f[j] {
                return false;
            }
        }
    }
    true
}

/// All `m`-element subsets of `{0, ..., ground-1}`, in increasing
/// numeric order of their masks.
pub fn subsets_of_size(ground: u32, m: u32) -> Vec<Mask> {
    (0..(1u32 << ground)).filter(|t| t.count_ones() == m).collect()
}

/// Render a mask as the sorted element list, matching the `Vec<u32>`
/// representation used by `sunflower.rs`.
pub fn mask_to_set(a: Mask) -> Vec<u32> {
    (0..32).filter(|i| a >> i & 1 == 1).collect()
}

/// Render a family in the notation used in the Coq sources.
pub fn family_to_coq(f: &[Mask]) -> String {
    let members: Vec<String> = f
        .iter()
        .map(|&a| {
            let elts: Vec<String> = mask_to_set(a).iter().map(|x| x.to_string()).collect();
            format!("[{}]", elts.join("; "))
        })
        .collect();
    format!("[{}]", members.join("; "))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn set(elts: &[u32]) -> Mask {
        elts.iter().fold(0, |acc, &x| acc | 1 << x)
    }

    #[test]
    fn pow_sat_matches_nat_pow() {
        assert_eq!(pow_sat(2, 0), 1);
        assert_eq!(pow_sat(0, 0), 1);
        assert_eq!(pow_sat(0, 3), 0);
        assert_eq!(pow_sat(3, 4), 81);
    }

    #[test]
    fn deg_counts_supersets() {
        let f = vec![set(&[0, 1]), set(&[0, 2]), set(&[1, 2])];
        assert_eq!(deg(0, &f), 3); // the empty set is in every member
        assert_eq!(deg(set(&[0]), &f), 2);
        assert_eq!(deg(set(&[0, 1]), &f), 1);
        assert_eq!(deg(set(&[0, 3]), &f), 0);
    }

    #[test]
    fn five_cycle_is_2_spread_but_has_no_3_disjoint_edges() {
        // The witness family of `Audit.no_spread_yields_disjoint_2_3_2`.
        let c5 = vec![
            set(&[0, 1]),
            set(&[1, 2]),
            set(&[2, 3]),
            set(&[3, 4]),
            set(&[0, 4]),
        ];
        assert!(is_uniform(2, &c5));
        assert!(is_distinct(&c5));
        assert!(is_rao_spread(2, &c5, 2, 5));
        assert!(c5.len() as u64 > pow_sat(2, 2));
        assert_eq!(matching_number(&c5), 2);
        assert!(!has_k_disjoint(&c5, 3));
    }

    #[test]
    fn star_is_not_spread() {
        let star = vec![set(&[0, 1]), set(&[0, 2]), set(&[0, 3])];
        assert!(!is_rao_spread(2, &star, 2, 4));
        assert_eq!(rao_witness_cands(2, &star, 2), Some(set(&[0])));
    }

    #[test]
    fn matching_number_of_disjoint_blocks() {
        let f = vec![set(&[0, 1]), set(&[2, 3]), set(&[4, 5])];
        assert_eq!(matching_number(&f), 3);
    }
}
