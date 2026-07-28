//! The link characterisation, as a computable predicate.
//!
//! A `k`-sunflower with core `Y` is `k` members all containing `Y`
//! whose parts outside `Y` are pairwise disjoint, because for
//! `Y ⊆ A, B`,
//!
//! ```text
//!     A ∩ B = Y   ⟺   (A \ Y) ∩ (B \ Y) = ∅.
//! ```
//!
//! So the conjectured statement is
//!
//! ```text
//!     ContainsKSunflower k F   ⟺   ∃ Y, HasKDisjoint k (link Y F),
//! ```
//!
//! with `link` and `HasKDisjoint` the definitions already in
//! `coq/Spread.v` and `coq/TwoUniform.v`. This module mirrors `link`
//! on bitmasks, in the same spirit as `spread.rs`: an independent
//! re-implementation whose disagreement with the Coq reading is the
//! signal worth having.
//!
//! Correspondence with the Coq source:
//!
//! | Coq                              | here                       |
//! |----------------------------------|----------------------------|
//! | `Spread.link T F`                | [`link`]                   |
//! | `TwoUniform.HasKDisjoint k F`    | `spread::has_k_disjoint`   |
//! | `exists Y, HasKDisjoint k (link Y F)` | [`link_core_witness`] |
//!
//! Two places the equivalence could plausibly break, and which the
//! tests in `rust/tests/link_characterisation.rs` aim at directly:
//!
//! * **A member equal to the core.** Then its petal is the empty set,
//!   which is disjoint from everything and would be counted by
//!   `has_k_disjoint`. Is the lifted family still a sunflower? (It is —
//!   `∅ ∩ A = ∅` is the core condition for that pair too — so the
//!   equivalence needs the empty petal to be *allowed*, not excluded.
//!   That is only visible on non-uniform families, since in an
//!   `m`-uniform family at most one member can equal a given `Y`.)
//! * **Distinctness of `F`.** On bitmasks set-equality is literal
//!   equality, so every family enumerated here is `Distinct`; that
//!   question is settled in Coq rather than here.

use crate::spread::{has_k_disjoint, Mask};

/// `Spread.link T F`: strip `t` out of the members of `f` that contain
/// it, and drop the members that do not.
pub fn link(t: Mask, f: &[Mask]) -> Vec<Mask> {
    f.iter().filter(|&&a| a & t == t).map(|&a| a & !t).collect()
}

/// `k` pairwise disjoint members of `f`, as a list of masks, if there
/// are any. The witness form of `spread::has_k_disjoint`.
pub fn k_disjoint_witness(f: &[Mask], k: usize) -> Option<Vec<Mask>> {
    fn go(f: &[Mask], used: Mask, need: usize, start: usize, acc: &mut Vec<Mask>) -> bool {
        if need == 0 {
            return true;
        }
        if f.len() < start + need {
            return false;
        }
        for i in start..f.len() {
            if f[i] & used == 0 {
                acc.push(f[i]);
                if go(f, used | f[i], need - 1, i + 1, acc) {
                    return true;
                }
                acc.pop();
            }
        }
        false
    }
    let mut acc = Vec::with_capacity(k);
    if go(f, 0, k, 0, &mut acc) {
        Some(acc)
    } else {
        None
    }
}

/// The right-hand side of the characterisation: a candidate core `Y`
/// whose link has `k` pairwise disjoint members, if one exists.
///
/// Quantifying `Y` over subsets of the ground set loses nothing: a `Y`
/// with an element outside it is contained in no member, so its link is
/// empty and only witnesses `k = 0`, which `Y = ∅` witnesses anyway.
pub fn link_core_witness(f: &[Mask], k: usize, ground: u32) -> Option<Mask> {
    (0..(1u32 << ground)).find(|&y| has_k_disjoint(&link(y, f), k))
}

/// Whether some link has `k` pairwise disjoint members.
pub fn has_k_disjoint_link(f: &[Mask], k: usize, ground: u32) -> bool {
    link_core_witness(f, k, ground).is_some()
}

/// Rebuild the sunflower a link witness stands for: the members of `f`
/// obtained by putting `y` back into each petal.
pub fn lift_petals(y: Mask, petals: &[Mask]) -> Vec<Mask> {
    petals.iter().map(|&b| b | y).collect()
}

/// All subsets of `{0, ..., ground-1}`, in increasing numeric order —
/// the enumeration for the non-uniform tests, where a member may equal
/// a candidate core.
pub fn all_subsets(ground: u32) -> Vec<Mask> {
    (0..(1u32 << ground)).collect()
}

/// Enumerate every family drawn from `sets`. The uniform case is
/// `testbed::for_each_family`; this takes the pool explicitly so the
/// non-uniform enumerations can use it too.
pub fn for_each_family_from<F: FnMut(&[Mask])>(sets: &[Mask], mut visit: F) {
    let n = sets.len();
    assert!(n <= 22, "2^{n} families is too many to enumerate");
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

#[cfg(test)]
mod tests {
    use super::*;

    fn set(elts: &[u32]) -> Mask {
        elts.iter().fold(0, |acc, &x| acc | 1 << x)
    }

    #[test]
    fn link_strips_the_core_and_drops_the_rest() {
        let f = vec![set(&[0, 1]), set(&[0, 2]), set(&[1, 2])];
        assert_eq!(link(set(&[0]), &f), vec![set(&[1]), set(&[2])]);
        assert_eq!(link(0, &f), f);
        assert_eq!(link(set(&[0, 1]), &f), vec![0]);
        assert_eq!(link(set(&[3]), &f), Vec::<Mask>::new());
    }

    #[test]
    fn a_star_is_a_disjoint_family_in_its_link() {
        // Three 2-sets through 0: a 3-sunflower with core {0}.
        let star = vec![set(&[0, 1]), set(&[0, 2]), set(&[0, 3])];
        assert!(!has_k_disjoint(&star, 3));
        assert_eq!(link_core_witness(&star, 3, 4), Some(set(&[0])));
    }

    #[test]
    fn k_disjoint_witness_agrees_with_the_predicate() {
        let f = vec![set(&[0, 1]), set(&[1, 2]), set(&[2, 3]), set(&[3, 4])];
        for k in 0..=4usize {
            assert_eq!(k_disjoint_witness(&f, k).is_some(), has_k_disjoint(&f, k));
        }
        let w = k_disjoint_witness(&f, 2).unwrap();
        assert_eq!(w.len(), 2);
        assert_eq!(w[0] & w[1], 0);
    }
}
