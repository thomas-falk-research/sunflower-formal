//! Falsification of the link characterisation of sunflowers.
//!
//! The claim under test:
//!
//! ```text
//!     ContainsKSunflower k F   ⟺   ∃ Y, HasKDisjoint k (link Y F)
//! ```
//!
//! — a `k`-sunflower with core `Y` is exactly `k` members through `Y`
//! whose petals are pairwise disjoint. If it holds it makes
//! `TwoUniform.sunflower_shape` the two cases `Y = ∅` and `Y = {v}` of
//! a statement true at every uniformity, and turns the existing
//! `link`-based reduction from a one-directional lift into a
//! characterisation.
//!
//! This file runs before the Coq proof, not after it. The left-hand
//! side is decided by `sunflower.rs`, the brute-force pairwise-
//! intersection detector, which knows nothing about links; the
//! right-hand side by `link.rs`, which knows nothing about
//! intersections. They are enumerated against each other over every
//! family drawn from a small ground set.
//!
//! The four things the tests aim at, in the order they would break:
//!
//! 1. **Both directions, uniform.** Ground 5 and 6 at `m = 2, 3`,
//!    `k = 2, 3, 4`.
//! 2. **A member equal to the core.** Only visible without uniformity:
//!    in an `m`-uniform family at most one member can equal a given
//!    `Y`, so the empty petal never has a second petal to be disjoint
//!    from. Over *all* subsets of a ground set it does, and the
//!    equivalence then requires the empty petal to be allowed rather
//!    than excluded — `∅ ∩ A = ∅` is the core condition for that pair
//!    too. `Sunflower.pairwise_disjoint_sunflower` carries a
//!    nonemptiness hypothesis that would rule this out, which is why
//!    the case is worth pinning down.
//! 3. **Degenerate `k`.** `k = 0` and `k = 1`, where "sunflower" is
//!    vacuous on one side and the link is empty on the other.
//! 4. **Witness-level agreement.** Not just that the two booleans
//!    match, but that the core of a found sunflower is a valid `Y`,
//!    and that lifting `k` disjoint petals back through `Y` yields a
//!    family the independent detector certifies as a `k`-sunflower
//!    with core exactly `Y`.

use sunflower_formal::link::{
    all_subsets, for_each_family_from, k_disjoint_witness, lift_petals, link, link_core_witness,
};
use sunflower_formal::spread::{family_to_coq, has_k_disjoint, mask_to_set, subsets_of_size, Mask};
use sunflower_formal::sunflower::{find_k_sunflower, is_k_sunflower};
use sunflower_formal::testbed::for_each_family;

/// The left-hand side, decided independently of anything in `link.rs`.
fn contains_k_sunflower(f: &[Mask], k: usize) -> bool {
    let sets: Vec<Vec<u32>> = f.iter().map(|&a| mask_to_set(a)).collect();
    match k {
        // `find_k_sunflower` declines below k = 2; the Coq definition
        // does not. `ContainsKSunflower 0 F` holds always (the empty
        // sub-family), and `ContainsKSunflower 1 F` exactly when F is
        // nonempty (a one-member sub-family, whose pairwise condition
        // is vacuous).
        0 => true,
        1 => !f.is_empty(),
        _ => find_k_sunflower(&sets, k).is_some(),
    }
}

/// The core of the sunflower a link witness stands for, checked by the
/// independent detector: put `y` back into each of `k` disjoint petals
/// and ask whether the result really is a `k`-sunflower with core `y`.
fn lifted_witness_is_a_sunflower(f: &[Mask], y: Mask, k: usize) -> Result<(), String> {
    let petals = match k_disjoint_witness(&link(y, f), k) {
        Some(p) => p,
        None => return Err(format!("no {k} disjoint petals over Y = {y:b}")),
    };
    let members = lift_petals(y, &petals);
    for &a in &members {
        if !f.contains(&a) {
            return Err(format!(
                "lifted member {} is not in {}",
                family_to_coq(&[a]),
                family_to_coq(f)
            ));
        }
    }
    let sets: Vec<Vec<u32>> = members.iter().map(|&a| mask_to_set(a)).collect();
    let indices: Vec<usize> = (0..k).collect();
    match is_k_sunflower(&sets, &indices) {
        Some(core) if core == mask_to_set(y) => Ok(()),
        Some(core) => Err(format!(
            "lift over Y = {} gave a sunflower with core {:?}",
            family_to_coq(&[y]),
            core
        )),
        None => Err(format!(
            "lift over Y = {} is not a sunflower: {}",
            family_to_coq(&[y]),
            family_to_coq(&members)
        )),
    }
}

/// One family, one `k`: check the equivalence and, when it holds, that
/// the witnesses cross over in both directions.
fn check(f: &[Mask], k: usize, ground: u32) {
    let lhs = contains_k_sunflower(f, k);
    let rhs = link_core_witness(f, k, ground);
    assert_eq!(
        lhs,
        rhs.is_some(),
        "k = {k}: ContainsKSunflower = {lhs} but the link side = {} on {}",
        rhs.is_some(),
        family_to_coq(f)
    );
    if k < 2 {
        return;
    }
    if let Some(y) = rhs {
        // ⟸ at the level of witnesses.
        lifted_witness_is_a_sunflower(f, y, k)
            .unwrap_or_else(|e| panic!("on {}: {e}", family_to_coq(f)));
        // ⟹ at the level of witnesses: the core the detector reports
        // is itself a valid Y, not merely *some* Y being valid.
        let sets: Vec<Vec<u32>> = f.iter().map(|&a| mask_to_set(a)).collect();
        let found = find_k_sunflower(&sets, k).expect("lhs holds");
        let core: Mask = found.core.iter().fold(0, |acc, &x| acc | 1 << x);
        assert!(
            has_k_disjoint(&link(core, f), k),
            "the core {} of a found {k}-sunflower is not a valid Y on {}",
            family_to_coq(&[core]),
            family_to_coq(f)
        );
    }
}

// ---------------------------------------------------------------
// 1. Uniform families
// ---------------------------------------------------------------

/// Uniformity 2, both ground sets, `k = 2, 3, 4`. At `m = 2` the
/// characterisation must specialise to `TwoUniform.
/// two_uniform_sunflower_iff`: the only candidate cores that can carry
/// `k >= 2` disjoint petals are `∅` and the singletons.
#[test]
fn equivalence_holds_on_every_2_uniform_family() {
    for &ground in &[5u32, 6] {
        for k in 0..=4usize {
            for_each_family(ground, 2, |f| check(f, k, ground));
        }
    }
}

/// Uniformity 3. This is the case the characterisation is *for*: at
/// `m = 3` sunflower-freeness is no longer the two graph parameters,
/// so if the equivalence survives here it is saying something the
/// uniformity-2 characterisation does not.
#[test]
fn equivalence_holds_on_every_3_uniform_family() {
    for k in 0..=4usize {
        for_each_family(5, 3, |f| check(f, k, 5));
    }
    // C(6,3) = 20, so 2^20 families; run the two k that matter.
    for k in [2usize, 3] {
        for_each_family(6, 3, |f| check(f, k, 6));
    }
}

// ---------------------------------------------------------------
// 2. The member-equal-to-the-core case
// ---------------------------------------------------------------

/// Without uniformity a family can contain `Y` itself alongside sets
/// that properly contain it, so a link can have the empty petal
/// *together with* nonempty ones. That is the configuration the
/// equivalence has to get right, and the only place the answer is not
/// forced.
#[test]
fn equivalence_holds_on_every_family_over_four_points() {
    let pool = all_subsets(4); // all 16 subsets, ∅ included
    for k in 0..=3usize {
        for_each_family_from(&pool, |f| check(f, k, 4));
    }
}

/// The case above, in the smallest form, spelled out: `{1}` is the core
/// and also a member. `{{1}, {1,2}, {1,3}}` is a 3-sunflower with core
/// `{1}` — every pairwise intersection is `{1}` — and its link over
/// `{1}` is `{∅, {2}, {3}}`, three pairwise disjoint sets.
#[test]
fn a_member_equal_to_the_core_is_a_petal_of_its_own() {
    let f: Vec<Mask> = vec![0b010, 0b110, 0b1010];
    assert_eq!(link(0b010, &f), vec![0b000, 0b100, 0b1000]);
    assert!(has_k_disjoint(&link(0b010, &f), 3));
    assert!(contains_k_sunflower(&f, 3));
    lifted_witness_is_a_sunflower(&f, 0b010, 3).unwrap();
    // And the empty petal is doing the work: dropping the member equal
    // to the core leaves only two petals.
    assert!(!has_k_disjoint(&link(0b010, &f[1..]), 3));
    assert!(!contains_k_sunflower(&f[1..], 3));
}

// ---------------------------------------------------------------
// 3. What the characterisation says about the two-uniform case
// ---------------------------------------------------------------

/// `TwoUniform.two_uniform_sunflower_iff` says a distinct 2-uniform
/// family has a `k`-sunflower iff it has `k` pairwise disjoint members
/// or a vertex of degree `k`. Under the characterisation those are the
/// links over `Y = ∅` and over `Y = {v}` — and no other `Y` can
/// contribute, because a link over a larger `Y` has at most one
/// member. Checking that the *restricted* search over
/// `{∅} ∪ singletons` gives the same verdict as the full one over all
/// `2^ground` candidate cores is the two-uniform theorem re-derived
/// from the general statement.
#[test]
fn at_uniformity_two_only_the_empty_core_and_the_singletons_matter() {
    for &ground in &[5u32, 6] {
        for k in 2..=4usize {
            for_each_family(ground, 2, |f| {
                let restricted = (0..ground)
                    .map(|v| 1u32 << v)
                    .chain(std::iter::once(0))
                    .any(|y| has_k_disjoint(&link(y, f), k));
                assert_eq!(
                    restricted,
                    link_core_witness(f, k, ground).is_some(),
                    "k = {k}: a core of size >= 2 carries a {k}-matching on {}",
                    family_to_coq(f)
                );
            });
        }
    }
}

/// The same statement one level down: at uniformity 2 the link over
/// `{v}` has `deg [v] F` members, all of them singletons, so it has `k`
/// pairwise disjoint members exactly when `deg [v] F >= k`. This is the
/// half of `two_uniform_sunflower_iff` that reads "some vertex has
/// degree `k`", stated as a fact about links.
#[test]
fn a_two_uniform_link_over_a_vertex_is_its_degree() {
    for &ground in &[5u32, 6] {
        for_each_family(ground, 2, |f| {
            for v in 0..ground {
                let l = link(1 << v, f);
                let deg = sunflower_formal::spread::deg(1 << v, f);
                assert_eq!(l.len(), deg);
                for k in 0..=deg + 1 {
                    assert_eq!(
                        has_k_disjoint(&l, k),
                        k <= deg,
                        "link over {{{v}}} of {} is not a set of {deg} singletons",
                        family_to_coq(f)
                    );
                }
            }
        });
    }
}

// ---------------------------------------------------------------
// 4. Sanity: the pieces the equivalence is assembled from
// ---------------------------------------------------------------

/// `Spread.length_link`: a link has exactly `deg Y F` members.
#[test]
fn link_length_is_the_degree() {
    for &(ground, m) in &[(5u32, 2u32), (5, 3), (6, 2)] {
        for_each_family(ground, m, |f| {
            for y in 0..(1u32 << ground) {
                assert_eq!(link(y, f).len(), sunflower_formal::spread::deg(y, f));
            }
        });
    }
}

/// A link is `(m - |Y|)`-uniform (`Spread.link_uniform`) and distinct
/// (`Spread.link_distinct`) — on masks, distinctness is literal, and
/// it holds because `Y ⊆ A` makes `A ↦ A \ Y` injective.
#[test]
fn a_link_is_uniform_and_distinct() {
    for &(ground, m) in &[(5u32, 2u32), (5, 3)] {
        for_each_family(ground, m, |f| {
            for y in 0..(1u32 << ground) {
                let l = link(y, f);
                assert!(sunflower_formal::spread::is_distinct(&l));
                if l.is_empty() {
                    continue;
                }
                // Only cores actually contained in a member survive.
                assert!(y.count_ones() <= m);
                assert!(sunflower_formal::spread::is_uniform(
                    m - y.count_ones(),
                    &l
                ));
            }
        });
    }
}

/// The empty core recovers the plain disjointness question: `link ∅ F`
/// is `F`, so `HasKDisjoint k F` is the `Y = ∅` case of the right-hand
/// side. This is what makes the characterisation a generalisation of
/// `Audit.no_k_disjoint_of_no_sunflower` rather than a different claim.
#[test]
fn the_empty_core_is_plain_disjointness() {
    for &(ground, m) in &[(5u32, 2u32), (5, 3)] {
        for_each_family(ground, m, |f| {
            assert_eq!(link(0, f), f.to_vec());
            for k in 0..=3usize {
                assert_eq!(has_k_disjoint(&link(0, f), k), has_k_disjoint(f, k));
            }
        });
    }
}

/// Every candidate core that works is a subset of some member — the
/// justification for quantifying `Y` over subsets of the ground set
/// rather than over all finite sets, and for the `cands`-style
/// restriction a Coq decision procedure would want.
#[test]
fn a_working_core_is_contained_in_a_member() {
    for &(ground, m) in &[(5u32, 2u32), (5, 3)] {
        for k in 1..=3usize {
            for_each_family(ground, m, |f| {
                if let Some(y) = link_core_witness(f, k, ground) {
                    assert!(
                        f.iter().any(|&a| a & y == y),
                        "core {} lies in no member of {}",
                        family_to_coq(&[y]),
                        family_to_coq(f)
                    );
                }
            });
        }
    }
}

/// A larger ground set than exhaustive enumeration can reach, sampled.
/// `2^C(7,3) = 2^35` families is out of range; a deterministic
/// pseudo-random sample of them is not, and a counterexample that only
/// appears at ground 7 would be the kind worth knowing about.
#[test]
fn equivalence_survives_sampling_at_ground_seven() {
    let sets = subsets_of_size(7, 3);
    let mut state: u64 = 0x2545_F491_4F6C_DD1D;
    for _ in 0..40_000 {
        let mut f: Vec<Mask> = Vec::new();
        for &s in &sets {
            state = state
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            // Keep families sparse enough to be interesting: a dense
            // family contains a sunflower for trivial reasons.
            if state >> 60 < 4 {
                f.push(s);
            }
        }
        for k in 2..=3usize {
            check(&f, k, 7);
        }
    }
}
