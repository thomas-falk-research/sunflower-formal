//! Generator-program search, and the counting ceiling that says where to
//! point it.
//!
//! Two things are pinned here.
//!
//! **The ceiling.** Sunflower-freeness caps the degree of a `(b-1)`-set
//! at 2 and of a `(b-2)`-set at 6 — the first because the link is a
//! 1-uniform family with matching number at most 2, the second because
//! the link is then a graph with `Δ <= 2` and `ν <= 2`, hence at most two
//! disjoint triangles. Counting members against the subsets they contain
//! turns each into a bound on `|F|`, and the smaller of the two is what a
//! family on `n` points can possibly have. This is what tells a search
//! which ground sets can hold a record and which cannot — and it says
//! §9's `b = 5` SAT row, run at ground 10, was asked at a ground whose
//! ceiling is 72 against a threshold of 101.
//!
//! **The generators.** Each is a program emitting a pool of candidate
//! blocks; its score is the largest verified intersecting sunflower-free
//! subfamily inside. The control is the unrestricted pool, and a
//! structured pool that scores below the control is a hypothesis worse
//! than no hypothesis. Every number below is of that kind, and every one
//! of them is negative — recorded so the next session does not re-derive
//! the same generators.

use sunflower_formal::genprog::{
    all_blocks, complementary_half, evaluate, least_ground, link_bound, size_ceiling,
    top_link_bound, transversals, twisted_transversals,
};
use sunflower_formal::orbit;

/// The two link bounds, and which one binds where.
#[test]
fn the_counting_ceiling_is_what_it_is_computed_to_be() {
    // b = 3: the (b-1)-set bound binds, and at six points it is *exactly*
    // iota(3) = 10. The extremal object of the 1972 tower saturates the
    // counting bound at its own ground set.
    assert_eq!(top_link_bound(3, 6), 10);
    assert_eq!(size_ceiling(3, 6), 10);

    // b = 4: the (b-2)-set bound takes over from nine points on.
    assert_eq!(top_link_bound(4, 8), 28);
    assert_eq!(link_bound(4, 8), 28);
    assert_eq!(size_ceiling(4, 9), 36);
    assert_eq!(size_ceiling(4, 11), 55);

    // b = 5: the row this session was pointed at.
    let row: [(u64, u64); 6] = [(10, 72), (11, 99), (12, 132), (13, 171), (14, 218), (15, 273)];
    for (n, want) in row {
        assert_eq!(size_ceiling(5, n), want, "b = 5, n = {n}");
    }
}

/// `iota(5) >= 101` — the threshold that would beat Abbott–Hanson–Sauer —
/// is **impossible below twelve points**, and `iota(4) >= 51`, which
/// would do the same through `double` and `cone`, is impossible below
/// eleven.
///
/// This is the fact that makes the search targetable. §9 ran the `b = 5`
/// SAT row at ground 10, whose ceiling is 72: no answer at that ground
/// could ever have reached the threshold.
#[test]
fn a_record_needs_a_ground_set_and_the_bound_says_which() {
    assert_eq!(least_ground(5, 101), 12);
    assert!(size_ceiling(5, 11) < 101);
    assert!(size_ceiling(5, 12) >= 101);
    assert_eq!(size_ceiling(5, 10), 72, "the ground the b=5 SAT row was run at");

    assert_eq!(least_ground(4, 51), 11);
    // and the current records sit far below their own ceilings
    assert!(78 < size_ceiling(5, 15), "iota(5) >= 78 lives on fifteen points");
    assert!(27 < size_ceiling(4, 9), "iota(4) >= 27 lives on nine points");
}

/// The framework rediscovers the value it must: the unrestricted pool at
/// `b = 3` on six points contains a 10-member family and no larger one,
/// which is `iota(3) = 10`. This is the differential check on the whole
/// generator apparatus — the evaluation shares no code with
/// `intersecting::iota`, and every family it returns is re-verified by
/// `orbit::verify`.
#[test]
fn the_evaluation_reproduces_iota_three() {
    let pool = all_blocks(6, 3);
    assert_eq!(pool.blocks.len(), 20);
    let s = evaluate(&pool, 1, 50_000_000);
    assert_eq!(s.best, 10, "iota(3) = 10");
    assert!(s.exhaustive);
    orbit::verify(&s.family, 3, true).unwrap();

    // and it is the ceiling, exactly
    assert_eq!(s.best as u64, size_ceiling(3, 6));
}

/// Asked as a decision, the unrestricted pool at `b = 4` on eight points
/// exhausts without a 28-member family — even though 28 is exactly the
/// counting ceiling there. The ceiling is not attained at `b = 4`, which
/// is the first place the pattern of `b = 3` breaks.
#[test]
fn the_ceiling_is_not_attained_at_uniformity_four() {
    assert_eq!(size_ceiling(4, 8), 28);
    let pool = all_blocks(8, 4);
    let s = evaluate(&pool, 28, 400_000_000);
    assert_eq!(s.best, 0, "no 28-member family on eight points");
    assert!(s.exhaustive, "and the search exhausted rather than gave up");
}

/// **Every structured generator scores below the unrestricted control.**
///
/// The pools encode hypotheses about what a record family looks like —
/// a grid of transversals (the shape of every product construction), a
/// cocycle-twisted grid (the algebraic move behind the modern cap-set
/// constructions, and the one §5 says is missing from the catalogue of
/// `cone`/`double`/`substitute`), and a complementary selection (the
/// shape of `iota(3) = 10`, which really is one triple from each
/// complementary pair of `[6]`).
///
/// None of them helps. The transversal shape caps out very low, and the
/// complementary selection reaches 8 at `b = 3` where the true value is
/// 10 — so the 2-(6,3,2) design is *not* the selection any weight rule
/// makes, which refutes the hypothesis that suggested the generator.
#[test]
fn the_structured_pools_all_lose_to_no_hypothesis() {
    let budget = 20_000_000;

    // The transversal shape: 4-uniform on a 4x3 grid, twelve points.
    let t = evaluate(&transversals(4, 3), 1, budget);
    assert!(t.best <= 13, "transversals 4x3 reached {}", t.best);

    // Twisting it by a weighted cocycle only removes blocks.
    for q in 2..=4u32 {
        for c in 0..q {
            let w = evaluate(&twisted_transversals(4, 3, q, c), 1, budget);
            assert!(w.best <= t.best, "the twist beat the untwisted grid");
        }
    }

    // The complementary selection at b = 3, where the truth is 10.
    let mut best_complementary = 0;
    for wm in 2..=5u32 {
        for r in 0..wm {
            let c = evaluate(&complementary_half(3, wm, r), 1, budget);
            best_complementary = best_complementary.max(c.best);
        }
    }
    assert!(
        best_complementary < 10,
        "a weight rule found the 2-(6,3,2) design after all: {best_complementary}"
    );

    // The control, on the same ground set, does reach it.
    assert_eq!(evaluate(&all_blocks(6, 3), 1, budget).best, 10);
}

/// The generator pools are all genuinely intersecting and genuinely
/// `b`-uniform, so a family found inside one needs no further hypothesis
/// to be a witness.
#[test]
fn pools_are_well_formed() {
    for p in [transversals(4, 3), twisted_transversals(4, 3, 3, 1), complementary_half(4, 3, 1)] {
        assert!(!p.blocks.is_empty(), "{} is empty", p.name);
        for &x in &p.blocks {
            assert_eq!(x.count_ones(), p.b, "{}: wrong uniformity", p.name);
            assert!(x < (1u64 << p.ground), "{}: block outside the ground", p.name);
        }
        let mut sorted = p.blocks.clone();
        sorted.sort_unstable();
        sorted.dedup();
        assert_eq!(sorted.len(), p.blocks.len(), "{}: repeated block", p.name);
    }
    // the complementary selection really does take one of each pair
    let p = complementary_half(4, 3, 1);
    assert_eq!(p.blocks.len(), 35, "C(8,4)/2 = 35");
    let full: u64 = (1u64 << 8) - 1;
    for &x in &p.blocks {
        assert!(!p.blocks.contains(&(full ^ x)), "both halves of a pair are in");
    }
}
