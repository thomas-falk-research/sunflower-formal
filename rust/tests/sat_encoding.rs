//! The SAT encoding, checked against the search it is meant to replace.
//!
//! A wrong encoding is the failure mode that matters here: it would
//! answer quickly and confidently, and there would be nothing to notice.
//! Four defences, all of them exhaustive over the range stated:
//!
//! 1. **Differential.** On every parameter the branch-and-bound can
//!    still decide, the SAT value and the searched value agree —
//!    `iota(b,g)` for `b <= 4` and `N(m,g)` for `m <= 3`. Two programs
//!    with nothing in common but the definition.
//! 2. **Never trust a model.** Every satisfying assignment is decoded to
//!    a family and re-checked by `intersecting::verify`, which shares no
//!    code with the encoder. `sat::solve` panics rather than returns if
//!    a model does not check out, so this is enforced everywhere, not
//!    only here.
//! 3. **Two solvers.** UNSAT is the verdict no witness can confirm, so
//!    it is the one that gets a second opinion: `solve_agreed` runs two
//!    independent solvers and panics if they disagree. Same discipline
//!    as `Reflect.rao_witness_agrees` on the Coq side.
//! 4. **The degree cap changes no answer.** `IotaGround.link_degree_ground_bound`
//!    proves `deg(x) <= N(b-1,g-1)`, so adding it as a cardinality
//!    constraint is sound by a theorem. Adding a constraint that was
//!    *not* implied would silently turn maxima into minima of something
//!    else; the check is that every value is the same with it and
//!    without.
//!
//! Skipped, loudly, if no solver is installed: a test that quietly
//! passes when the thing it tests is absent is worse than no test.

use sunflower_formal::ground::max_sunflower_free;
use sunflower_formal::intersecting::{iota, verify};
use sunflower_formal::sat::*;

const BUDGET: u64 = 20_000_000_000_000;

fn require(s: Solver) -> bool {
    if s.available() {
        return true;
    }
    eprintln!(
        "SKIPPING: {} is not installed (apt-get install -y cadical cryptominisat)",
        s.binary()
    );
    false
}

/// The largest `t` with a SAT answer, walking up from 1. Panics on
/// UNKNOWN: every parameter used here is decided in seconds, so a
/// timeout is a regression rather than a result.
fn sat_value(ground: u32, b: u32, intersecting: bool, cap: Option<usize>, s: Solver) -> usize {
    let mut best = 0;
    for t in 1..=200 {
        let v = if intersecting {
            decide_iota(ground, b, t, cap, s, 0)
        } else {
            decide_general(ground, b, t, cap, s, 0)
        }
        .expect("solver failed to run");
        match v {
            Verdict::Sat(fam) => {
                verify(&fam, b, intersecting).expect("model failed re-verification");
                assert!(fam.len() >= t, "model smaller than the target");
                best = t;
            }
            Verdict::Unsat => return best,
            Verdict::Unknown => panic!("timed out at ({b},{ground}) target {t}"),
        }
    }
    panic!("ladder ran off the end at ({b},{ground})");
}

// ---------------------------------------------------------------------
// 1. Differential against the exhaustive search.
// ---------------------------------------------------------------------

#[test]
fn sat_agrees_with_the_search_on_iota() {
    if !require(Solver::Cadical) {
        return;
    }
    for (b, g) in [
        (2u32, 2u32), (2, 3), (2, 5), (2, 8),
        (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 9),
        (4, 4), (4, 5), (4, 6), (4, 7),
    ] {
        let (searched, _, done) = iota(g, b, BUDGET, 0);
        assert!(done, "the search did not finish at ({b},{g})");
        let encoded = sat_value(g, b, true, None, Solver::Cadical);
        assert_eq!(encoded, searched, "iota({b},{g})");
    }
}

#[test]
fn sat_agrees_with_the_search_on_the_general_row() {
    if !require(Solver::Cadical) {
        return;
    }
    for (m, g) in [
        (1u32, 3u32), (1, 6),
        (2, 3), (2, 4), (2, 5), (2, 6), (2, 8),
        (3, 4), (3, 5), (3, 6), (3, 7),
    ] {
        let (searched, _, done) = max_sunflower_free(g, m, BUDGET);
        assert!(done, "the search did not finish at ({m},{g})");
        let encoded = sat_value(g, m, false, None, Solver::Cadical);
        assert_eq!(encoded, searched, "N({m},{g})");
    }
}

// ---------------------------------------------------------------------
// 2. The degree cap is sound: it is a theorem, and it changes nothing.
// ---------------------------------------------------------------------

/// `IotaGround.link_degree_ground_bound` gives `deg(x) <= N(b-1,g-1)`.
/// Adding it must not move any value. If it did, either the theorem or
/// the encoding would be wrong, and this is the only place that could
/// tell them apart.
#[test]
fn the_degree_cap_changes_no_answer() {
    if !require(Solver::Cadical) {
        return;
    }
    for (b, g) in [(3u32, 5u32), (3, 6), (3, 7), (4, 5), (4, 6), (4, 7)] {
        let (prev, _, done) = max_sunflower_free(g - 1, b - 1, BUDGET);
        assert!(done);
        let free = sat_value(g, b, true, None, Solver::Cadical);
        let capped = sat_value(g, b, true, Some(prev), Solver::Cadical);
        assert_eq!(free, capped, "iota({b},{g}) moved when the cap was added");

        let free = sat_value(g, b, false, None, Solver::Cadical);
        let capped = sat_value(g, b, false, Some(prev), Solver::Cadical);
        assert_eq!(free, capped, "N({b},{g}) moved when the cap was added");
    }
}

// ---------------------------------------------------------------------
// 3. Two independent solvers, on the verdict no witness can confirm.
// ---------------------------------------------------------------------

#[test]
fn two_solvers_agree() {
    if !require(Solver::Cadical) || !require(Solver::CryptoMiniSat) {
        return;
    }
    // One SAT instance and one UNSAT instance at each of three
    // parameters. `solve_agreed` panics on disagreement.
    for (b, g, value) in [(2u32, 6u32, 3usize), (3, 6, 10), (4, 7, 15)] {
        let sat = encode(g, b, value, true, SecondMember::Free, None);
        let v = solve_agreed(&sat, Solver::Cadical, Solver::CryptoMiniSat, 0)
            .expect("solvers failed to run");
        assert!(matches!(v, Verdict::Sat(_)), "iota({b},{g}) >= {value}");

        let unsat = encode(g, b, value + 1, true, SecondMember::Free, None);
        let v = solve_agreed(&unsat, Solver::Cadical, Solver::CryptoMiniSat, 0)
            .expect("solvers failed to run");
        assert_eq!(v, Verdict::Unsat, "iota({b},{g}) >= {}", value + 1);
    }
}

// ---------------------------------------------------------------------
// 4. The encoding's own pieces.
// ---------------------------------------------------------------------

/// The cardinality encoder, against brute force. `at_least` is the only
/// part of the encoding that is not a direct transcription of the
/// definitions, so it is the part that can be wrong quietly.
#[test]
fn the_cardinality_encoder_is_exact() {
    if !require(Solver::Cadical) {
        return;
    }
    for n in 1..=6usize {
        for t in 0..=(n + 1) {
            let mut cnf = Cnf::new();
            let lits: Vec<i32> = (0..n).map(|_| cnf.new_var()).collect();
            cnf.at_least(&lits, t);
            // Force exactly the first `f` literals true, the rest false,
            // and check satisfiability matches `f >= t`.
            for f in 0..=n {
                let mut c = cnf.clone();
                for (i, l) in lits.iter().enumerate() {
                    c.add(vec![if i < f { *l } else { -*l }]);
                }
                let inst = Instance {
                    sets: Vec::new(),
                    vars: Vec::new(),
                    cnf: c,
                    ground: 1,
                    b: 1,
                    target: 0,
                    intersecting: false,
                };
                let v = solve(&inst, Solver::Cadical, 0).expect("solver failed");
                let expect_sat = f >= t;
                assert_eq!(
                    matches!(v, Verdict::Sat(_)),
                    expect_sat,
                    "at_least(n={n}, t={t}) with {f} true"
                );
            }
        }
    }
}

/// The anchor is forced, which is only sound because relabelling the
/// ground set preserves everything (`DirectSum.relabel_preserves`).
/// Check the consequence rather than the justification: every witness
/// the encoder returns contains `{0,...,b-1}`, and the values still
/// match the unanchored search.
#[test]
fn the_anchor_is_in_every_witness() {
    if !require(Solver::Cadical) {
        return;
    }
    for (b, g) in [(2u32, 5u32), (3, 6), (4, 7)] {
        let (searched, _, done) = iota(g, b, BUDGET, 0);
        assert!(done);
        let inst = encode(g, b, searched, true, SecondMember::Free, None);
        match solve(&inst, Solver::Cadical, 0).expect("solver failed") {
            Verdict::Sat(fam) => {
                let anchor: u32 = (1 << b) - 1;
                assert!(fam.contains(&anchor), "the anchor is missing at ({b},{g})");
                assert_eq!(fam.len(), searched);
                verify(&fam, b, true).expect("model failed re-verification");
            }
            other => panic!("expected SAT at ({b},{g}), got {}", other.label()),
        }
    }
}

/// The orbit split of the second member: SAT on some orbit exactly when
/// SAT with the second member free. This is the reduction
/// `intersecting::iota_decide` carries, and it is sound only for
/// intersecting families, so it is worth checking rather than assuming.
#[test]
fn the_orbit_split_decides_the_same_question() {
    if !require(Solver::Cadical) {
        return;
    }
    for (b, g) in [(3u32, 6u32), (3, 7), (4, 6), (4, 7)] {
        for t in 2..=12usize {
            let free = encode(g, b, t, true, SecondMember::Free, None);
            let whole = matches!(
                solve(&free, Solver::Cadical, 0).expect("solver failed"),
                Verdict::Sat(_)
            );
            let split = matches!(
                decide_iota(g, b, t, None, Solver::Cadical, 0).expect("solver failed"),
                Verdict::Sat(_)
            );
            assert_eq!(whole, split, "orbit split at ({b},{g}) target {t}");
        }
    }
}

// ---------------------------------------------------------------------
// 5. What the encoding found, pinned without needing a solver.
// ---------------------------------------------------------------------

/// The ten-point witness for `N(3,10) >= 16`, the value
/// `coq/SliceRank.v` names as the one the general row turns on. It is
/// checked here by the brute-force verifier rather than re-found, so
/// this test reproduces the result on a machine with no SAT solver at
/// all — and `coq/IotaGround.ground10_max` is the same sixteen members.
///
/// Its shape is worth reading: the first four are *all* the triples of
/// `{0,1,2,3}`, which is exactly `Compression.compressed_bound`'s
/// extremal family at `m = 3`; the rest are the pairs from `{0,1}` on a
/// triangle over `{4,5,6}` and the pairs from `{2,3}` on a triangle over
/// `{7,8,9}`.
#[test]
fn the_ten_point_witness_is_what_it_claims() {
    let f: Vec<u16> = [
        [0, 1, 2], [0, 1, 3], [0, 2, 3], [1, 2, 3],
        [0, 4, 5], [1, 4, 5], [0, 4, 6], [1, 4, 6], [0, 5, 6], [1, 5, 6],
        [2, 7, 8], [3, 7, 8], [2, 7, 9], [3, 7, 9], [2, 8, 9], [3, 8, 9],
    ]
    .iter()
    .map(|t| t.iter().fold(0u16, |m, &x| m | 1 << x))
    .collect();

    assert_eq!(f.len(), 16);
    sunflower_formal::ground::verify(&f, 3).expect("not a sunflower-free 3-uniform family");

    // Ten points, and every one of them used.
    for x in 0..10u32 {
        assert!(f.iter().any(|&s| s >> x & 1 == 1), "point {x} unused");
    }
    assert!(f.iter().all(|&s| s < (1 << 10)), "a member leaves the ground set");

    // Degrees (6,6,6,6,4,4,4,4,4,4): sixteen members, forty-eight
    // incidences, and the proved cap `deg(x) <= N(2,9) = 6` met exactly
    // on the four points of the K4.
    let degs: Vec<usize> = (0..10)
        .map(|x| f.iter().filter(|&&s| s >> x & 1 == 1).count())
        .collect();
    assert_eq!(degs, vec![6, 6, 6, 6, 4, 4, 4, 4, 4, 4]);
    assert_eq!(degs.iter().sum::<usize>(), 3 * f.len());

    // It beats the nine-point maximum, which is what makes the row
    // climb: `N(3,9) = 14`, exhaustively, in `tests/iota_ground.rs`.
    assert!(f.len() > 14);

    // And it is inside the proved cap `N(3,g) <= 2g`.
    assert!(f.len() <= 20);
}

/// The solver finds at least as much as the pinned witness. Separate
/// from the test above so that the pinned result survives a machine with
/// no solver, and so that a regression in the encoder is not masked by
/// the hard-coded family.
#[test]
fn the_solver_still_reaches_sixteen_on_ten_points() {
    if !require(Solver::Cadical) {
        return;
    }
    match decide_general(10, 3, 16, None, Solver::Cadical, 120).expect("solver failed") {
        Verdict::Sat(fam) => {
            assert!(fam.len() >= 16);
            let as16: Vec<u16> = fam.iter().map(|&x| x as u16).collect();
            sunflower_formal::ground::verify(&as16, 3).expect("model failed re-verification");
        }
        other => panic!("expected SAT for N(3,10) >= 16, got {}", other.label()),
    }
}
