//! What stops `src/symbreak.rs` from being confidently wrong.
//!
//! The module adds three things the existing encoding did not have, and
//! each of them can be wrong in a way no verdict reveals:
//!
//! * a **counter** whose two directions must both hold, or a comparison
//!   between two points is not a constraint at all;
//! * **symmetry constraints** that are supposed to preserve satisfiability
//!   — an unsound one turns a SAT instance UNSAT, and UNSAT is exactly
//!   the verdict no witness can contradict;
//! * a **cube split** that is supposed to be a cover — a missing cube
//!   also reads as UNSAT.
//!
//! So: the counter is checked against a brute-force count, the symmetry
//! is checked by running every parameter with the constraints on and off
//! and demanding the same answer, the split is checked against the
//! unsplit instance, and the whole thing is checked against
//! `intersecting::iota`, which is an exhaustive branch-and-bound sharing
//! no code with any of it.

use sunflower_formal::intersecting;
use sunflower_formal::sat::{solve_cnf, Cnf, RawVerdict, Solver, Verdict};
use sunflower_formal::symbreak::{
    decide, decide_whole, degree_cubes, encode, sequence_cubes, solve_cube, SymOptions,
};

fn have_solver() -> bool {
    Solver::Cadical.available()
}

fn opts(kmax: usize) -> SymOptions {
    SymOptions {
        kmax,
        ..SymOptions::default()
    }
}

fn plain(kmax: usize) -> SymOptions {
    SymOptions {
        max_at_zero: false,
        sorted_blocks: false,
        degree_floor: false,
        exact_size: false,
        all_points_used: false,
        lex_ties: false,
        kmax,
    }
}

/// The exhaustive value, from the branch-and-bound. `budget` is generous
/// enough that `exhausted` is always true at these parameters; the
/// assertion says so rather than trusting it.
fn exhaustive_iota(ground: u32, b: u32) -> usize {
    let (best, _fam, exhausted) = intersecting::iota(ground, b, u64::MAX, 0);
    assert!(exhausted, "the branch-and-bound did not exhaust ({b},{ground})");
    best
}

/// The counter is an *iff*, checked against a brute-force count.
///
/// `n` free literals, a counter to `kmax`, and then for every `k` two
/// queries: "at least `k` holds while fewer than `k` literals are true"
/// and "at least `k` fails while at least `k` are true". Both must be
/// UNSAT. The first is the direction `Cnf::at_least` already had; the
/// second is the one this module needed and is the one a sequential
/// counter usually omits.
#[test]
fn the_order_counter_is_an_iff_in_both_directions() {
    if !have_solver() {
        eprintln!("skipping: cadical not on PATH");
        return;
    }
    for n in [1usize, 2, 5, 7] {
        for kmax in 1..=n {
            // Rebuild from scratch per query: the module's counter is
            // private, so it is exercised through `encode`-shaped use of
            // a bare `Cnf` here.
            for k in 1..=kmax {
                for (want_ge, cap) in [(true, k - 1), (false, k)] {
                    let mut cnf = Cnf::new();
                    let lits: Vec<i32> = (0..n).map(|_| cnf.new_var()).collect();
                    let ge = sunflower_formal::symbreak::order_counter_for_tests(
                        &mut cnf, &lits, kmax,
                    );
                    if want_ge {
                        // "at least k" asserted, but at most k-1 true.
                        cnf.add(vec![ge[k - 1]]);
                        cnf.at_most(&lits, cap);
                    } else {
                        // "at least k" denied, but at least k true.
                        cnf.add(vec![-ge[k - 1]]);
                        cnf.at_least(&lits, cap);
                    }
                    let v = solve_cnf(&cnf, Solver::Cadical, 60, "counter").unwrap();
                    assert_eq!(
                        v,
                        RawVerdict::Unsat,
                        "counter n={n} kmax={kmax} k={k} want_ge={want_ge} is not tight"
                    );
                }
            }
        }
    }
}

/// The encoding decides the values the exhaustive search decides.
///
/// `iota(3,6) = 10` is the seed of the whole 1972 tower and
/// `iota(4,8) = 24`, `iota(4,9) = 27` are the two rungs below the one
/// this session is aimed at. Each is checked from both sides: the value
/// is SAT and one more is UNSAT.
#[test]
fn the_symmetry_broken_encoding_agrees_with_the_exhaustive_search() {
    if !have_solver() {
        eprintln!("skipping: cadical not on PATH");
        return;
    }
    for (b, ground) in [(3u32, 5u32), (3, 6), (4, 6), (4, 7), (4, 8)] {
        let value = exhaustive_iota(ground, b);
        let at = decide(ground, b, value, opts(20), Solver::Cadical, 600).unwrap();
        assert!(
            matches!(at, Verdict::Sat(_)),
            "iota({b},{ground}) = {value} but the encoding says {} at {value}",
            at.label()
        );
        let above = decide(ground, b, value + 1, opts(20), Solver::Cadical, 600).unwrap();
        assert_eq!(
            above,
            Verdict::Unsat,
            "iota({b},{ground}) = {value} but the encoding does not refute {}",
            value + 1
        );
    }
}

/// The symmetry constraints move no answer.
///
/// This is the control §9 of `docs/roadmap.md` asked for and did not get
/// on the degree cap: run the same question with the restrictions on and
/// off and require the same verdict. An unsound restriction shows up
/// here as UNSAT-on, SAT-off.
#[test]
fn the_symmetry_constraints_change_no_answer() {
    if !have_solver() {
        eprintln!("skipping: cadical not on PATH");
        return;
    }
    for (b, ground) in [(3u32, 5u32), (3, 6), (4, 6), (4, 7)] {
        let value = exhaustive_iota(ground, b);
        for target in [value.saturating_sub(1).max(1), value, value + 1] {
            let on = decide(ground, b, target, opts(16), Solver::Cadical, 600).unwrap();
            let off = decide(ground, b, target, plain(16), Solver::Cadical, 600).unwrap();
            assert_eq!(
                on.label(),
                off.label(),
                "symmetry changed the verdict at iota({b},{ground}) >= {target}"
            );
        }
    }
}

/// The cube split answers the question it splits.
#[test]
fn the_cube_split_decides_the_same_question() {
    if !have_solver() {
        eprintln!("skipping: cadical not on PATH");
        return;
    }
    for (b, ground) in [(3u32, 6u32), (4, 7), (4, 8)] {
        let value = exhaustive_iota(ground, b);
        for target in [value, value + 1] {
            let split = decide(ground, b, target, opts(18), Solver::Cadical, 600).unwrap();
            let whole = decide_whole(ground, b, target, opts(18), Solver::Cadical, 600).unwrap();
            assert_eq!(
                split.label(),
                whole.label(),
                "the cube split disagrees with the unsplit instance at iota({b},{ground}) >= {target}"
            );
        }
    }
}

/// The cubes are a *cover*, and the check does not use the solver.
///
/// Cube `d` is `deg(0) >= d /\ ~(deg(0) >= d+1)`, and the list runs from
/// the instance's floor to its ceiling with the top cube one-sided. So
/// the only way a model escapes every cube is `deg(0) < floor` — which
/// the encoding asserts against — and that is what this checks: the
/// first cube's lower literal is the asserted floor, and consecutive
/// cubes' bounds abut with no gap.
#[test]
fn the_degree_cubes_abut_and_cover() {
    for (b, ground, target) in [(4u32, 9u32, 27usize), (4, 10, 32), (3, 6, 10)] {
        let inst = encode(ground, b, target, opts(20));
        let cubes = degree_cubes(&inst);
        assert!(!cubes.is_empty(), "no cubes at all");
        assert_eq!(cubes[0].0, inst.floor, "the split does not start at the floor");
        assert_eq!(
            cubes.last().unwrap().0,
            inst.kmax,
            "the split does not reach the ceiling"
        );
        for w in cubes.windows(2) {
            assert_eq!(w[1].0, w[0].0 + 1, "a gap between cubes {} and {}", w[0].0, w[1].0);
        }
        // Every cube but the last pins deg(0) from both sides; the last
        // is one-sided, which is what makes saturation harmless.
        for (d, lits) in &cubes {
            if *d < inst.kmax {
                assert_eq!(lits.len(), 2, "cube {d} is not two-sided");
            } else {
                assert_eq!(lits.len(), 1, "the top cube is not one-sided");
            }
        }
    }
}

/// The intersecting degree floor is arithmetic, and it is checked here
/// rather than only argued in a doc comment: every member of an
/// intersecting family meets the anchor, so the anchor's degrees sum to
/// at least `|F|` and the largest of them is at least `|F|/b`.
#[test]
fn the_degree_floor_holds_on_every_exhaustive_witness() {
    for (b, ground) in [(3u32, 5u32), (3, 6), (4, 6), (4, 7), (4, 8), (4, 9)] {
        let (best, fam, exhausted) = intersecting::iota(ground, b, u64::MAX, 0);
        assert!(exhausted, "not exhausted at ({b},{ground})");
        assert_eq!(best, fam.len());
        let anchor = fam[0];
        let mut sum = 0usize;
        for x in 0..ground {
            if anchor >> x & 1 == 1 {
                sum += fam.iter().filter(|s| *s >> x & 1 == 1).count();
            }
        }
        assert!(
            sum >= fam.len(),
            "the anchor's degrees sum to {sum} below |F| = {} at ({b},{ground})",
            fam.len()
        );
        let maxdeg = (0..ground)
            .map(|x| fam.iter().filter(|s| *s >> x & 1 == 1).count())
            .max()
            .unwrap_or(0);
        assert!(
            maxdeg >= best.div_ceil(b as usize),
            "max degree {maxdeg} below the floor {} at ({b},{ground})",
            best.div_ceil(b as usize)
        );
    }
}

/// The degree-sequence cubes are a cover, checked without the solver.
///
/// `sequence_cubes` enumerates the degree vectors the encoding admits:
/// `d_0` the maximum, each block non-increasing, `sum = b*t`, and every
/// entry at least one when `all_points_used` is on. If that enumeration
/// misses a vector, the models with that vector are in no cube and the
/// run reports UNSAT without having looked at them — the worst failure
/// this module can have. So it is checked against a brute-force sweep
/// over every vector in range, by code that shares nothing with the
/// recursion.
#[test]
fn the_degree_sequence_cubes_enumerate_every_admissible_vector() {
    for (b, ground, target, all_points) in [
        (3u32, 5u32, 8usize, true),
        (3, 6, 9, true),
        (4, 6, 12, false),
    ] {
        let mut o = opts(target);
        o.all_points_used = all_points;
        let inst = encode(ground, b, target, o);
        let cubes = sequence_cubes(&inst, o, &[], ground as usize, 1_000_000).expect("no split");
        let mine: std::collections::BTreeSet<Vec<usize>> =
            cubes.iter().map(|(s, _)| s.clone()).collect();
        assert_eq!(mine.len(), cubes.len(), "duplicate cube");

        // Brute force: every vector in [lo..=kmax]^ground, filtered.
        let g = ground as usize;
        let bb = b as usize;
        let lo = usize::from(all_points);
        let total = bb * target;
        let mut theirs: std::collections::BTreeSet<Vec<usize>> =
            std::collections::BTreeSet::new();
        let hi = inst.kmax.min(total);
        let mut v = vec![lo; g];
        loop {
            let ok = v[0] >= inst.floor
                && v.iter().all(|d| *d <= v[0])
                && v.iter().sum::<usize>() == total
                && (1..bb).all(|i| i + 1 >= bb || v[i] >= v[i + 1])
                && (bb..g).all(|i| i + 1 >= g || v[i] >= v[i + 1]);
            if ok {
                theirs.insert(v.clone());
            }
            // odometer
            let mut i = g;
            loop {
                if i == 0 {
                    break;
                }
                i -= 1;
                if v[i] < hi {
                    v[i] += 1;
                    for x in v.iter_mut().skip(i + 1) {
                        *x = lo;
                    }
                    break;
                }
                if i == 0 {
                    v[0] = hi + 1;
                }
            }
            if v[0] > hi {
                break;
            }
        }
        assert_eq!(
            mine, theirs,
            "the sequence split is not a cover at (b,g,t) = ({b},{ground},{target})"
        );
    }
}

/// And the finer split answers the question the coarser one answers.
///
/// Restricted to the *floor* value of `deg(0)`, which is the only kind
/// the driver ever refines: the number of sequences grows with the
/// deficiency `g*deg(0) - b*t`, so asking for all of them at once is
/// neither what the driver does nor affordable here.
#[test]
fn the_degree_sequence_split_decides_the_same_question() {
    if !have_solver() {
        eprintln!("skipping: cadical not on PATH");
        return;
    }
    for (b, ground) in [(3u32, 6u32), (4, 7), (4, 8)] {
        let value = exhaustive_iota(ground, b);
        for target in [value, value + 1] {
            let o = opts(target);
            let inst = encode(ground, b, target, o);
            let floor_cube: Vec<i32> = degree_cubes(&inst)
                .into_iter()
                .find(|(d, _)| *d == inst.floor)
                .expect("no floor cube")
                .1;
            let coarse = solve_cube(
                &inst,
                &floor_cube,
                Solver::Cadical,
                600,
                &format!("floor-{ground}-{b}-{target}"),
            )
            .unwrap();
            let cubes = sequence_cubes(&inst, o, &[inst.floor], ground as usize, 100_000).expect("no split");
            let mut sat = false;
            for (i, (_seq, cube)) in cubes.iter().enumerate() {
                let tag = format!("seq-{ground}-{b}-{target}-{i}");
                match solve_cube(&inst, cube, Solver::Cadical, 600, &tag).unwrap() {
                    Verdict::Sat(_) => {
                        sat = true;
                        break;
                    }
                    Verdict::Unsat => {}
                    Verdict::Unknown => panic!("cube {i} did not decide"),
                }
            }
            assert_eq!(
                sat,
                matches!(coarse, Verdict::Sat(_)),
                "the two splits disagree on the floor cube at iota({b},{ground}) >= {target}"
            );
        }
    }
}

/// The ladder refutes 32 members on every ground set it can afford here.
///
/// `docs/roadmap.md` §33.5 records the whole run, including the grounds
/// this test does not have the budget for. What is asserted here is the
/// part that is cheap: **no intersecting 3-sunflower-free family of
/// 4-sets has 32 members on nine points or fewer**, which is the whole
/// ladder below the frontier and is where `iota(4,9) = 27` lives.
#[test]
fn no_thirty_two_member_family_of_four_sets_fits_on_nine_points() {
    if !have_solver() {
        eprintln!("skipping: cadical not on PATH");
        return;
    }
    for ground in 4u32..=9 {
        let mut o = opts(32);
        o.all_points_used = true;
        let v = decide(ground, 4, 32, o, Solver::Cadical, 900).unwrap();
        assert_eq!(
            v,
            Verdict::Unsat,
            "iota(4,{ground}) >= 32 was not refuted (got {})",
            v.label()
        );
    }
}
