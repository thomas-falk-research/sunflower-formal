//! What the two-phase cube driver may skip, and what it may not.
//!
//! `examples/iota_sym.rs` decides a rung in two phases: every `deg(0)`
//! cube gets a `slice`, and the ones that stall are re-split by degree
//! sequence and re-run with the full `seconds`. A cube whose sequence
//! split exceeds the cap does not re-split. It enters phase two *in
//! exactly the form it has already failed in*, and the driver used to
//! re-run it anyway.
//!
//! That re-run is free of information and not free of time. Each cube is a
//! fresh solver process — nothing is carried between phases, no clauses,
//! no restarts — so an equal budget on an unchanged instance produces the
//! identical verdict. At `(4,11,28)`, `deg(0) = 17`, with
//! `--slice 45 --seconds 45`, the measured cost was 45.1 s to UNKNOWN and
//! then 45.1 s more to the same UNKNOWN. At the twelve-hour budgets the
//! hard cubes need, that is twelve hours per cube.
//!
//! Skipping the re-run is a scheduling decision, and the danger in it is
//! not wasted time but a wrong verdict: a cube skipped for lack of budget
//! is still **undecided**, and if the driver forgot it, a rung with one
//! undecided cube would report UNSAT. So this file pins six things: the
//! budget rule itself; the determinism it rests on; that a carried cube is
//! counted, so a rung holding one cannot read UNSAT; that the cubes which
//! refuse to split at full prefix do split under a shorter one, which is
//! the reason any of this matters; and the monotonicity in the target that
//! lets one rung's timings say anything about another's; and the solver
//! exit codes that let a crash be told from a budget at all (§51).

use sunflower_formal::intersecting;
use sunflower_formal::sat::{Solver, Verdict};
use sunflower_formal::symbreak::{
    decide, degree_cubes, encode, phase_two_adds_budget, plan_phase_two, sequence_cubes,
    solve_cube, SymOptions,
};

fn have_solver() -> bool {
    Solver::Cadical.available()
}

fn opts() -> SymOptions {
    SymOptions::default()
}

/// The rule, at every combination that reaches it. Zero means "no limit"
/// on both flags, which is what makes this worth writing down: the two
/// zeros mean opposite things about which phase is longer.
#[test]
fn the_budget_rule_answers_the_question_the_driver_asks() {
    // Sliced, and phase two really is longer: re-run.
    assert!(phase_two_adds_budget(60, 86400), "the ordinary rung shape");
    assert!(phase_two_adds_budget(120, 121), "one second more is still more");
    // Sliced finitely, phase two unlimited: re-run.
    assert!(phase_two_adds_budget(120, 0), "unlimited beats any slice");
    // Equal budgets: the re-run is the same computation. Skip.
    assert!(!phase_two_adds_budget(43200, 43200), "the twelve-hour trap");
    assert!(!phase_two_adds_budget(45, 45), "the measured case");
    // Phase two *shorter* than the slice: certainly no gain.
    assert!(!phase_two_adds_budget(300, 60));
    // No slicing at all: phase one already spent `seconds`, so phase two
    // repeats it exactly. This is the case a naive `seconds > slice` test
    // gets wrong, since `seconds > 0` is true.
    assert!(!phase_two_adds_budget(0, 43200), "slice 0 means phase one had it all");
    // Nothing exceeds an unlimited phase one.
    assert!(!phase_two_adds_budget(0, 0));
}

/// The determinism the skip rests on: a fresh process, the same cube, the
/// same budget, the same verdict. No state crosses between phases, so
/// phase two cannot pick up where phase one stopped.
///
/// The cube is `(4,11,28)` at `deg(0) = 17` — one of the seven that were
/// still open at eleven points — with a budget far below what it needs, so
/// both runs time out. That the second run is *not* faster is the point:
/// if the solver were carrying learnt clauses across processes, the re-run
/// would be cheap and worth doing.
#[test]
fn a_repeat_of_an_unrefined_cube_repeats_its_verdict() {
    if !have_solver() {
        eprintln!("cadical not installed; skipping");
        return;
    }
    let inst = encode(11, 4, 28, opts());
    let cube = vec![inst.deg_ge[0][16], -inst.deg_ge[0][17]];
    let first = solve_cube(&inst, &cube, Solver::Cadical, 5, "budget-a").unwrap();
    let second = solve_cube(&inst, &cube, Solver::Cadical, 5, "budget-b").unwrap();
    assert_eq!(
        matches!(first, Verdict::Unknown),
        matches!(second, Verdict::Unknown),
        "the same cube at the same budget changed its mind between runs"
    );
    assert!(
        matches!(first, Verdict::Unknown),
        "deg(0) = 17 at eleven points is supposed to be hard; five seconds decided it, \
         so this test is no longer testing what it says"
    );
}

/// The `deg(0)` split at eleven points, target 28, refines by degree
/// sequence — but how far it refines depends on `deg(0)`, and the
/// dependence runs the wrong way for the cubes that stall.
///
/// The deficiency `g*deg(0) - b*t` is what the enumeration partitions, and
/// it grows linearly in `deg(0)`, so the split grows with it. The small
/// `deg(0)` cubes — where the near-regular families live — split into a
/// handful; the large ones blow past any usable cap.
#[test]
fn the_sequence_split_grows_with_the_top_degree() {
    let inst = encode(11, 4, 28, opts());
    let n = |d0: usize, cap: usize| {
        sequence_cubes(&inst, opts(), &[d0], 11, cap).map(|cs| cs.len())
    };
    assert_eq!(n(11, 1_000_000), Some(224));
    assert_eq!(n(12, 1_000_000), Some(7857));
    assert_eq!(n(13, 1_000_000), Some(80062));
    // Monotone, and steeply: each step multiplies the count by five or
    // more, which is why the cap is reached and not approached.
    assert!(224 < 7857 && 7857 < 80062);
    // Past that the full split is unusable. `None` here means "more than
    // the cap", not "no split exists" — the distinction matters, because
    // the next test is what to do about it.
    assert_eq!(n(15, 1_000_000), None, "deg(0) = 15 is supposed to overflow");
    assert_eq!(n(17, 1_000_000), None, "deg(0) = 17 is supposed to overflow");
}

/// The answer for a cube that will not split: shorten the prefix, not
/// lengthen the budget.
///
/// `sequence_cubes` can fix only the first `prefix` degrees and leave the
/// rest free, subject to being fillable. That is still a partition of the
/// models, so it is still a sound split — it is just coarser. At ten
/// points a split into 144 sub-cubes beat the cube whole and one into 1939
/// lost, so the target is a few hundred, and a prefix of three or four
/// lands there for exactly the cubes that the full split cannot touch.
#[test]
fn the_cubes_that_will_not_split_at_full_prefix_split_at_a_short_one() {
    let inst = encode(11, 4, 28, opts());
    let n = |d0: usize, prefix: usize| {
        sequence_cubes(&inst, opts(), &[d0], prefix, 1_000_000).map(|cs| cs.len())
    };
    // All seven cubes still open at eleven points, at the two prefixes
    // worth using. Every one of them lands in the few-hundred range that
    // won at ten points, including the three the full split cannot touch
    // at all, and none of them needs the longer budget §48.1 asked for.
    let table = [
        (11, 12, 53),
        (12, 44, 288),
        (13, 90, 529),
        (14, 120, 680),
        (15, 136, 816),
        (16, 153, 969),
        (17, 171, 1140),
    ];
    for (d0, p3, p4) in table {
        assert_eq!(n(d0, 3), Some(p3), "deg(0) = {d0} at prefix three");
        assert_eq!(n(d0, 4), Some(p4), "deg(0) = {d0} at prefix four");
    }
    // The floor cube is the exception the plan turns on: its count barely
    // moves with the prefix, so it can be pinned completely and still stay
    // in the winning regime, while deg(0) = 15 cannot be pinned past
    // three. That asymmetry is why the prefix is chosen per cube.
    assert_eq!(
        (3..=8).map(|p| n(11, p).unwrap()).collect::<Vec<_>>(),
        vec![12, 53, 57, 64, 75, 94]
    );
    assert_eq!(n(11, 11), Some(224), "the floor cube splits fully at 224");
    assert!(n(15, 5).unwrap() > 300, "deg(0) = 15 leaves the regime by prefix five");

    // The three that overflow whole are exactly the three at the top.
    for d0 in [15, 16, 17] {
        assert_eq!(n(d0, 11), None, "deg(0) = {d0} is supposed to overflow whole");
    }
    // The number the plan turns on: the whole remaining eleven-point
    // problem, split at prefix three, is this many independent sub-cubes.
    let total: usize = table.iter().map(|(_, p3, _)| p3).sum();
    assert_eq!(total, 726);
    // And `--cubecap 300` is the setting that admits all seven and nothing
    // larger by accident.
    assert!(table.iter().all(|(_, p3, _)| *p3 <= 300));
    assert!(table.iter().any(|(_, _, p4)| *p4 > 300));
    // How far over the cap the smallest of them is, exactly: `None` above
    // is a cap being hit, and this says by how much, so the sequence
    // 224, 7857, 80062, 417711, 1420570 can be read as the single curve it
    // is rather than as four numbers and a failure.
    assert_eq!(
        sequence_cubes(&inst, opts(), &[15], 11, 2_000_000).map(|cs| cs.len()),
        Some(1_420_570)
    );
    // The prefix is a dial, and it is monotone in the obvious direction.
    let counts: Vec<usize> = (3..=6).map(|p| n(15, p).unwrap()).collect();
    assert!(
        counts.windows(2).all(|w| w[0] < w[1]),
        "a longer prefix must not give fewer sub-cubes: {counts:?}"
    );
    // A prefix of one is the coarse cube back again — the split degenerates
    // to the `deg(0)` cube it started from, which is the sanity check that
    // the dial spans the whole range.
    assert_eq!(n(15, 1), Some(1));
}

/// Which of two targets is the harder instance — checked on the encoding,
/// not assumed from the kernel.
///
/// `Product.IotaAtLeast_antitone` (audited, closed) says uniformity,
/// distinctness, intersecting-ness and sunflower-freeness all pass to
/// subfamilies, so a 32-member family contains a 28-member one and UNSAT
/// at 28 implies UNSAT at 32. §49.2 leans on that to say the target-32
/// timings in `docs/ladder/iota4_11.deg13.p3.tsv` are a *lower* bound on
/// what target 28 will cost.
///
/// The kernel statement is about families. The instances the ladder runs
/// carry more: symmetry breaking, a degree floor, and `exact_size`, which
/// asks for a family of **exactly** `t` members — and "exactly" is not
/// obviously monotone. It transfers because `all_points_used` is off, so
/// the instance asks for a family on *at most* `ground` points and the
/// trimmed subfamily is still a model. That is an argument about the
/// encoding, so it is checked against the encoding: the verdict must go
/// SAT while `t` is reachable and UNSAT once it is not, with exactly one
/// crossing, at the exhaustive value.
///
/// A non-monotone encoding would show up here as SAT above the value or
/// UNSAT below it, and would silently invalidate every comparison the
/// ladder makes between targets.
#[test]
fn the_encoding_is_monotone_in_the_target() {
    if !have_solver() {
        eprintln!("cadical not installed; skipping");
        return;
    }
    for (b, ground) in [(3u32, 5u32), (3, 6), (4, 7)] {
        let (value, _fam, exhausted) = intersecting::iota(ground, b, u64::MAX, 0);
        assert!(exhausted, "the branch-and-bound did not exhaust ({b},{ground})");
        for t in 1..=value + 2 {
            let v = decide(ground, b, t, SymOptions { kmax: 20, ..opts() }, Solver::Cadical, 600)
                .unwrap();
            let sat = matches!(v, Verdict::Sat(_));
            assert_eq!(
                sat,
                t <= value,
                "iota({b},{ground}) = {value}, but the encoding says {} at target {t} \
                 -- the verdict is not monotone and no comparison between targets is safe",
                v.label()
            );
        }
    }
}

/// The assertion the whole fix turns on, now that `plan_phase_two` is in
/// the library and a test can reach it: **a rung holding a carried cube
/// cannot report UNSAT.**
///
/// Phase one at `(4,11,28)` leaves seven cubes stalled. With a `cubecap`
/// of 300 and the full prefix, only `deg(0) = 11` refines (224 sub-cubes);
/// the other six exceed the cap and keep their coarse form. Whether those
/// six are re-run or carried is decided by the budget, and the two
/// outcomes must differ in exactly one way: the work scheduled. What must
/// **not** differ is whether an undecided cube can vanish.
#[test]
fn a_carried_cube_cannot_become_an_unsat() {
    let inst = encode(11, 4, 28, opts());
    let coarse: Vec<(String, Vec<i32>)> = degree_cubes(&inst)
        .into_iter()
        .map(|(d, l)| (format!("g=11 deg(0)={d}"), l))
        .collect();
    let stalled: Vec<usize> = (11..=17).collect();

    // Equal budgets: the six unrefined cubes are carried, not re-run.
    let skip = plan_phase_two(&inst, opts(), &coarse, &stalled, true, 11, 300, 3, 3);
    assert_eq!(skip.refined, 1, "only deg(0) = 11 fits under a cap of 300");
    assert_eq!(skip.fine.len(), 224, "and it contributes its 224 sub-cubes");
    assert_eq!(skip.carried.len(), 6, "the other six are carried");
    // The point. Even if every scheduled sub-cube comes back UNSAT, the
    // rung is not UNSAT, because six cubes were never decided.
    assert_eq!(skip.at_limit(0), 6);
    assert!(skip.at_limit(0) > 0, "a rung with a carried cube must not read UNSAT");

    // A bigger phase-two budget: the same six are re-run instead, so
    // nothing is carried and an all-UNSAT phase two really is UNSAT.
    let run = plan_phase_two(&inst, opts(), &coarse, &stalled, true, 11, 300, 60, 43200);
    assert_eq!(run.refined, 1);
    assert_eq!(run.carried.len(), 0);
    assert_eq!(run.fine.len(), 224 + 6, "the six go forward whole");
    assert_eq!(run.at_limit(0), 0, "nothing undecided, so UNSAT is available");

    // Nothing is dropped under either budget. `refined` cubes contribute
    // their sub-cubes to `fine`; every other stalled cube appears once,
    // either whole in `fine` or by name in `carried`. So the unrefined six
    // are all still accounted for in both plans — the budget changes where
    // they are, never whether they exist.
    for (name, p) in [("skip", &skip), ("run", &run)] {
        let unrefined_whole = p.fine.len() - 224;
        assert_eq!(
            unrefined_whole + p.carried.len(),
            stalled.len() - p.refined,
            "{name}: a stalled cube went missing"
        );
    }
}

/// What `sat::run_solver` assumes about the programs it shells out to, and
/// the reason it now has to assume anything at all.
///
/// Until §51 the exit status was read for nothing but reaping the child.
/// A solver that segfaults or is killed writes nothing to stdout, and
/// empty stdout parses as `Unknown` — the *same value a clean timeout
/// produces*. So "the solver died" and "the budget ran out" were the same
/// observation, and on 2026-08-28 that cost 55.6 h: a cryptominisat5 run
/// died 48.5 h into its budget, was read as a stall, and the driver spent
/// a second full budget re-solving the identical cube.
///
/// Telling them apart means knowing which exit codes are normal, and that
/// is a fact about cadical and cryptominisat5, not about this repository —
/// so it is measured here rather than trusted. The DIMACS convention is 10
/// SAT / 20 UNSAT; each solver's own timeout flag adds one more code, and
/// those are the ones that must NOT read as crashes, because every
/// `UNKNOWN` the ladder has ever recorded came out of that path.
#[test]
fn the_solver_exit_codes_the_crash_check_rests_on() {
    if !have_solver() {
        eprintln!("cadical not installed; skipping");
        return;
    }
    let dir = std::env::temp_dir();
    let unsat = dir.join("sf-exitcode-unsat.cnf");
    let sat = dir.join("sf-exitcode-sat.cnf");
    std::fs::write(&unsat, "p cnf 1 2\n1 0\n-1 0\n").unwrap();
    std::fs::write(&sat, "p cnf 1 1\n1 0\n").unwrap();

    let code = |bin: &str, args: &[&str]| -> Option<i32> {
        std::process::Command::new(bin)
            .args(args)
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::null())
            .status()
            .ok()
            .and_then(|s| s.code())
    };

    // The verdict codes, which are the DIMACS convention.
    assert_eq!(code("cadical", &[unsat.to_str().unwrap()]), Some(20));
    assert_eq!(code("cadical", &[sat.to_str().unwrap()]), Some(10));

    // The timeout code. This is the one that matters: `-t` on an instance
    // it cannot finish must stay inside the normal set, or every stalled
    // cube in the ladder would now be reported as a crash.
    let hard = encode(11, 4, 32, opts());
    let hard_path = dir.join("sf-exitcode-hard.cnf");
    std::fs::write(&hard_path, hard.cnf.to_dimacs()).unwrap();
    let t = code("cadical", &["-t", "3", hard_path.to_str().unwrap()]);
    assert_eq!(t, Some(0), "a cadical timeout must not look like a crash");
    assert!(
        [Some(0), Some(10), Some(15), Some(20)].contains(&t),
        "cadical's timeout code left the set sat.rs treats as normal"
    );

    if Solver::CryptoMiniSat.available() {
        assert_eq!(code("cryptominisat5", &["--verb", "0", unsat.to_str().unwrap()]), Some(20));
        let t = code(
            "cryptominisat5",
            &["--verb", "0", "--maxtime", "3", hard_path.to_str().unwrap()],
        );
        assert_eq!(t, Some(15), "a cryptominisat5 timeout must not look like a crash");
    }

    for p in [unsat, sat, hard_path] {
        let _ = std::fs::remove_file(p);
    }
}

/// The cover a checkpoint must exhaust is the one the *driver* enumerates,
/// and two models were in the tree disagreeing about what that is.
///
/// `docs/ladder/iota4_11.deg13.tsv` told a future session
/// "THE CUBE IS UNSAT ONLY WHEN ALL 1939 SUB-CUBES ARE UNSAT", under a
/// table of "corrected counts, superseding the figures an earlier session
/// quoted". Every row of that table is the count under
/// `all_points_used = true`. The driver runs with it **false** — that is
/// `SymOptions::default()`, and `examples/iota_sym.rs` sets it from no
/// flag — so its split of `deg(0) = 13` is 1949, and the live run prints
/// exactly that. Ten sub-cubes separate the two.
///
/// Why the cross-check the file cites did not catch it: it checked
/// `deg(0) = 12`, where both models give 19. That is the one value in the
/// table where they agree, so it confirms nothing about which is being
/// used. The discriminating cases are every other row.
///
/// Why it was not fatal, and why relying on that silently is still the
/// hazard: the ten extra sequences are exactly the ones carrying a point
/// of degree zero, so each asks for a 32-member family on at most ten
/// points, and `iota(4,10) = 27 < 32` (§46) refutes all ten. The
/// arithmetic is safe because of a theorem the file does not cite. A
/// checkpoint stopping at 1939 banked rows would read "cube closed" having
/// never attempted ten of its sub-cubes, and UNSAT is the verdict no
/// witness contradicts.
#[test]
fn the_split_cover_is_the_one_the_driver_runs() {
    let n = |o: SymOptions, d0: usize, prefix: usize| {
        let inst = encode(11, 4, 32, o);
        sequence_cubes(&inst, o, &[d0], prefix, 2_000_000).map(|cs| cs.len())
    };
    let loose = SymOptions::default();
    let tight = SymOptions { all_points_used: true, ..SymOptions::default() };
    assert!(!loose.all_points_used, "the driver's default is the loose model");

    // The two tables that were in the tree, both at target 32. `loose` is
    // what `docs/ladder/iota4_11.cryptominisat5.tsv` records and what the
    // driver runs; `tight` is what `iota4_11.deg13.tsv` called a
    // correction of it.
    let rows = [
        // deg(0), driver's cover, all_points_used cover
        (12usize, 19usize, 19usize),
        (13, 1949, 1939),
        (14, 32797, 31624),
        (15, 238850, 220047),
        (16, 1045128, 914505),
    ];
    for (d0, wide, narrow) in rows {
        assert_eq!(n(loose, d0, 11), Some(wide), "driver cover at deg(0) = {d0}");
        assert_eq!(n(tight, d0, 11), Some(narrow), "all_points_used cover at deg(0) = {d0}");
    }

    // The reason a cross-check at deg(0) = 12 proves nothing, stated so it
    // cannot be rediscovered by hand a third time.
    assert_eq!(n(loose, 12, 11), n(tight, 12, 11), "the two models agree at deg(0) = 12");
    for (d0, wide, narrow) in rows.iter().skip(1) {
        assert!(wide > narrow, "and disagree at every other deg(0) = {d0}");
    }

    // Tightening can only ever remove sequences, never add: the narrow
    // model is a sub-family of the wide one, so a run under the wide model
    // never misses a case the narrow one would have caught.
    for (d0, wide, narrow) in rows {
        let w: std::collections::HashSet<Vec<usize>> =
            sequence_cubes(&encode(11, 4, 32, loose), loose, &[d0], 11, 2_000_000)
                .unwrap()
                .into_iter()
                .map(|(s, _)| s)
                .collect();
        let t: std::collections::HashSet<Vec<usize>> =
            sequence_cubes(&encode(11, 4, 32, tight), tight, &[d0], 11, 2_000_000)
                .unwrap()
                .into_iter()
                .map(|(s, _)| s)
                .collect();
        assert!(t.is_subset(&w), "deg(0) = {d0}: the tight cover must sit inside the wide one");
        assert_eq!(w.len() - t.len(), wide - narrow);
        // And what the difference *is*: a point of degree zero, every time.
        assert!(
            w.difference(&t).all(|s| s.contains(&0)),
            "deg(0) = {d0}: the extra sequences must be the unused-point ones"
        );
    }

    // The prefix-3 split of cube 13 is 27 under either model, which is why
    // that number is the one figure the two files never disagreed about.
    assert_eq!(n(loose, 13, 3), Some(27));
    assert_eq!(n(tight, 13, 3), Some(27));
    // And prefix four is 171, not the 167 the driver's own doc comment said.
    assert_eq!(n(loose, 13, 4), Some(171));
}

/// What a prefix-3 sub-cube of cube 13 actually has to decide.
///
/// §50.3 proposed re-running the cube-13 second opinion over the prefix-3
/// split at `--seconds 7200`, on the strength of "five landed between
/// 136.1 s and 491.4 s, nine did not at 600 s" attributed to
/// `docs/ladder/iota4_11.deg13.p3.tsv`. Those fourteen rows are in
/// `iota4_11.deg13.tsv`, the **full** split. The p3 file's own four rows
/// are UNKNOWN at 2400.1 s under cadical, and its own recorded verdict is
/// "TOO COARSE, and the budget is the result".
///
/// This says why in one number rather than by citation: the enumeration is
/// most-extreme-first, so the four sub-cubes ever attempted are the four
/// largest, and the largest of them has to decide 559 full sub-cubes.
#[test]
fn the_prefix_three_cubes_of_thirteen_are_not_a_working_granularity() {
    let o = opts();
    let inst = encode(11, 4, 32, o);
    let full = sequence_cubes(&inst, o, &[13], 11, 2_000_000).unwrap();
    let p3 = sequence_cubes(&inst, o, &[13], 3, 2_000_000).unwrap();
    assert_eq!(full.len(), 1949);
    assert_eq!(p3.len(), 27);

    let mut buckets: std::collections::BTreeMap<Vec<usize>, usize> = Default::default();
    for (seq, _) in &full {
        *buckets.entry(seq[..3].to_vec()).or_insert(0) += 1;
    }
    // The split is a partition: every full sub-cube lands under exactly one
    // prefix-3 cube, and no prefix-3 cube is empty.
    assert_eq!(buckets.values().sum::<usize>(), 1949);
    assert_eq!(buckets.len(), p3.len());

    // The enumeration is lexicographically descending, so the four the
    // cadical pass attempted are simply its first four — and they are the
    // wrong four to spend a budget on. 559 + 327 + 181 + 94 = 1161 of the
    // 1949: three fifths of the cube in four pieces, against a mean bucket
    // of 1949/27 = 72.
    let order: Vec<usize> = p3.iter().map(|(s, _)| buckets[&s[..3].to_vec()]).collect();
    assert_eq!(&order[..4], &[559, 327, 181, 94], "the first four in enumeration order");
    assert_eq!(order[..4].iter().sum::<usize>(), 1161);
    assert_eq!(order[0], *buckets.values().max().unwrap(), "the very first cube is the largest");

    // Not the four largest, though, and the difference is the point: the
    // second-largest *family* of sequences, [13, 12, 12] with 246, sits at
    // index eight, so a pass that dies inside its first four has not even
    // reached it. Front-loading is by lex order, not by cost.
    let mut all: Vec<usize> = buckets.values().copied().collect();
    all.sort_unstable_by(|a, b| b.cmp(a));
    assert_eq!(&all[..4], &[559, 327, 246, 181]);
    assert_eq!(order.iter().position(|&n| n == 246), Some(8));

    // And the cheap ones are at the far end: the smallest prefix-3 cubes
    // hold a single full sub-cube each, at indices 14, 23 and 26. A
    // budget-limited pass over this split in enumeration order banks
    // nothing, because it spends the whole budget on the big end first.
    assert_eq!(*all.last().unwrap(), 1);
    let ones: Vec<usize> =
        order.iter().enumerate().filter(|(_, &n)| n == 1).map(|(i, _)| i).collect();
    assert_eq!(ones, vec![14, 23, 26]);
}
