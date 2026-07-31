//! Kramer–Mesner, run: is there a record family with prescribed symmetry?
//!
//! `docs/roadmap.md` §12 gives the threshold at every uniformity, and
//! `extend.rs` has just shown that the Abbott–Hanson–Sauer families
//! cannot be pushed past it by adding sets — they are maximal on every
//! ground set. So a record family has *different symmetry*, and the
//! standard instrument for that is to prescribe a group and search its
//! orbits.
//!
//! Three questions, in increasing cost:
//!
//! * `b = 4`, target **32**, ground 11..16. `iota(4,10) <= 31` is
//!   exhaustive (`docs/roadmap.md` §5) and **ground 11 and up is
//!   untouched** — two independent unrestricted searches failed there.
//!   This is the cheapest live rung on the whole ladder.
//! * `b = 5`, target **101**, ground 15..20. Best known 54.
//! * `b = 6`, target **317**, ground 18..21. Best known 300, and the
//!   closest fraction of any rung (0.946).
//!
//! Usage:
//!
//! ```text
//!   cargo run --release --example kramer_mesner            # the campaign
//!   cargo run --release --example kramer_mesner -- check   # the differential checks only
//! ```
//!
//! Output is flushed line by line: a run that is killed part way still
//! reports every group it decided.

use std::io::Write;

use sunflower_formal::{intersecting, orbit};

fn line(s: &str) {
    println!("{s}");
    let _ = std::io::stdout().flush();
}

/// With the trivial group every orbit is a singleton, so the orbit
/// search *is* an unrestricted search. Running it against
/// `intersecting::iota`, which shares no code with it, is the
/// differential test that makes the prescribed-group runs believable.
///
/// `(b,g) = (4,8)` is **excluded and was run once by hand**: both
/// searches return 24, which is the tabulated `iota(4,8)`. It is out of
/// the standing list because the orbit search has no anchor symmetry to
/// exploit — `intersecting::iota` forces a member to be `{0,...,b-1}`
/// and this does not — so it takes a quarter of an hour where the rows
/// kept below take seconds. A check that costs more than the campaign
/// it guards is one a future session will delete rather than run.
fn differential_checks() {
    line("=== differential checks: the trivial group reproduces iota(b,g) ===");
    line("   b   g   target   found   target+1   exhausted   branch-and-bound");
    let known: &[(u32, u32, usize)] = &[
        (2, 3, 3),
        (2, 5, 3),
        (3, 5, 6),
        (3, 6, 10),
        (3, 7, 10),
        (4, 7, 15),
    ];
    for &(b, g, expect) in known {
        let trivial: Vec<orbit::Perm> = vec![(0..g).collect()];
        let orbits = orbit::orbits_on_subsets(g, b, &trivial);
        // The decision framing, both ways: the value must be reachable
        // and one more must not be. `best` is not a maximum -- the bound
        // discards every branch that cannot reach the target -- so the
        // pair of verdicts is what pins the value, not a single number.
        let hit = orbit::search_orbits(&orbits, expect, true, 4_000_000_000);
        let miss = orbit::search_orbits(&orbits, expect + 1, true, 4_000_000_000);
        let (bb, _, done) = intersecting::iota(g, b, 4_000_000_000, 0);
        assert!(hit.exhaustive && miss.exhaustive && done, "a check ran out of budget");
        assert!(
            hit.best >= expect,
            "the orbit search did not reach iota({b},{g}) = {expect}"
        );
        assert!(
            miss.best < expect + 1,
            "the orbit search reached {} at ({b},{g}), above the tabulated {expect}",
            miss.best
        );
        assert_eq!(bb, expect, "branch-and-bound disagrees at ({b},{g})");
        orbit::verify(&hit.best_family, b, true).expect("the witness does not verify");
        line(&format!(
            "  {b:>2}  {g:>2}   {expect:>6}   {:>5}   {:>8}   {:>9}   {bb:>16}",
            "yes",
            expect + 1,
            "yes"
        ));
    }
    line("");
}

/// One row of the campaign.
///
/// `usable` is the diagnostic that explains most of what follows: an
/// orbit can only be part of the family if it is *internally* consistent
/// — pairwise intersecting when that is required, and sunflower-free
/// within itself. For an intersecting family under a transitive group
/// that is a brutal condition: two translates of a `b`-set under a
/// cyclic group on `g > 2b` points are usually disjoint, so almost every
/// orbit is dead before the search starts.
fn run_row(b: u32, target: usize, grounds: &[u32], intersecting: bool, budget: u64) {
    line(&format!(
        "=== b = {b}, target {target}, {} , ground {:?} ===",
        if intersecting {
            "intersecting (iota directly)"
        } else {
            "general (cone: iota(b+1) >= this)"
        },
        grounds
    ));
    line("  ground   group                       |G|   orbits   usable   reached   nodes        verdict");
    line("           (`usable` = orbits that are internally consistent; `reached` is the largest");
    line("            family the search saw, NOT a maximum -- the bound discards every branch");
    line("            that cannot reach the target)");
    for &g in grounds {
        for (name, gens) in orbit::standard_groups(g) {
            let group = match orbit::group_closure(g, &gens, 20_000) {
                Some(gr) => gr,
                None => {
                    line(&format!(
                        "  {g:>6}   {name:<24} >20000        -        -         -   -            skipped (too large)"
                    ));
                    continue;
                }
            };
            let orbits = orbit::orbits_on_subsets(g, b, &group);
            let usable = orbits
                .iter()
                .filter(|o| orbit::verify(o, b, intersecting).is_ok())
                .count();
            let r = orbit::search_orbits(&orbits, target, intersecting, budget);
            let verdict = if r.best >= target {
                "*** FOUND ***"
            } else if r.exhaustive {
                "exhausted: none"
            } else {
                "budget exhausted"
            };
            if !r.best_family.is_empty() {
                orbit::verify(&r.best_family, b, intersecting)
                    .unwrap_or_else(|e| panic!("witness for {name} at ground {g} is invalid: {e}"));
            }
            line(&format!(
                "  {g:>6}   {name:<24} {:>5}   {:>6}   {:>6}   {:>7}   {:<11}  {verdict}",
                group.len(),
                orbits.len(),
                usable,
                r.best,
                r.nodes
            ));
            if r.best >= target {
                line(&format!("      family: {:?}", r.best_family));
            }
        }
    }
    line("");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    differential_checks();
    if args.iter().any(|a| a == "check") {
        return;
    }

    // First, directly: iota with prescribed symmetry. The `usable`
    // column is the point of running it at all.
    run_row(4, 32, &[11, 12, 13, 14, 15, 16], true, 200_000_000);

    // Then through the cone, `g(m) <= iota(m+1)`
    // (`Product.iota_at_least_g_pred`), which drops the intersecting
    // condition and drops the uniformity by one. The target is the
    // threshold at `m + 1`.
    //
    // `m = 3, target 32` is the same rung as the row above, reached the
    // other way: a 3-uniform sunflower-free family of 32 members gives
    // `iota(4) >= 32`, refutes `Sharp.AHSOptimal` outright, and gives
    // `f(3,3) >= 33`. The proved `N(3,g) <= 2g`
    // (`IotaGround.three_uniform_ground_bound`) forces `g >= 16`, and at
    // `g = 16` the bound would have to be met with equality.
    run_row(3, 32, &[16, 17, 18, 19, 20, 21, 22], false, 400_000_000);

    // `m = 5, target 317` gives `iota(6) >= 317`, the closest rung.
    run_row(5, 317, &[15, 16, 17, 18, 19, 20], false, 200_000_000);
}
