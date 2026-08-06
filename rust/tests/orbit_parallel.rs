//! The root-split parallel search agrees with the sequential one, and
//! its checkpoint resumes rather than restarts.
//!
//! `orbit::search_orbits_parallel` is sound only because every pruning
//! test in `search_orbits` is against the fixed `target` and never
//! against the incumbent `best`, so root subtrees share nothing. That is
//! an argument, and an argument about a search is worth exactly what a
//! differential test says it is worth: every claim below is checked
//! against the sequential routine on the same input.
//!
//! What is *not* claimed: that `best` agrees. Neither routine computes a
//! maximum — the bound prunes branches that cannot reach `target`, and
//! such a branch may still contain families larger than the current
//! incumbent — so `best` depends on visit order and the parallel visit
//! order differs by construction. The decision, and exhaustiveness of a
//! negative, are what must agree, and those are what a caller may use.

use sunflower_formal::genprog::all_blocks;
use sunflower_formal::orbit::{search_orbits, search_orbits_parallel, verify};

fn singletons(g: u32, b: u32) -> Vec<Vec<u64>> {
    all_blocks(g, b).blocks.iter().map(|&x| vec![x]).collect()
}

/// The decision agrees, on both sides of the threshold, at every
/// parameter small enough to exhaust twice.
#[test]
fn parallel_and_sequential_decide_alike() {
    for (g, b) in [(6u32, 3u32), (7, 3), (8, 4), (9, 4)] {
        let orbits = singletons(g, b);
        for target in 1..=12usize {
            let seq = search_orbits(&orbits, target, true, u64::MAX);
            let par = search_orbits_parallel(&orbits, target, true, u64::MAX, 4, None);

            assert_eq!(
                seq.best >= target,
                par.best >= target,
                "decision differs at (g,b,target) = ({g},{b},{target}): \
                 sequential best {}, parallel best {}",
                seq.best,
                par.best
            );
            assert!(
                seq.exhaustive && par.exhaustive,
                "both should exhaust at ({g},{b},{target})"
            );
            if par.best >= target {
                verify(&par.best_family, b, true).unwrap_or_else(|e| {
                    panic!("parallel family at ({g},{b},{target}) does not verify: {e}")
                });
                assert!(par.best_family.len() >= target);
            }
        }
    }
}

/// `iota(3) = 10` is the value the whole 1972 tower rests on, and the
/// parallel search reproduces it: a family of 10 exists on six points and
/// one of 11 provably does not.
#[test]
fn the_parallel_search_reproduces_iota_three() {
    let orbits = singletons(6, 3);
    let yes = search_orbits_parallel(&orbits, 10, true, u64::MAX, 4, None);
    assert!(yes.best >= 10, "iota(3) >= 10");
    verify(&yes.best_family, 3, true).expect("the 10-member family verifies");

    let no = search_orbits_parallel(&orbits, 11, true, u64::MAX, 4, None);
    assert!(no.best < 11, "iota(3) < 11");
    assert!(no.exhaustive, "and that negative is exhaustive");
}

/// A checkpoint resumes rather than restarts.
///
/// The first run is given a budget that truncates it. The second run,
/// pointed at the same checkpoint file, must skip every root subproblem
/// the first finished — measurable as strictly fewer nodes than a fresh
/// exhaustive run — and must still reach the same verdict.
#[test]
fn the_checkpoint_resumes_rather_than_restarts() {
    let dir = std::env::temp_dir().join(format!("sf-ckpt-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("frontier.txt");
    let _ = std::fs::remove_file(&path);

    // An exhaustive negative, which is the case that matters here: it is
    // the one where the whole space really is traversed, so "resumed"
    // and "fresh" are comparable. 30.8M nodes fresh, so a budget of 2M
    // finishes some root subproblems and abandons one.
    let orbits = singletons(8, 4);
    let target = 25;

    let fresh = search_orbits_parallel(&orbits, target, true, u64::MAX, 4, None);
    assert!(fresh.best < target && fresh.exhaustive);

    // A truncated first pass.
    // Self-calibrating, and the fraction has to be this high for a
    // reason worth recording: with singleton orbits the root subproblems
    // are wildly uneven — root `i` is "the families whose lowest-indexed
    // member is block `i`", and the first few carry almost all the work —
    // so a budget of a tenth of the total completes *nothing*. Root
    // splitting buys the parallelism it promises; what it does not buy is
    // a fine-grained checkpoint near the top of the tree.
    let first = search_orbits_parallel(&orbits, target, true, fresh.nodes * 9 / 10, 4, Some(&path));
    assert!(!first.exhaustive, "the small budget should truncate");
    let recorded = std::fs::read_to_string(&path)
        .expect("a truncated run should still have recorded its completed subproblems");
    let done: Vec<&str> = recorded.lines().filter(|l| !l.trim().is_empty()).collect();
    assert!(!done.is_empty(), "some root subproblem should have completed");

    // The resumed pass does strictly less work and reaches the same verdict.
    let second = search_orbits_parallel(&orbits, target, true, u64::MAX, 4, Some(&path));
    assert!(second.best < target, "same verdict after resume");
    assert!(second.exhaustive, "and the resumed run is exhaustive");
    assert!(
        second.nodes < fresh.nodes,
        "resume should skip completed subproblems: {} nodes against {} fresh",
        second.nodes,
        fresh.nodes
    );

    let _ = std::fs::remove_file(&path);
    let _ = std::fs::remove_dir(&dir);
}

/// Thread count does not change the verdict, and for an **exhaustive
/// negative** it does not change the node count either.
///
/// The qualifier is the content. When the target is reachable the search
/// stops as soon as any worker finds a family, so how much of the space
/// was explored first depends on how many workers were racing — a
/// thread-dependent node count there is correct behaviour, not a bug.
/// When the answer is no, every root subproblem is traversed in full
/// whoever runs it, and the total must be identical.
#[test]
fn the_verdict_does_not_depend_on_the_thread_count() {
    for (g, b, target) in [(6u32, 3u32, 11usize), (7, 3, 11)] {
        let orbits = singletons(g, b);
        let mut verdicts = Vec::new();
        for threads in [1usize, 2, 3, 4, 8] {
            let r = search_orbits_parallel(&orbits, target, true, u64::MAX, threads, None);
            assert!(r.best < target, "({g},{b},{target}) should be a negative");
            verdicts.push((r.exhaustive, r.nodes));
        }
        let first = verdicts[0];
        for (i, v) in verdicts.iter().enumerate() {
            assert_eq!(v.0, first.0, "exhaustiveness differs at ({g},{b}) index {i}");
            assert_eq!(
                v.1, first.1,
                "node count differs at ({g},{b}) index {i}: the root subproblems \
                 partition the space, so an exhausted total is thread-independent"
            );
        }
    }
}

/// When the target *is* reachable, the family a race returns may differ
/// with the thread count — but it is always a real one.
#[test]
fn a_found_family_always_verifies_whoever_found_it() {
    let orbits = singletons(6, 3);
    for threads in [1usize, 2, 4, 8] {
        let r = search_orbits_parallel(&orbits, 10, true, u64::MAX, threads, None);
        assert!(r.best >= 10, "iota(3) >= 10 at {threads} threads");
        verify(&r.best_family, 3, true)
            .unwrap_or_else(|e| panic!("{threads} threads produced a bad family: {e}"));
    }
}
