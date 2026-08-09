//! The reduction at an arbitrary profile, and the greedy barrier —
//! the numbers behind `coq/Profile.v`.
//!
//! `SpreadReduction.spread_reduction` never uses that `r^j` is a power.
//! Replacing it by an arbitrary `B : nat -> nat` gives
//! `f(m,k) <= B(m) + 1` whenever every `m`-uniform family satisfying
//! `deg T F <= B(m - |T|)` and exceeding `B(m)` has `k` pairwise disjoint
//! members. The *greedy cover step* — maximal matching of at most `k-1`
//! members, so a cover by `(k-1)m` points, so `|F| <= (k-1)m·B(m-1)` —
//! discharges that hypothesis exactly when
//!
//! ```text
//!     (k-1) * m * B(m-1)  <=  B(m)      for every m <= n
//! ```
//!
//! and unrolling that from `B(0) = 1` gives `B(m) >= (k-1)^m · m!`, which
//! is Erdős–Rado 1960. Six claims are checked here, sharing no code with
//! the Coq side:
//!
//! 1. **The barrier.** Every greedy-closed profile dominates
//!    `(k-1)^m·m!` — checked over a systematic family of profiles, at
//!    several `k`, in exact `u128`. (`greedy_forces_erdos_rado`)
//! 2. **The bound is attained.** Erdős–Rado's own profile is greedy-closed
//!    with *equality* at every level, so it is the least one.
//!    (`er_profile_greedy_closed`)
//! 3. **The power profile.** `r = (k-1)n` is greedy-closed for `r^j` at
//!    every `k` and every `m <= n`, which is
//!    `cover_spread_disjoint_general` — `SpreadThreshold`'s `k = 3` cover
//!    bound at every `k`.
//! 4. **Bernoulli in `nat`.** `n^k(n+k) <= n(n+1)^k`, and its consequence
//!    `2·n^n <= (n+1)^n`, which is what turns §28.4's range check into a
//!    theorem. (`pow_bernoulli`, `two_pow_le_succ_pow`)
//! 5. **`2^n·n! <= (n+1)^n` at every `n`** — the same comparison
//!    `rust/tests/hilton_milner.rs` pins to `n = 200`, re-checked here
//!    from the Bernoulli side so the two agree.
//! 6. **The greedy step is lossy, and measurably so.** The *true* least
//!    profile at `k = 3` has `B(2) = 6`, against the greedy step's `8`:
//!    two disjoint triangles are 2-uniform, have max degree `2 = B(1)`,
//!    simple, and no three pairwise disjoint edges. Exhaustive. So the
//!    barrier is a statement about the method, not about the truth.

/// `(k-1)^m * m!` — Erdős–Rado's profile, `ErdosRado_Greedy.er_upper_bound`
/// minus its `+1`.
fn er_profile(k: u128, m: u32) -> u128 {
    let mut acc: u128 = 1;
    for j in 1..=m {
        acc = acc * (k - 1) * (j as u128);
    }
    acc
}

/// `GreedyClosed n k B` : `(k-1)·m·B(m-1) <= B(m)` for `1 <= m <= n`.
fn greedy_closed(k: u128, b: &[u128]) -> bool {
    (1..b.len()).all(|m| (k - 1) * (m as u128) * b[m - 1] <= b[m])
}

// ---------------------------------------------------------------------------
// 1 & 2. The barrier, and that it is attained
// ---------------------------------------------------------------------------

#[test]
fn every_greedy_closed_profile_dominates_erdos_rado() {
    // A systematic family of profiles: start from Erdős–Rado's and inflate
    // each level by a factor, then repair upward so the result is still
    // greedy-closed. Whatever comes out must dominate `(k-1)^m·m!`.
    let mut checked = 0usize;
    for k in 2u128..=5 {
        for infl in [1u128, 2, 3, 7] {
            for bump_at in 0u32..=6 {
                let n = 12u32;
                let mut b = vec![0u128; (n + 1) as usize];
                b[0] = 1;
                for m in 1..=n {
                    let need = (k - 1) * (m as u128) * b[(m - 1) as usize];
                    b[m as usize] = if m == bump_at { need * infl } else { need };
                }
                assert!(greedy_closed(k, &b), "construction should be greedy-closed");
                for m in 0..=n {
                    assert!(
                        er_profile(k, m) <= b[m as usize],
                        "greedy_forces_erdos_rado violated: k={k} m={m} \
                         B(m)={} < (k-1)^m m! = {}",
                        b[m as usize],
                        er_profile(k, m)
                    );
                    checked += 1;
                }
            }
        }
    }
    assert_eq!(checked, 4 * 4 * 7 * 13);
}

#[test]
fn erdos_rados_own_profile_is_greedy_closed_with_equality() {
    for k in 2u128..=6 {
        let n = 15u32;
        let b: Vec<u128> = (0..=n).map(|m| er_profile(k, m)).collect();
        assert!(greedy_closed(k, &b));
        // equality at every level -- this is what makes it *least*
        for m in 1..=n {
            assert_eq!(
                (k - 1) * (m as u128) * b[(m - 1) as usize],
                b[m as usize],
                "k={k} m={m}"
            );
        }
    }
}

// ---------------------------------------------------------------------------
// 3. The power profile: cover_spread_disjoint, at every k
// ---------------------------------------------------------------------------

#[test]
fn the_power_profile_is_greedy_closed_at_r_equals_k_minus_one_times_n() {
    for k in 2u128..=6 {
        for n in 1u32..=8 {
            let r = (k - 1) * (n as u128);
            let b: Vec<u128> = (0..=n).map(|j| r.pow(j)).collect();
            assert!(
                greedy_closed(k, &b),
                "cover_spread_disjoint_general fails at k={k} n={n}"
            );
            // and it is sharp for this argument: r = (k-1)n - 1 breaks it
            // at the top level, whenever that is still positive
            if r >= 2 {
                let r2 = r - 1;
                let b2: Vec<u128> = (0..=n).map(|j| r2.pow(j)).collect();
                let ok = greedy_closed(k, &b2);
                assert_eq!(
                    ok,
                    (k - 1) * (n as u128) <= r2,
                    "sharpness at k={k} n={n}: greedy closure should hold \
                     exactly when (k-1)n <= r"
                );
            }
        }
    }
}

// ---------------------------------------------------------------------------
// 4 & 5. Bernoulli, and the exact comparison with 1960
// ---------------------------------------------------------------------------

#[test]
fn bernoulli_in_nat() {
    // n^k * (n+k) <= n * (n+1)^k, the induction behind `pow_bernoulli`
    for n in 0u128..=12 {
        for k in 0u32..=12 {
            let lhs = n.pow(k) * (n + k as u128);
            let rhs = n * (n + 1).pow(k);
            assert!(lhs <= rhs, "pow_bernoulli fails at n={n} k={k}");
        }
    }
    // and the instance k = n, which is `two_pow_le_succ_pow`
    for n in 1u128..=25 {
        assert!(
            2 * n.pow(n as u32) <= (n + 1).pow(n as u32),
            "two_pow_le_succ_pow fails at n={n}"
        );
    }
}

/// `2^n · n!`, or `None` once it leaves `u128`.
fn er_value(n: u32) -> Option<u128> {
    let mut er: u128 = 1;
    for j in 1..=n {
        er = er.checked_mul(2)?.checked_mul(j as u128)?;
    }
    Some(er)
}

#[test]
fn erdos_rado_is_below_the_n_to_the_n_ceiling() {
    // 2^n * n! <= (n+1)^n at every n. `rust/tests/hilton_milner.rs` pins the
    // same comparison to n = 200 with its own big-integer arithmetic; this
    // is the exact `u128` range, reached from the Bernoulli side.
    //
    // Every power here is `checked_pow`: the first draft of this test used
    // `pow`, which wraps silently in release mode, and reported a failure at
    // n = 28 for a theorem that is true at every n. `(n+1)^n` leaves `u128`
    // at n = 27, so the range stops at 26 and says so.
    let mut last = 0u32;
    for n in 0u32..=26 {
        let er = er_value(n).expect("2^n n! fits in u128 below n = 27");
        let ceiling = (n as u128 + 1)
            .checked_pow(n)
            .expect("(n+1)^n fits in u128 below n = 27");
        assert!(
            er <= ceiling,
            "erdos_rado_below_the_n_to_the_n_ceiling fails at n={n}: \
             2^n n! = {er} > (n+1)^n = {ceiling}"
        );
        // tight at n = 0 and n = 1, strict from n = 2 on
        if n >= 2 {
            assert!(er < ceiling, "expected strict at n={n}");
        } else {
            assert_eq!(er, ceiling, "expected equality at n={n}");
        }
        last = n;
    }
    assert_eq!(last, 26, "the u128 range is 0..=26 and is fully covered");
    // and the first n at which `(n+1)^n` leaves u128, recorded so the bound
    // above is a fact about the arithmetic rather than a guess
    assert!((27u128 + 1).checked_pow(27).is_none());
}

// ---------------------------------------------------------------------------
// 6. The greedy step is lossy: the true B(2) is 6, not 8
// ---------------------------------------------------------------------------

/// Exhaustive: the largest simple graph on `ground` vertices with max
/// degree at most `maxdeg` and no three pairwise disjoint edges.
///
/// Backtracking over the edge list with the two prunes that matter: the
/// degree cap, and "adding this edge completes a 3-matching".
fn max_edges_no_three_matching(ground: usize, maxdeg: usize) -> (usize, Vec<(usize, usize)>) {
    let edges: Vec<(usize, usize)> = (0..ground)
        .flat_map(|a| ((a + 1)..ground).map(move |b| (a, b)))
        .collect();
    let mut deg = vec![0usize; ground];
    let mut chosen: Vec<(usize, usize)> = Vec::new();
    let mut best = (0usize, Vec::new());

    fn disjoint(e: (usize, usize), f: (usize, usize)) -> bool {
        e.0 != f.0 && e.0 != f.1 && e.1 != f.0 && e.1 != f.1
    }

    fn rec(
        i: usize,
        edges: &[(usize, usize)],
        deg: &mut Vec<usize>,
        maxdeg: usize,
        chosen: &mut Vec<(usize, usize)>,
        best: &mut (usize, Vec<(usize, usize)>),
    ) {
        if chosen.len() > best.0 {
            *best = (chosen.len(), chosen.clone());
        }
        if i == edges.len() || chosen.len() + (edges.len() - i) <= best.0 {
            return;
        }
        let e = edges[i];
        if deg[e.0] < maxdeg && deg[e.1] < maxdeg {
            // does e complete a triple of pairwise disjoint edges?
            let free: Vec<(usize, usize)> =
                chosen.iter().copied().filter(|&f| disjoint(e, f)).collect();
            let completes = free
                .iter()
                .enumerate()
                .any(|(a, &fa)| free[a + 1..].iter().any(|&fb| disjoint(fa, fb)));
            if !completes {
                deg[e.0] += 1;
                deg[e.1] += 1;
                chosen.push(e);
                rec(i + 1, edges, deg, maxdeg, chosen, best);
                chosen.pop();
                deg[e.0] -= 1;
                deg[e.1] -= 1;
            }
        }
        rec(i + 1, edges, deg, maxdeg, chosen, best);
    }

    rec(0, &edges, &mut deg, maxdeg, &mut chosen, &mut best);
    best
}

#[test]
fn the_least_profile_at_uniformity_two_is_six_not_eight() {
    // At k = 3 the profile condition at m = 2 reads
    //   deg{x}   <= B(1) = 2      (max degree two)
    //   deg{x,y} <= B(0) = 1      (simple)
    // and the family must have no three pairwise disjoint members. The
    // greedy step gives (k-1)·m·B(1) = 2·2·2 = 8, which is Erdős–Rado's
    // value; the truth is 6.
    for ground in 6..=9 {
        let (best, witness) = max_edges_no_three_matching(ground, 2);
        assert_eq!(
            best, 6,
            "least profile at m=2 should be 6 on {ground} points, got {best} \
             ({witness:?})"
        );
    }
    // The witness is two disjoint triangles, at every ground set searched.
    let (_, w) = max_edges_no_three_matching(6, 2);
    let mut comps = vec![0usize; 6];
    for (i, &(a, b)) in w.iter().enumerate() {
        let _ = i;
        comps[a] += 1;
        comps[b] += 1;
    }
    assert!(comps.iter().all(|&d| d == 2), "every vertex has degree 2: {w:?}");

    // Erdős–Rado's profile at the same place is 8, so the greedy step
    // over-counts by 2 already at uniformity two. `greedy_forces_erdos_rado`
    // says no refinement of *that step* can close the gap; something else
    // has to.
    assert_eq!(er_profile(3, 2), 8);
    assert!(6 < er_profile(3, 2));
}

// ---------------------------------------------------------------------------
// The costing table: every linear route loses to 1960, exactly
// ---------------------------------------------------------------------------

#[test]
fn every_linear_route_ceiling_is_at_least_erdos_rado() {
    // `tools/ceiling.py` prints this; here it is checked independently.
    // A route with r*(n,3) <= c·n yields f(n,3) <= (c n)^n + 1, and every
    // linear route in the development has c >= 1.
    let mut covered = 0usize;
    for n in 1u32..=23 {
        let er = er_value(n).expect("fits");
        // c = 1 is the smallest linear ceiling any method here reaches
        // (the matching-split best case, and star extremality's pin).
        let c1 = (n as u128 + 1).checked_pow(n).expect("fits");
        assert!(er <= c1, "n={n}: 2^n n! = {er} > (n+1)^n = {c1}");
        // and 2n, 2n+1, ceil(1.74n) are all worse still
        for r in [2 * n as u128, 2 * n as u128 + 1, (174 * n as u128) / 100 + 1] {
            let v = r.checked_pow(n).expect("(2n+1)^n fits in u128 below n = 24");
            assert!(er <= v, "n={n} r={r}");
        }
        covered += 1;
    }
    assert_eq!(covered, 23, "n = 1..=23 is the exact u128 range for (2n+1)^n");
    assert!((2u128 * 24 + 1).checked_pow(24).is_none());
}
