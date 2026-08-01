//! `tau` of the extremal families, and what a `tau`-indexed bound gives.
//!
//! §8 of the session brief called this "cheap and never done". Half of it
//! was already done: `extension.rs`'s
//! `the_covering_number_is_multiplicative_under_substitution` measures
//! `tau(triangle) = 2`, `tau(iota3) = 3` and checks
//! `tau(substitute(G,H)) = tau(G) tau(H)` on four pairs. This file is the
//! arithmetic that was supposed to follow from it, and it does not come
//! out the way the brief expected.
//!
//! ## The premise was wrong
//!
//! The brief predicted `tau(b) = b^(log_3 2) ~ b^0.63` for the AHS tower,
//! which needs a base with `tau = 2` at uniformity 3. The measured value
//! is `tau(iota3) = 3`, not 2. Since `tau` is multiplicative under
//! substitution and uniformity is too, the tower has
//!
//!     tau(substitute^k(base)) = tau(base)^k = b(base)^k = b
//!
//! so **`tau = b` exactly**, not `b^0.63`. That is the *maximum possible*:
//! an intersecting family is covered by any one of its own members, so
//! `tau <= b` always, and the 1972 families sit at the ceiling.
//!
//! ## What that does to the bound
//!
//! There is **no `b^tau` bound in general**: at `tau = 1` every member
//! shares a point, the family is a full star, and it is unbounded. The
//! bound has to be derived at `tau = b` specifically, and it uses
//! `tau = b` twice.
//!
//! Pick `A_1 in F`; every member meets it, so `b` branches for the first
//! point `x_1`. Since `tau = b > 1`, `{x_1}` is not a cover, so some
//! `A_2 in F` misses `x_1`, and every member through `x_1` meets `A_2`:
//! `b` branches again for a point `x_2 =/= x_1`. This continues while
//! `{x_1..x_k}` is not a cover, i.e. for `k < tau = b`, and after `b`
//! steps the member contains `b` distinct chosen points, so *is* the set
//! of them. Each leaf holds at most one member, giving `|F| <= b^b`.
//!
//! Both uses of `tau = b` are load-bearing: it keeps the branching going
//! for `b` levels, and `b = |B|` makes the leaves singletons. (Stated as
//! elementary arithmetic, not attributed: no search for priority was run,
//! and `docs/reading.md` B12 records the surrounding literature under
//! *base*, *nucleus*, *crosscut* and *minimal cover*.)
//!
//! Since `b! ~ (b/e)^b`, `b^b = b! e^b / sqrt(2 pi b)` — the **same `n!`
//! barrier** as every counting recursion, reached a third way. To get
//! `C^b` out of a `tau`-indexed bound the extremal families would need
//! `tau = O(log b)`; they have the largest `tau` an intersecting family
//! can have.
//!
//! So §8 closes the same way §2 and §3 did: the route is real, the
//! arithmetic is checkable, and it stops at `n!`.

use sunflower_formal::{extend, intersecting, structure};

/// Both families are copied verbatim from `rust/tests/extension.rs`, which
/// is where the `tau` measurements they are used for already live. Rule 7:
/// the ten triples of the `2-(6,3,2)` design are looked up, not recalled.
fn masks(sets: &[&[u32]]) -> Vec<u32> {
    sets.iter()
        .map(|s| s.iter().fold(0u32, |a, &x| a | 1 << x))
        .collect()
}

fn triangle() -> Vec<u32> {
    masks(&[&[0, 1], &[0, 2], &[1, 2]])
}

fn iota3() -> Vec<u32> {
    masks(&[
        &[0, 1, 2],
        &[0, 1, 3],
        &[0, 2, 4],
        &[1, 3, 4],
        &[2, 3, 4],
        &[1, 2, 5],
        &[0, 3, 5],
        &[2, 3, 5],
        &[0, 4, 5],
        &[1, 4, 5],
    ])
}

/// The measured `tau`, and the fact the brief got wrong: both bases sit
/// at `tau = b`, the ceiling, not below it.
#[test]
fn the_extremal_bases_have_tau_equal_to_their_uniformity() {
    let tri = structure::widen(&triangle());
    let i3 = structure::widen(&iota3());
    assert_eq!(
        extend::covering_number(&tri, 3, 1_000_000),
        Some(2),
        "tau(triangle) should be 2 = its uniformity"
    );
    assert_eq!(
        extend::covering_number(&i3, 4, 1_000_000),
        Some(3),
        "tau(iota3) should be 3 = its uniformity, NOT the 2 the \
         b^(log_3 2) prediction needs"
    );
}

/// And the tower keeps `tau = b`, because `tau` and uniformity multiply
/// together under substitution.
#[test]
fn the_tower_keeps_tau_equal_to_b() {
    let tri = structure::widen(&triangle());
    let i3 = structure::widen(&iota3());
    let cases: &[(&[u128], u32, &[u128], u32, usize, usize)] = &[
        // (G, ground(G), H, ground(H), uniformity of the product, tau)
        (&tri, 3, &tri, 3, 4, 4),
        (&i3, 6, &i3, 6, 9, 9),
    ];
    for &(g, vg, h, wg, uniformity, want_tau) in cases {
        let gg: Vec<u32> = g.iter().map(|&x| x as u32).collect();
        let hh: Vec<u32> = h.iter().map(|&x| x as u32).collect();
        let f = intersecting::substitute(&gg, vg, &hh, wg);
        assert_eq!(
            extend::covering_number(&f, want_tau + 1, 400_000_000),
            Some(want_tau),
            "tau of the substitution should be {want_tau}"
        );
        assert_eq!(
            want_tau, uniformity,
            "tau = b is the whole point: the tower sits at the ceiling"
        );
    }
}

/// The arithmetic. The greedy tree at `tau = b` gives `b^b`, which is
/// `b! e^b / sqrt(2 pi b)` — the `n!` barrier again, not `C^b`.
#[test]
fn the_tau_bound_lands_on_the_same_factorial_barrier() {
    // Stirling: b! = (b/e)^b sqrt(2 pi b), so exactly
    //     ln(b^b / b!) = b - (1/2) ln(2 pi b) + o(1).
    // Asserted against Stirling rather than against a loose "~ b", so the
    // test says what is true at b = 10 as well as at b = 80.
    for b in [10usize, 20, 40, 80] {
        let ln_bb = (b as f64) * (b as f64).ln();
        let ln_fact: f64 = (1..=b).map(|i| (i as f64).ln()).sum();
        let ratio_ln = ln_bb - ln_fact;
        let stirling =
            b as f64 - 0.5 * (2.0 * std::f64::consts::PI * b as f64).ln();
        assert!(
            (ratio_ln - stirling).abs() < 0.05,
            "b={b}: ln(b^b / b!) = {ratio_ln}, Stirling says {stirling}"
        );
        // The consequence: b^b / b! grows like e^b up to a sqrt factor, so
        // b^b is factorial-rate, not exponential.
        assert!(
            ratio_ln > 0.75 * b as f64,
            "b={b}: b^b / b! should still be growing like e^b"
        );
    }
    // And the rate test the whole session uses: g^(1/b)/b -> const means
    // factorial, -> 0 means exponential. b^b gives exactly 1.
    for b in [20usize, 100, 400] {
        let rate = ((b as f64) * (b as f64).ln() / b as f64 - (b as f64).ln()).exp();
        assert!(
            (rate - 1.0).abs() < 1e-9,
            "b={b}: the tau bound's rate should be exactly 1, got {rate}"
        );
    }
}

/// For contrast, and to keep the comparison honest: `b^b` is *better*
/// than Erdős–Rado's `b! 4^b = (4b/e)^b` by `(e/4)^b`, so the `tau` route
/// is not worthless — it is just on the wrong side of the barrier.
#[test]
fn the_tau_bound_beats_erdos_rado_but_not_the_barrier() {
    for b in [10usize, 20, 40] {
        let ln_tau_bound = (b as f64) * (b as f64).ln();
        let ln_fact: f64 = (1..=b).map(|i| (i as f64).ln()).sum();
        let ln_er = ln_fact + (b as f64) * 4f64.ln();
        assert!(
            ln_tau_bound < ln_er,
            "b={b}: b^b should beat Erdos-Rado's b! 4^b"
        );
        // but both have rate bounded away from zero, i.e. both are n!·C^n
        let rate_tau = (ln_tau_bound / b as f64 - (b as f64).ln()).exp();
        assert!(rate_tau > 0.9, "b={b}: tau rate {rate_tau} is not exponential");
    }
}
