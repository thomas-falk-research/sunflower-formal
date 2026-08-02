//! The ALWZ Theorem 4.2 chain, evaluated numerically.
//!
//! `coq/IntersectingSpread.v` proves the one-step consequence of
//! [ALWZ20] Theorem 4.2 and the comparison that kills it. This is the
//! arithmetic behind the comparison: the recursion
//!
//!     iota(b) <= max_{1<=t<=b} kappa(b)^t * g(b-t) - 1
//!     g(b)    <= 2b * iota(b)
//!
//! with `kappa(b) = ceil(C ln b) + 1`, evaluated with the maximum over
//! `t` taken honestly at every level — `t` is existential in "F is not
//! kappa-spread", so an upper bound has to survive every `t`.
//!
//! The finding is that the chain never beats Erdős–Rado's
//! `g(b) <= 2b g(b-1)`. The adversary takes `t = 1`, where the chain
//! reads `iota(b) < kappa * g(b-1) <= kappa * 2(b-1) * iota(b-1)` —
//! Erdős–Rado's step multiplied by `kappa`.
//!
//! Seeded with the values the development knows: `g(2) = 6` exactly,
//! `g(3) <= 26` (`PureLink.g_three_at_most_26`), `iota(3) = 10` exactly.

/// kappa(b) = ceil(C * ln b) + 1, the O(log w) of Theorem 4.2 with the
/// constant made explicit. Never below 2, since kappa <= 1 is vacuous.
fn kappa(b: usize, c: f64) -> u128 {
    if b <= 1 {
        return 2;
    }
    let v = (c * (b as f64).ln()).ceil() as i64 + 1;
    (v.max(2)) as u128
}

fn seeds() -> (Vec<u128>, Vec<u128>) {
    // index by b; g(0)=1 g(1)=2 g(2)=6 g(3)<=26, iota(1)=1 iota(2)=3 iota(3)=10
    (vec![1, 2, 6, 26], vec![1, 1, 3, 10])
}

/// Erdős–Rado: g(b) <= 2b g(b-1), from the same seeds.
fn erdos_rado(bmax: usize) -> Vec<u128> {
    let (mut g, _) = seeds();
    for b in g.len()..=bmax {
        g.push(g[b - 1].saturating_mul(2 * b as u128));
    }
    g
}

/// The section 2 chain, with `max` over the existential `t`.
/// Returns (g, iota, argmax_t).
fn chain(bmax: usize, c: f64) -> (Vec<u128>, Vec<u128>, Vec<usize>) {
    let (mut g, mut io) = seeds();
    let mut ts = vec![0usize; g.len()];
    for b in g.len()..=bmax {
        let k = kappa(b, c);
        let mut best: u128 = 0;
        let mut best_t = 1usize;
        for t in 1..=b {
            let pow = k.saturating_pow(t as u32);
            let v = pow.saturating_mul(g[b - t]);
            if v > best {
                best = v;
                best_t = t;
            }
        }
        io.push(best.saturating_sub(1));
        ts.push(best_t);
        // g via the star bound, never worse than Erdős–Rado
        let via_star = io[b].saturating_mul(2 * b as u128);
        let via_er = g[b - 1].saturating_mul(2 * b as u128);
        g.push(via_star.min(via_er));
        let gb = g[b];
        io[b] = io[b].min(gb);
    }
    (g, io, ts)
}

/// Erdős–Rado's `2^b b!` passes `u128::MAX` at about `b = 28`, and a
/// saturating multiply that has hit the ceiling reports a *smaller*
/// growth rate than the truth — which would look exactly like the chain
/// winning. Every exact test stays below the ceiling and asserts it.
const BMAX: usize = 24;

fn assert_no_saturation(g: &[u128], label: &str) {
    for (b, &v) in g.iter().enumerate() {
        assert!(
            v < u128::MAX,
            "{label}: g({b}) saturated u128; the comparison below would be \
             meaningless. Lower BMAX."
        );
    }
}

#[test]
fn chain_never_beats_erdos_rado() {
    for &c in &[1.0, 2.0, 4.0, 8.0, 16.0] {
        let (g, _, _) = chain(BMAX, c);
        let er = erdos_rado(BMAX);
        assert_no_saturation(&g, "chain");
        assert_no_saturation(&er, "erdos_rado");
        for b in 4..=BMAX {
            assert!(
                g[b] >= er[b],
                "C={c}: chain g({b}) = {} beat Erdos-Rado {} -- the \
                 IntersectingSpread.v finding would be wrong",
                g[b],
                er[b]
            );
        }
    }
}

/// The sharper form: the chain is not merely no better, it is *equal* to
/// Erdős–Rado, because the Erdős–Rado clamp inside `chain` is what is
/// binding at every level. Drop the clamp and the chain is strictly worse.
#[test]
fn chain_without_the_clamp_is_strictly_worse() {
    for &c in &[2.0, 4.0] {
        let (mut g, mut io) = seeds();
        for b in g.len()..=20 {
            let k = kappa(b, c);
            let mut best: u128 = 0;
            for t in 1..=b {
                best = best.max(k.saturating_pow(t as u32).saturating_mul(g[b - t]));
            }
            io.push(best.saturating_sub(1));
            g.push(io[b].saturating_mul(2 * b as u128));
        }
        let er = erdos_rado(20);
        assert!(
            g[20] > er[20],
            "C={c}: unclamped chain g(20) = {} should exceed Erdos-Rado {}",
            g[20],
            er[20]
        );
    }
}

/// The adversary settles on `t = 1`, which is the level at which the
/// re-intersection factor `2(b-t)` is largest. This is the mechanism, and
/// it is what `IntersectingSpread.chain_recursion_at_one` formalises.
#[test]
fn the_adversary_chooses_t_equal_one() {
    let (_, _, ts) = chain(BMAX, 2.0);
    for b in 12..=BMAX {
        assert_eq!(
            ts[b], 1,
            "at b={b} the worst t was {} rather than 1",
            ts[b]
        );
    }
}

/// The same recursion in log space, so the growth rate can be measured
/// far past where `u128` saturates. Returns `ln g(b)`.
fn chain_log(bmax: usize, c: f64) -> Vec<f64> {
    let (gs, ios) = seeds();
    let mut lg: Vec<f64> = gs.iter().map(|&v| (v as f64).ln()).collect();
    let mut lio: Vec<f64> = ios.iter().map(|&v| (v as f64).ln()).collect();
    for b in lg.len()..=bmax {
        let lk = (kappa(b, c) as f64).ln();
        let mut best = f64::NEG_INFINITY;
        for t in 1..=b {
            let v = (t as f64) * lk + lg[b - t];
            if v > best {
                best = v;
            }
        }
        lio.push(best);
        let l2b = (2.0 * b as f64).ln();
        lg.push((lio[b] + l2b).min(lg[b - 1] + l2b));
    }
    lg
}

/// The chain's growth rate stays factorial: `g(b)^(1/b) / b` tends to a
/// positive constant (`2/e = 0.736`, Erdős–Rado's), where the ALWZ bound
/// `(C log b)^b` sends it to zero. That difference is the whole question,
/// and the chain lands on the wrong side of it.
#[test]
fn chain_growth_is_factorial_not_exponential() {
    let lg = chain_log(200, 2.0);
    let rate = |b: usize| (lg[b] / b as f64 - (b as f64).ln()).exp();
    for &b in &[50, 100, 200] {
        assert!(
            rate(b) > 0.6,
            "chain rate at b={b} was {}; it should stay near Erdos-Rado's \
             2/e = 0.736, not collapse",
            rate(b)
        );
    }
    // Erdős–Rado's own rate, for the comparison the finding rests on.
    assert!(
        (rate(200) - 2.0 / std::f64::consts::E).abs() < 0.05,
        "chain rate {} should sit on Erdos-Rado's 2/e = {}",
        rate(200),
        2.0 / std::f64::consts::E
    );
    // The ALWZ target, for contrast, does go to zero.
    let alwz = |b: usize| ((kappa(b, 2.0) as f64).ln() - (b as f64).ln()).exp();
    assert!(
        alwz(200) < 0.1,
        "the ALWZ target rate at b=200 was {}, expected well below the chain",
        alwz(200)
    );
    assert!(
        alwz(200) < rate(200),
        "ALWZ target {} should beat the chain {}",
        alwz(200),
        rate(200)
    );
}

/// The seeds are the values the Coq layer proves, not guesses. If
/// `PureLink.g_three_at_most_26` ever moves, this is the reminder.
#[test]
fn seeds_match_the_coq_layer() {
    let (g, io) = seeds();
    assert_eq!(g[2], 6, "g(2) = 6 exactly (PureLink.g_two_at_most_six)");
    assert_eq!(g[3], 26, "g(3) <= 26 (PureLink.g_three_at_most_26)");
    assert_eq!(io[2], 3, "iota(2) = 3 exactly");
    assert_eq!(io[3], 10, "iota(3) = 10 exactly (wide::iota_three_is_exactly_ten)");
}
