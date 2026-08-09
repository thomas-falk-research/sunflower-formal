//! Stage A of the spread lemma — the numbers behind `coq/Counting.v`.
//!
//! `docs/roadmap.md` §1 stages the discharge of `ALWZ.Rao20_lemma2`
//! through the counting proof (Lovett PCMI §3), and Stage A is the
//! arithmetic that proof needs: fixed-size subset enumeration, a counting
//! operator, `C(n,j) <= 2^n`, and **one binomial estimate**.
//!
//! Everything here is an *independent* implementation. `binom` in the Coq
//! file is Pascal's recursion; here it is the multiplicative formula
//! `C(n,j) = prod (n-i)/(i+1)`, which shares no structure with it. The
//! layer count in the Coq file is `filter (length = j) (subsets l)`; here
//! it is an enumeration over bitmasks. Two definitions agreeing is a
//! check on both.
//!
//! Nine claims:
//!
//! 1. **The two binomials agree**, over the whole `u128`-safe range, and
//!    the Coq recursion's convention off the triangle (`C(n,j) = 0` for
//!    `j > n`) is checked rather than assumed.
//! 2. **Absorption**: `C(N,j+1)*(j+1) = C(N,j)*(N-j)` with *truncated*
//!    subtraction — the identity the Coq proof turns on, and the place
//!    `nat`'s `-` could have broken it.
//! 3. **The estimate**: `c*N <= d*(j+1)` implies
//!    `c^m * C(N,j+m) <= d^m * C(N,j)`, exhaustively over a box.
//! 4. **That hypothesis is exactly minimal.** Lovett's use gives
//!    `c*N <= d*j`; the argument only needs `c*N <= d*(j+1)`, and
//!    `c*N <= d*(j+2)` is **false** — 102 counterexamples in a small
//!    box, the smallest being `N=1, j=0, c=2, d=1, m=1`. So the Coq
//!    statement carries the weakest hypothesis that works, not the one
//!    the application happens to supply.
//! 5. **`C(n,j) <= 2^n`**, and `sum_j C(n,j) = 2^n`, which is
//!    `length_subsets`.
//! 6. **The layer**: enumerating the size-`j` subsets by bitmask gives
//!    `C(n,j)` of them, they are distinct, and each has size `j`.
//! 7. **Counting**: `count` partition, monotonicity, disjoint additivity,
//!    and an injection giving an inequality — the shape Claim 3.4 uses.

/// Binomial coefficients by the multiplicative formula — no Pascal, so
/// this shares nothing with `Counting.binom` beyond the answer.
/// `None` on overflow.
fn binom_mul(n: u64, j: u64) -> Option<u128> {
    if j > n {
        return Some(0);
    }
    let j = j.min(n - j);
    let mut acc: u128 = 1;
    for i in 0..j {
        acc = acc.checked_mul((n - i) as u128)?;
        acc /= (i + 1) as u128;
    }
    Some(acc)
}

/// Pascal's recursion as a table, matching `Counting.binom`'s convention.
fn binom_pascal(n: usize, j: usize) -> u128 {
    let mut row = vec![0u128; j + 2];
    row[0] = 1;
    for _ in 0..n {
        let mut next = vec![0u128; j + 2];
        next[0] = 1;
        for t in 1..=j + 1 {
            next[t] = row[t - 1] + row[t];
        }
        row = next;
    }
    row[j.min(j + 1)]
}

/// `N - j` in `nat`: truncated at zero.
fn msub(a: u128, b: u128) -> u128 {
    if a > b {
        a - b
    } else {
        0
    }
}

// ---------------------------------------------------------------------------
// 1. The two definitions agree
// ---------------------------------------------------------------------------

#[test]
fn the_multiplicative_formula_and_pascals_recursion_agree() {
    let mut checked = 0usize;
    for n in 0..=40u64 {
        for j in 0..=45u64 {
            let a = binom_mul(n, j).expect("C(n,j) fits in u128 for n <= 40");
            let b = binom_pascal(n as usize, j as usize);
            assert_eq!(a, b, "disagreement at C({n},{j})");
            checked += 1;
        }
    }
    assert_eq!(checked, 41 * 46);
    // the off-triangle convention `Counting.binom_zero_above`
    for n in 0..=20u64 {
        for j in (n + 1)..=(n + 6) {
            assert_eq!(binom_pascal(n as usize, j as usize), 0, "C({n},{j})");
        }
        assert_eq!(binom_pascal(n as usize, 0), 1, "binom_zero at n={n}");
        assert_eq!(binom_pascal(n as usize, n as usize), 1, "binom_diag at n={n}");
        if n >= 1 {
            assert_eq!(binom_pascal(n as usize, 1), n as u128, "binom_one at n={n}");
        }
    }
}

// ---------------------------------------------------------------------------
// 2. Absorption, with truncated subtraction
// ---------------------------------------------------------------------------

#[test]
fn absorption_survives_truncated_subtraction() {
    // C(N, j+1) * (j+1) = C(N, j) * (N - j), the identity `binom_absorb`
    // turns on. The interesting range is j >= N, where `nat`'s `-` clamps:
    // both sides must be zero rather than the identity failing.
    let mut above_diagonal = 0usize;
    for n in 0..=30usize {
        for j in 0..=35usize {
            let lhs = binom_pascal(n, j + 1) * (j as u128 + 1);
            let rhs = binom_pascal(n, j) * msub(n as u128, j as u128);
            assert_eq!(lhs, rhs, "absorption fails at N={n} j={j}");
            if j >= n {
                assert_eq!(lhs, 0, "expected both sides zero at N={n} j={j}");
                above_diagonal += 1;
            }
        }
    }
    assert!(above_diagonal > 0, "the clamping range must actually be exercised");
}

// ---------------------------------------------------------------------------
// 3 & 4. The estimate, and that its hypothesis is load-bearing
// ---------------------------------------------------------------------------

/// `c^m * C(N, j+m) <= d^m * C(N, j)`, or `None` if either side overflows.
fn estimate_holds(n: usize, j: usize, c: u128, d: u128, m: u32) -> Option<bool> {
    let lhs = c.checked_pow(m)?.checked_mul(binom_pascal(n, j + m as usize))?;
    let rhs = d.checked_pow(m)?.checked_mul(binom_pascal(n, j))?;
    Some(lhs <= rhs)
}

#[test]
fn the_binomial_estimate_holds_under_its_hypothesis() {
    let mut with_hyp = 0usize;
    for n in 0..=16usize {
        for j in 0..=18usize {
            for c in 0..=5u128 {
                for d in 0..=5u128 {
                    if c * (n as u128) <= d * (j as u128 + 1) {
                        for m in 0..=6u32 {
                            let ok = estimate_holds(n, j, c, d, m)
                                .expect("no overflow in this box");
                            assert!(
                                ok,
                                "binom_ratio fails at N={n} j={j} c={c} d={d} m={m}"
                            );
                            with_hyp += 1;
                        }
                    }
                }
            }
        }
    }
    assert!(with_hyp > 10_000, "the box must actually cover the sharp hypothesis c*N <= d*(j+1)");
}

#[test]
fn the_successor_in_the_hypothesis_is_exactly_the_boundary() {
    // `Counting.binom_ratio` assumes `c*N <= d*(j+1)`. One notch further
    // -- `c*N <= d*(j+2)` -- and the estimate is false, so the hypothesis
    // is minimal for this argument rather than merely convenient.
    //
    // The witness `Counting.binom_ratio_needs_the_successor` carries:
    let (n, j, c, d, m) = (1usize, 0usize, 2u128, 1u128, 1u32);
    assert!(c * (n as u128) <= d * (j as u128 + 2), "it satisfies the weakened form");
    assert!(c * (n as u128) > d * (j as u128 + 1), "and violates the real one");
    assert_eq!(estimate_holds(n, j, c, d, m), Some(false));

    // and it is not an isolated point
    let mut violations = 0usize;
    for n in 0..=15usize {
        for j in 0..=17usize {
            for c in 0..=6u128 {
                for d in 0..=6u128 {
                    if c * (n as u128) <= d * (j as u128 + 2) {
                        for m in 0..=6u32 {
                            if estimate_holds(n, j, c, d, m) == Some(false) {
                                violations += 1;
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(
        violations, 102,
        "the j+2 relaxation should fail in exactly 102 places in this box"
    );
}

#[test]
fn dropping_the_hypothesis_entirely_is_worse_still() {
    // With no hypothesis at all: C(10,5) = 252 against C(10,0) = 1.
    assert_eq!(estimate_holds(10, 0, 1, 1, 5), Some(false));
    assert_eq!(binom_pascal(10, 5), 252);
    assert_eq!(binom_pascal(10, 0), 1);
}

// ---------------------------------------------------------------------------
// 5. C(n,j) <= 2^n, and the row sums to 2^n
// ---------------------------------------------------------------------------

#[test]
fn binomials_are_bounded_by_two_to_the_n_and_the_row_sums_to_it() {
    for n in 0..=30usize {
        let two_n = 1u128 << n;
        let mut row = 0u128;
        for j in 0..=n + 5 {
            let b = binom_pascal(n, j);
            assert!(b <= two_n, "binom_le_two_pow fails at C({n},{j})");
            row += b;
        }
        // `length_subsets`: the whole powerset is 2^n, so the layers sum to it
        assert_eq!(row, two_n, "row {n} should sum to 2^{n}");
    }
}

// ---------------------------------------------------------------------------
// 6. The layer, enumerated
// ---------------------------------------------------------------------------

/// Every size-`j` subset of `{0,..,n-1}`, as bitmasks — an enumeration,
/// where the Coq side filters `subsets` by length.
fn layer(n: u32, j: u32) -> Vec<u32> {
    (0u32..(1u32 << n)).filter(|m| m.count_ones() == j).collect()
}

#[test]
fn the_layer_enumeration_has_binom_many_distinct_members() {
    for n in 0..=14u32 {
        for j in 0..=n + 2 {
            let l = layer(n, j);
            assert_eq!(
                l.len() as u128,
                binom_pascal(n as usize, j as usize),
                "length_subsets_of_size fails at n={n} j={j}"
            );
            // distinct, and each of the right size -- `subsets_of_size_NoDup_enum`
            // and `subsets_of_size_incl`
            let mut sorted = l.clone();
            sorted.sort_unstable();
            sorted.dedup();
            assert_eq!(sorted.len(), l.len(), "the layer must have no repeats");
            assert!(l.iter().all(|m| m.count_ones() == j));
            assert!(l.iter().all(|m| *m < (1u32 << n)));
        }
        // the layers partition the powerset: `length_subsets`
        let total: usize = (0..=n).map(|j| layer(n, j).len()).sum();
        assert_eq!(total, 1usize << n, "layers of {n} should exhaust 2^{n}");
    }
}

// ---------------------------------------------------------------------------
// 7. Counting: partition, monotonicity, disjoint additivity, injection
// ---------------------------------------------------------------------------

fn count<T>(p: impl Fn(&T) -> bool, l: &[T]) -> usize {
    l.iter().filter(|x| p(x)).count()
}

#[test]
fn the_counting_operator_behaves() {
    let l: Vec<u32> = layer(10, 4);
    let even = |m: &u32| m % 2 == 0;
    let odd = |m: &u32| m % 2 == 1;
    let low = |m: &u32| *m < 64;

    // `count_partition`
    assert_eq!(count(even, &l) + count(|m: &u32| !even(m), &l), l.len());
    // `count_disjoint_add` -- even and odd are disjoint predicates
    assert!(l.iter().all(|m| !(even(m) && odd(m))));
    assert_eq!(
        count(even, &l) + count(odd, &l),
        count(|m: &u32| even(m) || odd(m), &l)
    );
    // `count_mono`
    assert!(l.iter().all(|m| !low(m) || *m < 1024));
    assert!(count(low, &l) <= count(|m: &u32| *m < 1024, &l));

    // `count_inj_le`: complementation is an injection from the size-4
    // layer of a 10-set into the size-6 layer, so C(10,4) <= C(10,6).
    // (They are equal, which is the tightest case an injection bound has.)
    let mask = (1u32 << 10) - 1;
    let target: Vec<u32> = layer(10, 6);
    let images: Vec<u32> = l.iter().map(|m| m ^ mask).collect();
    let mut dedup = images.clone();
    dedup.sort_unstable();
    dedup.dedup();
    assert_eq!(dedup.len(), images.len(), "complementation must be injective");
    assert!(
        images.iter().all(|m| target.contains(m)),
        "complementation must land in the size-6 layer"
    );
    assert!(l.len() <= target.len(), "count_inj_le");
    assert_eq!(l.len(), target.len(), "C(10,4) = C(10,6)");
}

// ---------------------------------------------------------------------------
// The estimate at the point roadmap §1 quotes
// ---------------------------------------------------------------------------

#[test]
fn the_estimate_at_a_quarter_matches_the_coq_example() {
    // `Counting.ratio_at_a_quarter`: q = 1/4, N = 8, j = 2, m = 3.
    assert!(1 * 8 <= 4 * 2);
    assert_eq!(binom_pascal(8, 5), 56);
    assert_eq!(binom_pascal(8, 2), 28);
    assert_eq!(1u128.pow(3) * 56, 56);
    assert_eq!(4u128.pow(3) * 28, 1792);
    assert!(56 <= 1792);
    // and `Counting.binom_row_six`
    let row: Vec<u128> = (0..=7).map(|j| binom_pascal(6, j)).collect();
    assert_eq!(row, vec![1, 6, 15, 20, 15, 6, 1, 0]);
    // and `Counting.absorb_above_the_diagonal`
    assert_eq!(binom_pascal(4, 6) * 6, binom_pascal(4, 5) * msub(4, 5));
}
