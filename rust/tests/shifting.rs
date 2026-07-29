//! Compression against sunflower-freeness: the exhaustive record.
//!
//! Shifting is the standard instrument of extremal set theory. This
//! suite points it at sunflower-freeness and measures what happens. The
//! summary, every line of it exhaustive over the stated range:
//!
//! 1. **The controls pass.** Shifting preserves size, uniformity,
//!    intersecting-ness and the matching number — so the implementation
//!    is the textbook operation and not something else.
//! 2. **It does not preserve 3-sunflower-freeness, and it fails at the
//!    first opportunity.** The smallest counterexample has **three**
//!    members, which is the least a 3-sunflower can have. `{01, 02, 13}`
//!    is sunflower-free; its `(0,1)`-shift is the star `{01, 02, 03}`.
//! 3. **The maximum is not attained by a compressed family either.** A
//!    left-compressed 3-sunflower-free `m`-uniform family has at most
//!    `m + 1` members — on *any* ground set — against `N(2,6) = 6`,
//!    `N(3,6) = 10` and `g(b) ≥ 2·ι(b)` exponential. Compression does
//!    not cost a constant here. It collapses the problem from
//!    exponential to linear.
//! 4. **The mechanism, exactly.** By
//!    `LinkCharacterisation.sunflower_iff_link_matching`, sunflower-free
//!    means *every* link has matching number `≤ 2`. Shifting preserves
//!    that at the **empty** link — the standard fact — and breaks it at
//!    a **singleton** core, because shifting towards `i` is precisely
//!    the operation that inflates `deg(i)`, and
//!    `IotaGround.link_degree_ground_bound` is precisely the theorem
//!    that caps it. Intersecting-ness is the single empty-link
//!    condition `ν ≤ 1`, which is why the tool works for Erdős–Ko–Rado
//!    and cannot work here.
//! 5. **Compression drives diversity to its minimum**, and the extremal
//!    `ι` families are where diversity is largest. The two are pointed
//!    in opposite directions, which is the sharpest available statement
//!    of why the field's standard tool is unavailable for this problem.

use std::collections::HashSet;

use sunflower_formal::ground::max_sunflower_free;
use sunflower_formal::intersecting::{iota, iota_decide};
use sunflower_formal::shift::*;
use sunflower_formal::spread::matching_number;

const BUDGET: u64 = 20_000_000_000_000;

/// Every `size`-subset of `[n]`, lexicographic. `visit` returns false to
/// stop early.
fn for_each_combination(n: usize, size: usize, visit: &mut dyn FnMut(&[usize]) -> bool) {
    if size > n {
        return;
    }
    let mut idx: Vec<usize> = (0..size).collect();
    loop {
        if !visit(&idx) {
            return;
        }
        let mut p = size;
        loop {
            if p == 0 {
                return;
            }
            p -= 1;
            if idx[p] < n - (size - p) {
                idx[p] += 1;
                for q in (p + 1)..size {
                    idx[q] = idx[q - 1] + 1;
                }
                break;
            }
        }
    }
}

/// Every family of at most `max_size` members drawn from the `m`-subsets
/// of `[ground]`, including the empty one.
fn for_each_family(ground: u32, m: u32, max_size: usize, visit: &mut dyn FnMut(&[u32])) {
    let sets = subsets_of_size(ground, m);
    for size in 0..=max_size.min(sets.len()) {
        for_each_combination(sets.len(), size, &mut |idx| {
            let fam: Vec<u32> = idx.iter().map(|&i| sets[i]).collect();
            visit(&fam);
            true
        });
    }
}

// ---------------------------------------------------------------------
// 1. The controls: this is the textbook operation.
// ---------------------------------------------------------------------

/// Shifting preserves size, uniformity, intersecting-ness and the
/// matching number. All four are what the literature uses it for, and a
/// wrong implementation would fail one of them.
#[test]
fn shifting_does_what_the_literature_says() {
    for (ground, m, cap) in [(4u32, 2u32, 6usize), (5, 2, 5), (6, 2, 4), (5, 3, 5), (6, 3, 4)] {
        for_each_family(ground, m, cap, &mut |f| {
            for j in 0..ground {
                for i in 0..j {
                    let g = shift_family(f, i, j);
                    assert_eq!(g.len(), f.len(), "size changed by ({i},{j}) on {f:?}");
                    let distinct: HashSet<u32> = g.iter().copied().collect();
                    assert_eq!(distinct.len(), g.len(), "shift collided on {f:?}");
                    assert!(
                        g.iter().all(|&a| a.count_ones() == m),
                        "uniformity lost by ({i},{j}) on {f:?}"
                    );
                    if is_intersecting(f) {
                        assert!(
                            is_intersecting(&g),
                            "intersecting lost by ({i},{j}) on {f:?}"
                        );
                    }
                    assert!(
                        matching_number(&g) <= matching_number(f),
                        "matching number rose under ({i},{j}) on {f:?}"
                    );
                }
            }
        });
    }
}

/// The three descriptions of "left-compressed" agree: stable under every
/// `(i,j)`-shift, stable under the adjacent ones alone, and a down-set
/// in the dominance order. The middle one is what the search in
/// `max_left_compressed` relies on, and it is the one that is not
/// obvious.
#[test]
fn the_three_descriptions_of_compressed_agree() {
    for (ground, m, cap) in [(4u32, 2u32, 6usize), (5, 2, 5), (5, 3, 5), (6, 3, 4)] {
        for_each_family(ground, m, cap, &mut |f| {
            let a = is_left_compressed(f, ground);
            let b = is_left_compressed_adjacent(f, ground);
            let c = is_dominance_downset(f, ground, m);
            assert_eq!(a, b, "adjacent shifts did not generate on {f:?}");
            assert_eq!(a, c, "compressed is not a dominance down-set on {f:?}");
        });
    }
}

/// The compression terminates, the potential is what drives it, and the
/// fixed point has the size it started with.
#[test]
fn shift_closure_is_compressed_and_size_preserving() {
    for (ground, m, cap) in [(5u32, 2u32, 5usize), (6, 2, 4), (6, 3, 4)] {
        for_each_family(ground, m, cap, &mut |f| {
            let (cl, steps) = shift_closure(f, ground);
            assert_eq!(cl.len(), f.len(), "closure changed size on {f:?}");
            assert!(is_left_compressed(&cl, ground), "closure not compressed on {f:?}");
            if steps > 0 {
                assert!(
                    potential(&cl) < potential(f),
                    "potential did not fall on {f:?}"
                );
            }
        });
    }
}

// ---------------------------------------------------------------------
// 2. It does not preserve sunflower-freeness, and fails at three members.
// ---------------------------------------------------------------------

/// The named counterexample, in both uniformities, checked by hand
/// rather than found by search.
#[test]
fn the_smallest_counterexample() {
    // {0,1} {0,2} {1,3}: the three pairwise intersections are {0}, {1}
    // and the empty set, all different, so it is no sunflower.
    let f: Vec<u32> = vec![0b0011, 0b0101, 0b1010];
    assert!(is_sunflower_free(&f));
    // The (0,1)-shift moves only {1,3}, whose image {0,3} is absent.
    let g = shift_family(&f, 0, 1);
    assert_eq!(g, vec![0b0011, 0b0101, 0b1001]);
    assert!(!is_sunflower_free(&g), "the star {{01,02,03}} is a sunflower");

    // Uniformity 3, the same shape one level up.
    let f3: Vec<u32> = vec![0b00111, 0b01011, 0b10101];
    assert!(is_sunflower_free(&f3));
    let g3 = shift_family(&f3, 1, 2);
    assert!(!is_sunflower_free(&g3));
}

/// Exhaustively: three members is the least a counterexample can have,
/// and four points the least ground set it can live on. Three is also
/// the least a 3-sunflower can have, so shifting fails as early as it is
/// possible to fail.
#[test]
fn the_counterexample_is_minimal() {
    // Nothing at all on three points at uniformity 2: the only
    // sunflower-free families there are already compressed or too small.
    let mut broke_on_three_points = false;
    for_each_family(3, 2, 3, &mut |f| {
        if is_sunflower_free(f) && breaking_shift(f, 3).is_some() {
            broke_on_three_points = true;
        }
    });
    assert!(!broke_on_three_points, "a 3-point counterexample exists");

    // On four points it does, and already at three members.
    let mut smallest = usize::MAX;
    for_each_family(4, 2, 6, &mut |f| {
        if is_sunflower_free(f) && breaking_shift(f, 4).is_some() && f.len() < smallest {
            smallest = f.len();
        }
    });
    assert_eq!(smallest, 3, "smallest counterexample at (2,4)");

    // And at uniformity 3, likewise three members.
    let mut smallest3 = usize::MAX;
    for_each_family(5, 3, 4, &mut |f| {
        if is_sunflower_free(f) && breaking_shift(f, 5).is_some() && f.len() < smallest3 {
            smallest3 = f.len();
        }
    });
    assert_eq!(smallest3, 3, "smallest counterexample at (3,5)");
}

// ---------------------------------------------------------------------
// 3. The maximum is not attained by a compressed family: it is `m + 1`.
// ---------------------------------------------------------------------

/// The `m + 1` bound, exhaustive over every ground set in range, and
/// with the witness identified: all `m`-subsets of an `(m+1)`-set.
///
/// The bound does not move with the ground set. That is the whole
/// content — `N(m,g)` climbs and `ι(m,g)` sits at an exponential value,
/// while the compressed maximum is stuck at `m + 1` however much room it
/// is given.
#[test]
fn compressed_maximum_is_m_plus_one() {
    for m in 1u32..=6 {
        for g in m..=(2 * m + 3).min(13) {
            let (best, witness, _) = max_left_compressed(g, m, false);
            let expect = if g < m + 1 { 1 } else { (m + 1) as usize };
            assert_eq!(best, expect, "left-compressed max at m={m} g={g}");
            assert!(is_sunflower_free(&witness));
            assert!(is_left_compressed(&witness, g));
            if g >= m + 1 {
                let mut w = witness.clone();
                w.sort_unstable();
                let mut expect_w = initial_segment_witness(m);
                expect_w.sort_unstable();
                assert_eq!(w, expect_w, "witness at m={m} g={g}");
            }
        }
    }
}

/// The intersecting question separately, because the extremal `ι`
/// families are regular and regular is very far from compressed. It
/// behaves identically: `m + 1` from `m ≥ 2` on. So compression is no
/// better suited to the intersecting problem than to the general one,
/// even though intersecting-ness is exactly the property shifting was
/// built to preserve.
#[test]
fn compressed_iota_is_also_m_plus_one() {
    for m in 2u32..=6 {
        for g in (m + 1)..=(2 * m + 3).min(13) {
            let (best, witness, _) = max_left_compressed(g, m, true);
            assert_eq!(best, (m + 1) as usize, "compressed iota at m={m} g={g}");
            assert!(is_intersecting(&witness));
            assert!(is_sunflower_free(&witness));
        }
    }
}

/// The witness is genuinely extremal-looking and genuinely useless: all
/// `m`-subsets of an `(m+1)`-set is sunflower-free at every `m`, because
/// two of them meet in `m-1` points and three of them meet pairwise in
/// three *different* `(m-1)`-sets.
#[test]
fn the_compressed_witness_is_sunflower_free_at_every_m() {
    for m in 1u32..=12 {
        let w = initial_segment_witness(m);
        assert_eq!(w.len(), (m + 1) as usize);
        assert!(is_sunflower_free(&w), "m={m}");
        assert!(is_left_compressed(&w, m + 1), "m={m}");
        if m >= 2 {
            assert!(is_intersecting(&w), "m={m}");
        }
    }
}

/// The gap, stated against the numbers the repository already has. This
/// is the assertion worth reading: compression is not lossy, it is
/// destructive.
#[test]
fn compression_collapses_the_problem() {
    // Uniformity 2: six against three.
    let (n26, _, done) = max_sunflower_free(6, 2, BUDGET);
    assert!(done);
    assert_eq!(n26, 6);
    assert_eq!(max_left_compressed(6, 2, false).0, 3);

    // Uniformity 3: ten against four, and the ten is the 1972 seed.
    let (n36, _, done) = max_sunflower_free(6, 3, BUDGET);
    assert!(done);
    assert_eq!(n36, 10);
    assert_eq!(max_left_compressed(6, 3, false).0, 4);

    // Intersecting, uniformity 3: iota(3) = 10 against four.
    let (i36, _, done) = iota(6, 3, BUDGET, 0);
    assert!(done);
    assert_eq!(i36, 10);
    assert_eq!(max_left_compressed(6, 3, true).0, 4);

    // Uniformity 4 on nine points: twenty-seven against five. The value
    // 27 is pinned exhaustively in `tests/iota_ground.rs`; asked as a
    // maximum query rather than a decision it is hours, so this only
    // re-derives the witness.
    let (found, w49, _) = iota_decide(9, 4, 27, BUDGET);
    assert!(found);
    assert_eq!(w49.len(), 27);
    assert_eq!(max_left_compressed(9, 4, true).0, 5);
}

// ---------------------------------------------------------------------
// 4. The mechanism: the empty link survives, every other one does not.
// ---------------------------------------------------------------------

/// Shifting preserves the empty-link condition and breaks a
/// singleton-link one. Exhaustive over every sunflower-free family in
/// range that some shift destroys: in **every** case the matching
/// number of the family itself (the empty link) does not rise, and the
/// core the new sunflower needs is non-empty.
#[test]
fn the_failure_is_always_at_a_non_empty_core() {
    let mut seen = 0usize;
    for (ground, m, cap) in [(4u32, 2u32, 6usize), (5, 2, 5), (6, 2, 4), (5, 3, 4), (6, 3, 4)] {
        for_each_family(ground, m, cap, &mut |f| {
            if !is_sunflower_free(f) {
                return;
            }
            let Some((_, _, g)) = breaking_shift(f, ground) else {
                return;
            };
            seen += 1;
            // The empty link: the matching number never rises. So "no
            // three pairwise disjoint members" survives every shift,
            // and it is the *only* part of sunflower-freeness that does.
            assert!(matching_number(&g) <= matching_number(f));
            assert!(matching_number(&g) <= 2, "nu rose above 2 on {f:?}");
            // The new sunflower therefore has a non-empty core: a
            // sunflower with empty core is three pairwise disjoint
            // members, which nu <= 2 forbids.
            let (nu_before, _) = max_link_matching(f, ground);
            let (nu_after, core) = max_link_matching(&g, ground);
            assert_eq!(nu_before, 2.min(f.len()), "F should be sunflower-free");
            assert!(nu_after >= 3, "no link exceeded 2 on {f:?}");
            assert_ne!(core, 0, "the failing core was empty on {f:?}");
        });
    }
    assert!(seen > 0, "no counterexamples were enumerated at all");
}

/// The same on the family the repository cares about. `two_triangles`
/// attains `f(2,3) - 1 = 6`; every shift that moves it produces a
/// four-member star, so the link at a *point* goes from matching number
/// 2 to 4 while the link at the empty set stays at 2.
#[test]
fn two_triangles_is_destroyed_by_every_shift_that_moves_it() {
    let two_triangles: Vec<u32> = vec![0b000011, 0b000101, 0b000110, 0b011000, 0b101000, 0b110000];
    assert!(is_sunflower_free(&two_triangles));
    assert_eq!(max_link_matching(&two_triangles, 6), (2, 0));

    let mut moved = 0;
    for j in 0..6u32 {
        for i in 0..j {
            let g = shift_family(&two_triangles, i, j);
            if g == two_triangles {
                continue;
            }
            moved += 1;
            assert!(!is_sunflower_free(&g), "({i},{j}) preserved it");
            assert_eq!(matching_number(&g), 2, "the empty link moved");
            let (nu, core) = max_link_matching(&g, 6);
            assert_eq!(nu, 4, "({i},{j})");
            assert_eq!(core.count_ones(), 1, "the failing core is a point");
        }
    }
    assert_eq!(moved, 9, "shifts that move two_triangles");

    // And the closure keeps all six members while losing the property.
    let (cl, steps) = shift_closure(&two_triangles, 6);
    assert_eq!(cl.len(), 6);
    assert!(steps > 0);
    assert!(!is_sunflower_free(&cl));
}

// ---------------------------------------------------------------------
// 5. Diversity: compression and the extremal objects point opposite ways.
// ---------------------------------------------------------------------

fn max_degree(f: &[u32], ground: u32) -> usize {
    (0..ground)
        .map(|x| f.iter().filter(|&&a| a >> x & 1 == 1).count())
        .max()
        .unwrap_or(0)
}

/// `diversity = |F| - maxdeg` measures how far an intersecting family is
/// from a star. Compression drives it to **1**, the least a family with
/// more than one member can have. The extremal `ι` families sit at
/// roughly `|F|/2`. That is the contrast in one number, and it is why
/// shifting is the wrong instrument: it optimises for exactly the shape
/// the extremal objects avoid.
#[test]
fn compression_minimises_diversity_and_the_extremal_families_maximise_it() {
    for m in 2u32..=6 {
        let w = initial_segment_witness(m);
        assert_eq!(w.len() - max_degree(&w, m + 1), 1, "compressed diversity at m={m}");
    }

    let (n, w, done) = iota(6, 3, BUDGET, 0);
    assert!(done);
    assert_eq!(n, 10);
    assert_eq!(w.len() - max_degree(&w, 6), 5, "iota(3,6) diversity");

    let (found, w, _) = iota_decide(9, 4, 27, BUDGET);
    assert!(found);
    assert_eq!(w.len(), 27);
    assert_eq!(w.len() - max_degree(&w, 9), 15, "iota(4,9) diversity");
}

/// Why the degree is the mechanism, tied to the repository's own
/// theorem. `IotaGround.link_degree_ground_bound` caps every degree of a
/// sunflower-free `b`-uniform family on `g` points by `N(b-1, g-1)`.
/// Shifting towards `i` moves members *into* the star at `i`, so it
/// pushes exactly the quantity that theorem bounds. Measured here: the
/// shift that breaks a family is always one that raises `deg(i)`.
#[test]
fn a_breaking_shift_always_raises_the_degree_of_its_target() {
    let mut seen = 0usize;
    for (ground, m, cap) in [(4u32, 2u32, 6usize), (5, 2, 5), (5, 3, 4), (6, 3, 4)] {
        for_each_family(ground, m, cap, &mut |f| {
            if !is_sunflower_free(f) {
                return;
            }
            for j in 0..ground {
                for i in 0..j {
                    let g = shift_family(f, i, j);
                    if g == *f || is_sunflower_free(&g) {
                        continue;
                    }
                    seen += 1;
                    let before = f.iter().filter(|&&a| a >> i & 1 == 1).count();
                    let after = g.iter().filter(|&&a| a >> i & 1 == 1).count();
                    assert!(after > before, "deg({i}) did not rise on {f:?}");
                }
            }
        });
    }
    assert!(seen > 0);
}

// ---------------------------------------------------------------------
// 6. The same question at every sunflower size.
// ---------------------------------------------------------------------

fn binom(n: u64, r: u64) -> u64 {
    if r > n {
        return 0;
    }
    let mut v = 1u64;
    for i in 0..r {
        v = v * (n - i) / (i + 1);
    }
    v
}

/// Nothing above is special to 3. A left-compressed `k`-sunflower-free
/// `m`-uniform family has at most `C(m+k-2, m)` members — **polynomial
/// in `m` of degree `k-2`** — and the bound is attained by all
/// `m`-subsets of an `(m+k-2)`-set.
///
/// Exhaustive over every parameter in range, and it matters which way
/// this cuts: [Mis26] (arXiv:2606.02667, June 2026) proves the
/// Erdős–Rado conjecture for shifted families with the *exponential*
/// bound `s^(2s-2) 2^k` and no lower bound at all. The truth is
/// polynomial, and this says what it is.
#[test]
fn the_compressed_bound_is_polynomial_at_every_sunflower_size() {
    for k in 3usize..=5 {
        for m in 1u32..=3 {
            for g in m..=(m + (k as u32) + 2).min(9) {
                let (best, _, _) = max_left_compressed_k(g, m, k);
                let predicted = binom((m + k as u32 - 2) as u64, m as u64)
                    .min(binom(g as u64, m as u64));
                assert_eq!(
                    best as u64, predicted,
                    "max left-compressed {k}-sunflower-free at m={m}, g={g}"
                );
            }
        }
    }
}

/// The extremal family, at every `k`: all `m`-subsets of an
/// `(m+k-2)`-set is left-compressed and `k`-sunflower-free.
///
/// The proof is a counting argument. Writing `B_i` for the complement of
/// the `i`-th member in the `(m+k-2)`-set, `|B_i| = k-2`; a `k`-sunflower
/// needs every pairwise union `B_i ∪ B_j` to be the same set `C`, so
/// every point of `C` is missing from at most one `B_i` and therefore
/// lies in at least `k-1` of them. Counting incidences,
/// `k(k-2) ≥ |C|(k-1)`, while two distinct `(k-2)`-sets have union at
/// least `k-1`, so `|C| ≥ k-1`. Together `(k-1)² ≤ k(k-2)`, which is
/// false. Checked here rather than assumed.
#[test]
fn the_extremal_compressed_family_at_every_sunflower_size() {
    for k in 3usize..=6 {
        for m in 1u32..=4 {
            let w = initial_segment_witness_k(m, k);
            let g = m + k as u32 - 2;
            assert_eq!(
                w.len() as u64,
                binom(g as u64, m as u64),
                "size at k={k}, m={m}"
            );
            assert!(is_left_compressed(&w, g), "compressed at k={k}, m={m}");
            for i in 0..w.len() {
                assert!(
                    !creates_k_sunflower(&w[..i], w[i], k),
                    "a {k}-sunflower at k={k}, m={m}"
                );
            }
        }
    }
}

/// The degree of the polynomial is `k-2`, so the gap against the
/// unrestricted problem widens at every sunflower size — it is not a
/// `k = 3` accident. At `k = 3` compression permits `m+1` where the
/// truth is exponential; at `k = 4` it permits `(m+2)(m+1)/2`.
#[test]
fn compression_stays_polynomial_while_the_truth_is_exponential() {
    // Degree k-2 in m: check the closed form against the enumeration.
    for k in 3usize..=6 {
        for m in 1u64..=8 {
            let c = binom(m + k as u64 - 2, m);
            let mut poly = 1u64;
            for i in 1..=(k as u64 - 2) {
                poly = poly * (m + i) / i;
            }
            assert_eq!(c, poly, "C(m+k-2,m) is degree k-2 at k={k}, m={m}");
        }
    }
    // And at k = 3 it really is linear, against the proved lower bounds.
    assert_eq!(binom(2 + 1, 2), 3);
    assert_eq!(binom(3 + 1, 3), 4);
    assert_eq!(max_left_compressed(6, 2, false).0, 3);
    assert_eq!(max_left_compressed(6, 3, false).0, 4);
}
