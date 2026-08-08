//! The two-point-cover case at every uniformity: the arithmetic, checked.
//!
//! `CrossIntersecting.two_cover_star_extremal` proves the star extremal
//! among `m`-uniform intersecting Rao-spread families of covering number
//! at most 2, for every `m`, once `r >= m + 1`. §24.10 had the `m = 3`
//! row; §25.4 gave the general argument in prose and named two Coq pieces
//! as missing; §26 supplies both and proves it. The reduction is to a pair
//! of cross-intersecting families at uniformity `u = m - 1`:
//!
//! ```text
//!   |A| + |B| <= (r - 1) * r^(u-1)     for r >= u + 2,
//! ```
//!
//! which is `CrossIntersecting.cross_pair_bound`. What is checked here is
//! the arithmetic core -- where the threshold `m + 1` comes from -- and
//! the one row small enough to exhaust, both by code sharing nothing with
//! the Coq.
//!
//! Writing `a` for the covering number of `A` and `s = a - 1`, the two
//! bounds available are `|A| <= a*r^(u-1)` with `|B| <= u^a*r^(u-a)`, and
//! the same with the roles swapped. Either
//!
//! ```text
//!   (O1)   u^a <= (r - 2 - s) * r^s        or       (O2)   2*u^a <= (r - 1) * r^s
//! ```
//! suffices, and the claim is that every `s` in `0..u-1` satisfies one of
//! them -- (O1) when `2s <= u`, (O2) when `2s >= u`, both by Bernoulli.
//! `CrossIntersecting.budget_split` is that disjunction in Coq.

/// Minimal big natural: base `10^9` limbs, little-endian. The products
/// compared below run past `u128` well before `u = 30`, and the crate has
/// no dependencies, so this is the arithmetic.
#[derive(Clone, PartialEq, Eq)]
struct Big(Vec<u64>);

const BASE: u64 = 1_000_000_000;

impl Big {
    fn one() -> Big {
        Big(vec![1])
    }
    fn mul_small(&self, k: u64) -> Big {
        let mut out = Vec::with_capacity(self.0.len() + 2);
        let mut carry = 0u64;
        for &d in &self.0 {
            let x = d * k + carry;
            out.push(x % BASE);
            carry = x / BASE;
        }
        while carry > 0 {
            out.push(carry % BASE);
            carry /= BASE;
        }
        while out.len() > 1 && *out.last().unwrap() == 0 {
            out.pop();
        }
        Big(out)
    }
    fn pow(base: u64, e: u64) -> Big {
        let mut a = Big::one();
        for _ in 0..e {
            a = a.mul_small(base);
        }
        a
    }
    fn le(&self, other: &Big) -> bool {
        if self.0.len() != other.0.len() {
            return self.0.len() < other.0.len();
        }
        for i in (0..self.0.len()).rev() {
            if self.0[i] != other.0[i] {
                return self.0[i] < other.0[i];
            }
        }
        true
    }
}

/// `(O1)`: the cover bound on `A` plus the greedy bound on `B`.
/// `u^(s+1) <= (r - 2 - s) * r^s`.
fn o1(u: u64, r: u64, s: u64) -> bool {
    if r < s + 3 {
        return false;
    }
    Big::pow(u, s + 1).le(&Big::pow(r, s).mul_small(r - 2 - s))
}

/// `(O2)`: the greedy bound on both. `2*u^(s+1) <= (r - 1) * r^s`.
fn o2(u: u64, r: u64, s: u64) -> bool {
    Big::pow(u, s + 1)
        .mul_small(2)
        .le(&Big::pow(r, s).mul_small(r - 1))
}

#[test]
fn every_covering_number_is_covered_by_one_of_the_two_options() {
    // u = m - 1, and the threshold is r >= u + 2 = m + 1.
    for u in 1u64..=60 {
        for r in (u + 2)..=(u + 12) {
            for s in 0..u {
                assert!(
                    o1(u, r, s) || o2(u, r, s),
                    "u={u} r={r} s={s}: neither option holds"
                );
            }
        }
    }
}

#[test]
fn the_split_is_exactly_at_twice_s_versus_u() {
    // The proof does not case-split on which option happens to work: it
    // splits on 2s <= u, and Bernoulli does each half. Check that the
    // declared split is the one that goes through, so the write-up is not
    // describing a different proof from the one that closes.
    for u in 1u64..=60 {
        for r in (u + 2)..=(u + 12) {
            for s in 0..u {
                if 2 * s <= u {
                    assert!(o1(u, r, s), "2s <= u should give O1: u={u} r={r} s={s}");
                }
                if 2 * s >= u {
                    assert!(o2(u, r, s), "2s >= u should give O2: u={u} r={r} s={s}");
                }
            }
        }
    }
}

#[test]
fn the_threshold_m_plus_one_is_where_the_star_case_turns_over() {
    // s = 0 is the case where A is a star, and there (O1) reads
    // u <= r - 2, i.e. r >= u + 2 = m + 1 exactly. One below and both
    // options fail, so m+1 is not slack in the write-up.
    for u in 1u64..=60 {
        assert!(o1(u, u + 2, 0), "u={u}: r = u+2 must work at s = 0");
        if u >= 2 {
            assert!(!o1(u, u + 1, 0), "u={u}: r = u+1 must fail at s = 0");
            assert!(!o2(u, u + 1, 0), "u={u}: r = u+1 must fail at s = 0");
        }
    }
}

// ---------------------------------------------------------------------
// the one row small enough to exhaust: u = 2

type Edge = (u32, u32);

fn meets(e: Edge, f: Edge) -> bool {
    e.0 == f.0 || e.0 == f.1 || e.1 == f.0 || e.1 == f.1
}

/// Rao's condition at uniformity 2 with parameter `r`: every point has
/// degree at most `r`, and no edge is repeated (degree at most `r^0 = 1`
/// at a pair), which a set of distinct edges gives for free.
fn rao2(g: &[Edge], n: u32, r: usize) -> bool {
    (0..n).all(|v| g.iter().filter(|e| e.0 == v || e.1 == v).count() <= r)
}

fn all_edges(n: u32) -> Vec<Edge> {
    (0..n).flat_map(|a| (a + 1..n).map(move |b| (a, b))).collect()
}

/// Exhaustive maximum of `|A| + |B|` over nonempty cross-intersecting
/// 2-uniform Rao(`r`) families. Confined as the proof confines it: take
/// an edge of `B` and relabel it `{0,1}`; every edge of `A` meets it.
fn max_cross_pair(n: u32, r: usize) -> usize {
    let edges = all_edges(n);
    let anchor: Vec<Edge> = edges
        .iter()
        .copied()
        .filter(|&(a, b)| a == 0 || a == 1 || b == 0 || b == 1)
        .collect();
    let mut best = 0usize;
    for mask in 0u32..(1u32 << anchor.len()) {
        let a: Vec<Edge> = (0..anchor.len())
            .filter(|i| mask >> i & 1 == 1)
            .map(|i| anchor[i])
            .collect();
        if a.is_empty() || !rao2(&a, n, r) {
            continue;
        }
        let pool: Vec<Edge> = edges
            .iter()
            .copied()
            .filter(|&e| a.iter().all(|&f| meets(e, f)))
            .collect();
        if !pool.contains(&(0, 1)) {
            continue;
        }
        // largest Rao(r) subset of `pool` containing {0,1}
        let rest: Vec<Edge> = pool.iter().copied().filter(|&e| e != (0, 1)).collect();
        let mut bb = 1usize;
        for m2 in 0u32..(1u32 << rest.len()) {
            if 1 + m2.count_ones() as usize <= bb {
                continue;
            }
            let mut b = vec![(0u32, 1u32)];
            b.extend((0..rest.len()).filter(|i| m2 >> i & 1 == 1).map(|i| rest[i]));
            if rao2(&b, n, r) {
                bb = b.len();
            }
        }
        if a.len() + bb > best {
            best = a.len() + bb;
        }
    }
    best
}

#[test]
fn the_cross_intersecting_bound_holds_and_has_slack_at_u_equals_two() {
    // u = 2 is m = 3. The claim is |A| + |B| <= (r-1)*r^(u-1) = (r-1)*r
    // for r >= u + 2 = 4. Exhaustively, the truth is 2r + 1 -- one edge
    // against the two full stars at its endpoints -- so the bound is loose
    // by roughly a factor of r/2. It still closes, because what closes it
    // is the s = 0 row, not the size of the slack.
    //
    // The ground set has to be large enough to hold two stars of degree r;
    // r + 2 points suffice and fewer do not, which the two rows below show.
    for (n, r) in [(7u32, 4usize), (8, 5), (8, 6)] {
        let truth = max_cross_pair(n, r);
        let bound = (r - 1) * r;
        assert!(truth <= bound, "r={r}: truth {truth} exceeds bound {bound}");
        assert_eq!(truth, 2 * r + 1, "r={r} on {n} points");
        // `CrossRefined.cross_pair_refined` gives u*max(2u,r+1)*r^(u-2),
        // which at u = 2 is 2(r+1): one above the truth, against this
        // bound's factor of r/2.
        assert!(truth <= 2 * (r + 1), "r={r}");
        assert_eq!(2 * (r + 1), truth + 1, "r={r}");
    }
    // too few points and the maximum is smaller -- the search is
    // exhaustive on the ground it is given, not on all grounds
    assert_eq!(max_cross_pair(6, 6), 10);

    // adding back the pair-degree term r^(u-1) = r gives the tau <= 2
    // bound on |G| at m = 3 as 3r + 1, against TwoCover's max(4r, 3r+4)
    // and against the star r^2. At r = 4: 13 <= 16 = 4^2.
    for r in 4..=6usize {
        assert!(3 * r + 1 <= r * r, "r={r}");
    }
    assert_eq!(3 * 4 + 1, 13);
    assert_eq!(4 * 4, 16);
}

// ---------------------------------------------------------------------
// why the covering-number-3 piece must carry the Rao condition

/// The witness of `CrossIntersecting.tau_three_piece_unbounded_at_four`:
/// every 3-subset of `{0..4}` with one free coordinate attached.
fn lift(nw: u32) -> Vec<Vec<u32>> {
    let base: Vec<Vec<u32>> = (0..5u32)
        .flat_map(|a| ((a + 1)..5).flat_map(move |b| ((b + 1)..5).map(move |c| vec![a, b, c])))
        .collect();
    let mut out = Vec::new();
    for w in 5..(5 + nw) {
        for c in &base {
            let mut s = c.clone();
            s.push(w);
            out.push(s);
        }
    }
    out
}

fn meets_set(a: &[u32], b: &[u32]) -> bool {
    a.iter().any(|x| b.contains(x))
}

#[test]
fn the_tau_three_piece_is_unbounded_at_uniformity_four() {
    // At m = 3 the same quantity is 10 (Frankl; `rust/tests/tau_three.rs`
    // exhausts it). At m = 4 there is no bound at all without a degree
    // cap, which is why `TauThreePieceAtMost` carries `RaoSpread`.
    for nw in [3u32, 4, 6, 10, 25] {
        let g = lift(nw);
        assert_eq!(g.len() as u32, 10 * nw, "size is 10|W|");
        // 4-uniform, distinct
        assert!(g.iter().all(|c| c.len() == 4));
        let mut sorted: Vec<Vec<u32>> = g.clone();
        for c in sorted.iter_mut() {
            c.sort_unstable();
        }
        sorted.sort();
        sorted.dedup();
        assert_eq!(sorted.len(), g.len(), "distinct");
        // intersecting
        for a in &g {
            for b in &g {
                assert!(meets_set(a, b));
            }
        }
        // covering number at least 3
        let pts: Vec<u32> = (0..(5 + nw)).collect();
        for &p in &pts {
            for &q in &pts {
                assert!(
                    g.iter().any(|c| !c.contains(&p) && !c.contains(&q)),
                    "no member misses {p} and {q}"
                );
            }
        }
        // the degree Rao would cap: a triple of {0..4} sits in |W| members
        let d3 = (0..5u32)
            .flat_map(|a| ((a + 1)..5).flat_map(move |b| ((b + 1)..5).map(move |c| [a, b, c])))
            .map(|t| g.iter().filter(|s| t.iter().all(|x| s.contains(x))).count())
            .max()
            .unwrap();
        assert_eq!(d3 as u32, nw, "deg of a triple is exactly |W|");
    }
    // and 10|W| beats any fixed constant
    assert!(lift(100).len() > 999);
}

#[test]
fn the_general_bound_reproduces_the_three_uniform_row() {
    // two_cover_star_extremal at m = 3 is TwoCover.covered_by_two_at_most_star:
    // (r-1)*r^(u-1) for the two tails, plus r^(m-2) for the pair layer,
    // is exactly the star r^(m-1).
    for m in 2..=12u32 {
        for r in (m + 1)..=(m + 6) {
            let u = m - 1;
            let tails = (r - 1) * r.pow(u - 1);
            let pairs = r.pow(m - 2);
            assert_eq!(tails + pairs, r.pow(m - 1), "m={m} r={r}");
        }
    }
}

// ---------------------------------------------------------------------
// the large-r threshold: m^3 <= r^2

/// `CrossIntersecting.star_extremal_for_large_r` closes every covering
/// number at once from `m^3 <= r^2`. The greedy gives `m^t * r^(m-t)` at
/// covering number `t`, which beats the star `r^(m-1)` iff `m^t <= r^(t-1)`.
#[test]
fn the_binding_covering_number_is_three() {
    for m in 3u64..=40 {
        // least r with m+1 <= r and m^3 <= r^2
        let mut r = m + 1;
        while r * r < m * m * m {
            r += 1;
        }
        // every covering number from 3 up is then covered
        for t in 3..=m {
            let lhs = Big::pow(m, t);
            let rhs = Big::pow(r, t - 1);
            assert!(lhs.le(&rhs), "m={m} r={r} t={t}");
        }
        // and t = 3 is the binding one: one below the threshold it fails
        if r > m + 1 {
            let below = r - 1;
            assert!(
                below * below < m * m * m,
                "m={m}: r-1 should miss the t=3 condition"
            );
            assert!(
                !Big::pow(m, 3).le(&Big::pow(below, 2)),
                "m={m}: t=3 must fail one below"
            );
        }
    }
}

#[test]
fn the_large_r_threshold_is_strictly_above_m_plus_one() {
    // so star_extremal_for_large_r is not §24.13's conjecture: the
    // conjecture is at r = m+1, and m^3 > (m+1)^2 for every m >= 3.
    for m in 3u64..=40 {
        assert!(m * m * m > (m + 1) * (m + 1), "m={m}");
    }
    // at m = 3 the threshold is 6, where TauThree proves the row at 4
    let mut r = 4u64;
    while r * r < 27 {
        r += 1;
    }
    assert_eq!(r, 6);
}
