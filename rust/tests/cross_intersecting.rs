//! The two-point-cover case at every uniformity: the arithmetic, checked.
//!
//! `TwoCover.covered_by_two_at_most_star` proves the star extremal among
//! 3-uniform intersecting Rao-spread families of covering number at most
//! 2, once `r >= 4 = m + 1`. docs/roadmap.md §25.4 gives the same
//! statement for every `m` at the same threshold `r >= m + 1`, by reducing
//! it to a pair of cross-intersecting families at uniformity `u = m - 1`:
//!
//! ```text
//!   |A| + |B| <= (r - 1) * r^(u-1)     for r >= u + 2,
//! ```
//!
//! where `A` and `B` are the tails of the two pieces. That argument is
//! **prose, not Coq** (§25.4 says exactly what is missing). What is
//! checked here is its arithmetic core, which is where the threshold
//! `m + 1` comes from, and the one row small enough to exhaust.
//!
//! Writing `a` for the covering number of `A` and `s = a - 1`, the two
//! bounds available are `|A| <= a*r^(u-1)` with `|B| <= u^a*r^(u-a)`, and
//! the same with the roles swapped. Either
//!
//! ```text
//!   (O1)   u^a <= (r - 2 - s) * r^s        or       (O2)   2*u^a <= (r - 1) * r^s
//! ```
//! suffices, and the claim is that every `s` in `0..u-1` satisfies one of
//! them — (O1) when `2s <= u`, (O2) when `2s >= u`, both by Bernoulli.

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
