//! The trace LP at b = 3, and what it does and does not reach.
//!
//! `docs/roadmap.md` §3 of the session brief proposed computing `f(3,3)`
//! exactly from the trace decomposition. This is that decomposition
//! costed out. The finding is negative and it is recorded here rather
//! than in prose alone.
//!
//! Setup: `F` is 3-uniform sunflower-free, `M` a maximal matching. Three
//! pairwise disjoint members are a sunflower with empty core, so
//! `|M| <= 2`; if `|M| = 1` then `F` is intersecting and
//! `|F| <= iota(3) = 10`. So take `|M| = 2`, `T = A1 u A2`, `|T| = 6`,
//! and for `S subseteq T` write `F_S = { A in F : A cap T = S }`.
//!
//! Writing `n_k` for the number of members whose trace has size `k`:
//!
//!   |F| = n1 + n2 + n3            (every member meets T)
//!   n1 + 2 n2 + 3 n3 <= 6 * g(2) = 36     (degree identity, deg(t) <= g(2))
//!   n3 >= 2                        (A1 and A2 are themselves members)
//!   n1 <= 18                       (six classes, each <= iota(2) = 3, by
//!                                   PureLink.trace_class_intersecting)
//!   n1 <= 16                       (cross-intersecting pure links)
//!
//! Eliminating `n2` from the budget gives the whole LP in one line:
//!
//!   |F| <= n1/2 + 18 - n3/2
//!
//! so `n1 <= 18, n3 >= 2` gives 26 and `n1 <= 16` gives 25.
//!
//! ## Two findings, both negative
//!
//! 1. **Without the cross-intersecting constraint the LP gives 26 —
//!    exactly what `PureLink.g_recursion_sharp` proves in half a page.**
//!    The entire trace layer buys nothing over the recursion on its own.
//! 2. **With it the LP gives 25**, one member better, against a
//!    conjectured truth of `g(3) = 20`. The LP is five short and the
//!    slack is structural: it sees class sizes and a degree budget, and
//!    nothing about how the classes interact. **The trace LP cannot
//!    compute `f(3,3)`.**
//!
//! The per-class LP over all 41 trace classes, solved exactly with CBC,
//! returns the same two values (26 and 25) as the aggregate relaxation
//! tested here — the relaxation is tight, so the aggregate is the whole
//! content.
//!
//! Where `n1 <= 16` comes from: for `t =/= t'` in the same `A_i` the pure
//! links `P_t`, `P_t'` are cross-intersecting, since an edge of one
//! disjoint from an edge of the other gives, with the *other* matching
//! member, three pairwise disjoint members. Each `P_t` is an intersecting
//! 2-uniform sunflower-free family, hence a triangle (3 edges), a path
//! (2), an edge or empty. Two triangles are cross-intersecting only if
//! identical, and three identical triangles give members `{t,a,b}` over
//! the three `t in A_i` whose pairwise intersections are all `{a,b}` — a
//! 3-sunflower. So at most two of the three are triangles and
//! `sum_{t in A_i} |P_t| <= 3 + 3 + 2 = 8`.

/// Maximise `n1 + n2 + n3` under the trace budget. `n1_cap` is 18
/// without the cross-intersecting constraint and 16 with it.
fn trace_lp(n1_cap: u32) -> u32 {
    let degree_budget = 6 * 6; // |T| * g(2)
    let n2_cap = 6 * 1 + 9 * 2; // 6 classes inside a matching member (iota(1)=1)
                                // + 9 straddling (g(1) = 2)
    let n3_cap = 20; // every 3-subset of T, each forced to a single member
    let mut best = 0;
    for n1 in 0..=n1_cap {
        for n3 in 2..=n3_cap {
            if n1 + 3 * n3 > degree_budget {
                continue;
            }
            let n2 = ((degree_budget - n1 - 3 * n3) / 2).min(n2_cap);
            best = best.max(n1 + n2 + n3);
        }
    }
    best
}

#[test]
fn trace_lp_without_cross_intersecting_matches_the_recursion() {
    assert_eq!(
        trace_lp(18),
        26,
        "the trace decomposition alone should reproduce \
         PureLink.g_recursion_sharp's g(3) <= 26, no better"
    );
}

#[test]
fn cross_intersecting_is_worth_exactly_one_member() {
    assert_eq!(trace_lp(16), 25, "with cross-intersecting the LP gives 25");
    assert_eq!(
        trace_lp(18) - trace_lp(16),
        1,
        "the cross-intersecting constraint is worth exactly one member"
    );
}

/// The closed form the search above is a check on. Both are recorded
/// because the closed form is what a Coq proof would formalise and the
/// search is what says the closed form did not drop a constraint.
#[test]
fn the_closed_form_agrees_with_the_search() {
    for n1_cap in 0..=18u32 {
        // |F| <= n1/2 + 18 - n3/2, maximised at n1 = n1_cap, n3 = 2,
        // then clamped by the n2 cap.
        let closed = n1_cap / 2 + 18 - 1;
        assert!(
            trace_lp(n1_cap) <= closed,
            "n1_cap={n1_cap}: search gave {} but the closed form caps at {closed}",
            trace_lp(n1_cap)
        );
    }
    assert_eq!(trace_lp(16), 16 / 2 + 18 - 1);
    assert_eq!(trace_lp(18), 18 / 2 + 18 - 1);
}

/// The gap that closes the route. `g(3)` is conjectured to be 20 — the
/// doubling of the 2-(6,3,2) design — and is known to be at least 20
/// (`Intersecting.lower_bound_3_3_20`). The LP stops at 25.
#[test]
fn the_trace_lp_cannot_reach_the_conjectured_value() {
    let known_lower = 20;
    assert!(
        trace_lp(16) > known_lower,
        "if the LP ever reached 20 this test is the thing to delete"
    );
    assert_eq!(
        trace_lp(16) - known_lower,
        5,
        "the trace LP is five members short of deciding g(3)"
    );
}
