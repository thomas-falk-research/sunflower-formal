//! Falsification and instrumentation for `coq/Maximal.v`.
//!
//! The campaign question was: **can a single further `b`-set be added to
//! the Abbott–Hanson–Sauer substitution?** At `b = 9` the substitution
//! builds 10,000 members and `docs/roadmap.md` §12's threshold is
//! 10,001, so one addable set would beat 1972 outright.
//!
//! The answer is no, at every uniformity the repository can build, and
//! this file is what stops that from being a claim:
//!
//! 1. **The trace reduction is checked, not assumed.** `extend.rs`
//!    claims a candidate interacts with the family only through its
//!    trace on the support, so enumerating traces answers the question
//!    for every ground set at once. Here the trace verdict is checked
//!    against actually building the extended family and handing it to
//!    `structure::verify_128`, on every trace of the small rows.
//!
//! 2. **Two independent methods must agree.** A minimal-hitting-set
//!    enumeration and a brute-force trace walk are run on the same
//!    families and must return the same verdict. (The third method, SAT
//!    with two solvers agreeing, lives in `examples/extend_ahs.rs`; it
//!    is not in the test suite because it shells out.)
//!
//! 3. **The mechanism is pinned.** The covering number `tau` of each
//!    substitution family equals its uniformity, and equals the product
//!    of the covering numbers of the two factors. That multiplicativity
//!    is *why* the answer is no, and a future session that changes a
//!    construction will see it here rather than in a different verdict.
//!
//! 4. **Maximal is not maximum.** The Fano plane is a maximal
//!    intersecting 3-uniform family with seven members against
//!    `iota(3) = 10`, which is the witness `coq/Maximal.v` carries so
//!    that the negative result is not over-read.

use sunflower_formal::{extend, intersecting, structure};

fn masks(sets: &[&[u32]]) -> Vec<u32> {
    sets.iter()
        .map(|s| s.iter().fold(0u32, |a, &x| a | 1 << x))
        .collect()
}

fn triangle() -> Vec<u32> {
    masks(&[&[0, 1], &[0, 2], &[1, 2]])
}

fn two_triangles() -> Vec<u32> {
    masks(&[&[0, 1], &[1, 2], &[0, 2], &[3, 4], &[4, 5], &[3, 5]])
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

/// The seven lines of the Fano plane: the difference set `{0,1,3}` and
/// its translates mod 7.
fn fano() -> Vec<u32> {
    (0..7u32)
        .map(|i| (0u32..3).fold(0u32, |a, j| a | 1 << ((i + [0, 1, 3][j as usize]) % 7)))
        .collect()
}

// ---------------------------------------------------------------------
// 1. The trace reduction is a reduction
// ---------------------------------------------------------------------

/// `trace_is_addable` must agree with actually building the extended
/// family and re-verifying it from scratch. This is the claim the whole
/// file rests on: that a point outside the support changes no
/// intersection, so the verdict depends only on the trace.
#[test]
fn the_trace_verdict_agrees_with_rebuilding_the_family() {
    let cases: Vec<(Vec<u128>, usize, bool)> = vec![
        (structure::widen(&triangle()), 2, true),
        (structure::widen(&iota3()), 3, true),
        (structure::widen(&two_triangles()), 2, false),
        (
            intersecting::substitute(&triangle(), 3, &triangle(), 3),
            4,
            true,
        ),
    ];
    let mut checked = 0usize;
    for (f, b, inter) in cases {
        let pts = extend::support_points_128(&f);
        // Every trace of size at most b, as a mask.
        let mut traces: Vec<u128> = Vec::new();
        fn go(pts: &[u32], i: usize, cur: u128, b: usize, out: &mut Vec<u128>) {
            out.push(cur);
            if cur.count_ones() as usize == b {
                return;
            }
            for k in i..pts.len() {
                go(pts, k + 1, cur | 1u128 << pts[k], b, out);
            }
        }
        go(&pts, 0, 0, b, &mut traces);
        for &t in &traces {
            let verdict = extend::trace_is_addable(&f, b, t, inter, true);
            let member = extend::pad_with_fresh(&f, b, t);
            let mut widened = f.clone();
            widened.push(member);
            let rebuilt = structure::verify_128(&widened, b as u32, inter).is_ok();
            assert_eq!(
                verdict, rebuilt,
                "the trace verdict and the rebuilt family disagree at b = {b}, trace {t:#b}"
            );
            checked += 1;
        }
    }
    // Pinned, because the failure mode of an exhaustive check is that it
    // quietly stops being exhaustive.
    // 7 traces on the triangle (b = 2, 3 points), 42 on iota3 (b = 3, 6
    // points), 22 on two_triangles (b = 2, 6 points), 256 on the
    // substitution (b = 4, 9 points).
    assert_eq!(checked, 7 + 42 + 22 + 256, "the trace enumeration changed size");
}

// ---------------------------------------------------------------------
// 2. The verdict, two ways
// ---------------------------------------------------------------------

/// The substitution families admit no extension, and the two methods
/// agree about it. The pure substitutions are settled by the
/// *intersecting* condition alone, which is the stronger negative: no
/// `b`-set meets every member except the members.
#[test]
fn the_substitution_families_are_maximal() {
    let tri = triangle();
    let i3 = iota3();

    let rows: Vec<(&str, Vec<u128>, usize, bool)> = vec![
        (
            "substitute(iota(2), iota(2)) = iota(4,9) = 27",
            intersecting::substitute(&tri, 3, &tri, 3),
            4,
            true,
        ),
        (
            "substitute(iota(2), iota(3)) = 300 at b = 6",
            intersecting::substitute(&tri, 3, &i3, 6),
            6,
            true,
        ),
    ];
    for (name, f, b, brute) in rows {
        structure::verify_128(&f, b as u32, true).unwrap_or_else(|e| panic!("{name}: {e}"));

        // Method one: minimal hitting sets.
        let (hs, done) = extend::minimal_hitting_sets(&f, b, 200_000_000);
        assert!(done, "{name}: the hitting-set enumeration ran out of budget");
        let tau = hs.iter().map(|s| s.count_ones() as usize).min().unwrap();
        assert_eq!(tau, b, "{name}: tau is {tau}, not the uniformity {b}");
        let minimum: Vec<u128> = hs
            .into_iter()
            .filter(|s| s.count_ones() as usize == b)
            .collect();
        assert_eq!(minimum.len(), f.len(), "{name}: wrong number of minimum transversals");
        assert!(
            minimum.iter().all(|s| f.contains(s)),
            "{name}: a minimum transversal is not a member"
        );

        // Method two: brute force over every trace.
        if brute {
            let traces = extend::addable_traces_brute(&f, b, true, false);
            assert!(
                traces.is_empty(),
                "{name}: brute force found {} addable traces",
                traces.len()
            );
        }
    }
}

/// The `b = 9` row, where one addable set would beat 1972. Ten thousand
/// members on thirty-six points: the brute force is `1.4e8` traces and
/// is not run, so this is the hitting-set method alone — cross-checked
/// against brute force at `b = 4` and `b = 6` above, and against SAT
/// with two solvers agreeing in `examples/extend_ahs.rs`.
#[test]
fn the_ten_thousand_member_family_at_b_nine_is_maximal() {
    let i3 = iota3();
    let f = intersecting::substitute(&i3, 6, &i3, 6);
    assert_eq!(f.len(), 10_000);
    assert_eq!(structure::support_count_128(&f), 36);
    structure::verify_128(&f, 9, true).expect("the b = 9 family does not verify");

    let (hs, done) = extend::minimal_hitting_sets(&f, 9, 400_000_000);
    assert!(done, "the hitting-set enumeration ran out of budget at b = 9");
    let tau = hs.iter().map(|s| s.count_ones() as usize).min().unwrap();
    assert_eq!(tau, 9, "tau at b = 9 is {tau}, not 9");
    let minimum: Vec<u128> = hs.into_iter().filter(|s| s.count_ones() == 9).collect();
    assert_eq!(minimum.len(), 10_000);
    assert!(minimum.iter().all(|s| f.contains(s)));
    // So the only 9-set meeting every member is a member: 10,001 is not
    // reachable by extension, on any ground set.
}

/// The cone rows. The apex meets everything, so there the meeting
/// condition is vacuous and the question is whether the *base* extends
/// as a sunflower-free family. It does not.
#[test]
fn the_cone_bases_are_maximal_sunflower_free_families() {
    let base = intersecting::substitute(&two_triangles(), 6, &triangle(), 3);
    assert_eq!(base.len(), 54);
    structure::verify_128(&base, 4, false).expect("the b = 5 base does not verify");
    let traces = extend::addable_traces_brute(&base, 4, false, true);
    assert!(
        traces.is_empty(),
        "the b = 5 base admits {} extensions",
        traces.len()
    );
    // And the apex-free case needs a transversal of size at most 5.
    assert_eq!(
        extend::covering_number(&base, 5, 200_000_000),
        None,
        "tau of the b = 5 base dropped to 5 or below"
    );
}

// ---------------------------------------------------------------------
// 3. The mechanism: tau is multiplicative
// ---------------------------------------------------------------------

/// `tau(substitute(G,H)) = tau(G) * tau(H)`, which is *why* the answer
/// is no: an intersecting family is met by each of its own members, so
/// `tau <= ab`, and the substitution forces `tau >= tau(G) tau(H)`.
/// When both factors have `tau` equal to their uniformity the two meet.
#[test]
fn the_covering_number_is_multiplicative_under_substitution() {
    let tri = structure::widen(&triangle());
    let i3 = structure::widen(&iota3());
    let tt = structure::widen(&two_triangles());

    assert_eq!(extend::covering_number(&tri, 3, 1_000_000), Some(2));
    assert_eq!(extend::covering_number(&i3, 4, 1_000_000), Some(3));
    // g(2) = two_triangles is not intersecting; two points per triangle.
    assert_eq!(extend::covering_number(&tt, 5, 1_000_000), Some(4));

    let cases: &[(&[u128], u32, &[u128], u32, usize)] = &[
        (&tri, 3, &tri, 3, 2 * 2),
        (&tri, 3, &i3, 6, 2 * 3),
        (&i3, 6, &i3, 6, 3 * 3),
        (&tt, 6, &tri, 3, 4 * 2),
    ];
    for &(g, vg, h, wg, want) in cases {
        let gg: Vec<u32> = g.iter().map(|&x| x as u32).collect();
        let hh: Vec<u32> = h.iter().map(|&x| x as u32).collect();
        let f = intersecting::substitute(&gg, vg, &hh, wg);
        assert_eq!(
            extend::covering_number(&f, want + 1, 400_000_000),
            Some(want),
            "tau is not multiplicative on this pair"
        );
    }
}

// ---------------------------------------------------------------------
// 4. Maximal is not maximum
// ---------------------------------------------------------------------

/// The Fano plane is maximal intersecting with seven members, against
/// the exhaustive `iota(3) = 10`. This is the witness `coq/Maximal.v`
/// carries, checked here before it was transcribed: `tau = 3`, the
/// minimum transversals are exactly the seven lines, and it contains a
/// sunflower (so it is not an `iota` witness, which a reader could
/// otherwise mistake it for).
#[test]
fn the_fano_plane_is_maximal_intersecting_with_seven_members() {
    let f = structure::widen(&fano());
    assert_eq!(f.len(), 7);
    assert!(structure::is_intersecting(&fano()));
    assert_eq!(extend::covering_number(&f, 4, 1_000_000), Some(3));
    let (hs, done) = extend::minimal_hitting_sets(&f, 3, 1_000_000);
    assert!(done);
    assert_eq!(hs.len(), 7);
    assert!(hs.iter().all(|s| f.contains(s)));
    // Nothing can be added, even ignoring sunflower-freeness.
    assert!(extend::addable_traces_brute(&f, 3, true, false).is_empty());
    // And it is not an iota witness: three concurrent lines are a
    // sunflower with the common point as core.
    assert!(structure::verify_128(&f, 3, true).is_err());
    // While iota(3) = 10 exists.
    let i3 = structure::widen(&iota3());
    structure::verify_128(&i3, 3, true).expect("iota3 does not verify");
    assert!(i3.len() > f.len());
}

/// And the same phenomenon inside the sunflower-free world, found by
/// random greedy growth in `examples/extend_ahs.rs`: a *six*-member
/// intersecting sunflower-free 3-uniform family to which nothing can be
/// added on any ground set, against `iota(3) = 10`.
#[test]
fn a_six_member_iota_family_is_already_maximal() {
    let f = structure::widen(&masks(&[
        &[3, 6, 8],
        &[2, 3, 8],
        &[0, 3, 4],
        &[4, 5, 8],
        &[3, 4, 6],
        &[1, 4, 8],
    ]));
    structure::verify_128(&f, 3, true).expect("the six-member witness does not verify");
    assert!(
        extend::addable_traces_brute(&f, 3, true, true).is_empty(),
        "the six-member family is not maximal after all"
    );
    assert!(f.len() < 10);
}

// ---------------------------------------------------------------------
// 5. Why prescribed symmetry does not transfer
// ---------------------------------------------------------------------

/// `Maximal.regular_intersecting_ground_bound`: a regular intersecting
/// `b`-uniform family lives on at most `b^2` points.
///
/// **Order of work, recorded because the repository's rule is the other
/// way round.** This one statement was proved in Coq *before* it was
/// enumerated here — it is three lines from `Pigeonhole.pigeonhole_family`
/// and the incidence count, and it was written down as the explanation
/// of a measurement rather than as a conjecture to test. The enumeration
/// below was added afterwards and found no counterexample; that is
/// weaker evidence than the usual order gives, and it is recorded as
/// such rather than presented as falsification.
#[test]
fn regular_intersecting_families_live_on_at_most_b_squared_points() {
    // Every point degree equal?
    fn regular(f: &[u128]) -> bool {
        let pts = extend::support_points_128(f);
        let degs: Vec<usize> = pts
            .iter()
            .map(|&p| f.iter().filter(|&&a| a >> p & 1 == 1).count())
            .collect();
        degs.windows(2).all(|w| w[0] == w[1])
    }

    // The repository's own intersecting witnesses.
    let named: Vec<(&str, Vec<u128>, u32)> = vec![
        ("iota(2) = 3", structure::widen(&triangle()), 2),
        ("iota(3) = 10", structure::widen(&iota3()), 3),
        (
            "iota(4,9) = 27",
            intersecting::substitute(&triangle(), 3, &triangle(), 3),
            4,
        ),
        (
            "substitute(iota(2), iota(3)) = 300",
            intersecting::substitute(&triangle(), 3, &iota3(), 6),
            6,
        ),
        ("the Fano plane", structure::widen(&fano()), 3),
    ];
    for (name, f, b) in &named {
        let g = structure::support_count_128(f) as usize;
        if regular(f) {
            assert!(
                g <= (*b as usize) * (*b as usize),
                "{name} is regular on {g} points, above b^2 = {}",
                b * b
            );
        }
    }

    // And the theorem's contrapositive on the family that refutes the
    // universal ground reading: the cone of the tree paths is
    // intersecting on `2^b - 1` points, far past `b^2`, so it *must* be
    // irregular -- and it is, the apex having degree |F|.
    for d in 3u32..=6 {
        let tp = structure::tree_paths_128(d);
        let apex = (1u32 << (d + 1)) - 2;
        let h = structure::cone_128(&tp, apex);
        let b = d + 1;
        let g = structure::support_count_128(&h);
        structure::verify_128(&h, b, true).expect("the coned tree paths do not verify");
        assert_eq!(g, (1 << b) - 1);
        if g as usize > (b * b) as usize {
            assert!(
                !regular(&h),
                "a regular intersecting family on {g} > b^2 points would refute \
                 Maximal.regular_intersecting_ground_bound"
            );
        }
    }
}

/// The Kramer–Mesner obstruction, as a measurement rather than a claim:
/// a `G`-invariant sunflower-free family is a union of orbits, so every
/// orbit must itself have no three pairwise disjoint members. For a
/// group acting on a ground set much larger than `3b` an orbit almost
/// always contains three disjoint translates, and then the orbit is
/// unusable.
///
/// Pinned at the two ends the campaign measured: at `b = 3` on sixteen
/// points *no* orbit of any group in the standard list survives, and at
/// `b = 5` on fifteen most of them do.
#[test]
fn orbits_are_usable_only_when_the_ground_set_is_small_against_three_b() {
    use sunflower_formal::orbit;
    for &(g, b, want_any) in &[(16u32, 3u32, false), (15, 5, true)] {
        let mut any = false;
        for (_name, gens) in orbit::standard_groups(g) {
            let group = match orbit::group_closure(g, &gens, 20_000) {
                Some(gr) => gr,
                None => continue,
            };
            let orbits = orbit::orbits_on_subsets(g, b, &group);
            if orbits.iter().any(|o| orbit::verify(o, b, false).is_ok()) {
                any = true;
                break;
            }
        }
        assert_eq!(
            any, want_any,
            "usable orbits at (b,g) = ({b},{g}) changed: 3b = {}",
            3 * b
        );
    }
}
