//! Does the ground set of an *intersecting* sunflower-free family stay
//! small, where the general one does not?
//!
//! `coq/SliceRank.v` names `GroundBounded c` — "an extremal
//! sunflower-free `m`-uniform family can be realised on at most `c*m`
//! points" — as the one fact that would turn Naslund–Sawin into the
//! sunflower conjecture at `k = 3`, and records that the measurements do
//! not support it: the `m = 3` row of `N(m,g)` is still climbing at
//! `g = 3m`.
//!
//! `coq/IotaGround.v` asks the same question about intersecting
//! families, which `IotaRate.conjecture_k_3_iff_iota_exponential` says is
//! an equivalent problem. This suite is the measurement behind that
//! choice, and it checks three things:
//!
//! 1. **The divergence.** `iota(3,g)` and `N(3,g)` agree at six points
//!    and then separate: the general maximum climbs, the intersecting one
//!    does not move.
//! 2. **The link degree bound**, `b*|F| <= g*N(b-1,g-1)`, which
//!    `IotaGround.link_degree_ground_bound` proves — checked here against
//!    families the proof knows nothing about, and checked for *equality*
//!    at the rows where it is tight.
//! 3. **The structure at those rows.** Equality forces regularity; the
//!    witnesses are regular, and their diversity `|F| - maxdeg` is large,
//!    so the extremal intersecting families are as far from a star as an
//!    intersecting family gets. That is the regime Hilton–Milner and
//!    Frankl's diversity theorems are built for.
//!
//! Cost: everything at uniformity 3 is instant even at fourteen points —
//! intersecting-ness prunes that hard. The `b = 4` rows need `N(3,7)` and
//! `N(3,8)`, which are the expensive part (eighteen seconds for the
//! latter), so they are computed once and cached.

use std::collections::HashMap;
use std::sync::OnceLock;

use sunflower_formal::ground::max_sunflower_free;
use sunflower_formal::intersecting::{iota, iota_decide, verify};

const BUDGET: u64 = 20_000_000_000_000;

/// `N(m, g)`, the general maximum, computed once. `N(3,9)` is a quarter
/// of an hour and is not in this table; nothing here needs it.
fn general(m: u32, g: u32) -> usize {
    static T: OnceLock<HashMap<(u32, u32), usize>> = OnceLock::new();
    let t = T.get_or_init(|| {
        let mut t = HashMap::new();
        for (m, g) in [
            (1u32, 2u32), (1, 5), (1, 8), (1, 9),
            (2, 2), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 13),
            (3, 6), (3, 7), (3, 8),
        ] {
            let (n, _, done) = max_sunflower_free(g, m, BUDGET);
            assert!(done, "N({m},{g}) did not finish");
            t.insert((m, g), n);
        }
        t
    });
    *t.get(&(m, g))
        .unwrap_or_else(|| panic!("N({m},{g}) is not in the cached table"))
}

fn degrees(f: &[u32], ground: u32) -> Vec<usize> {
    (0..ground)
        .map(|x| f.iter().filter(|a| *a >> x & 1 == 1).count())
        .collect()
}

/// 1. The divergence. Both rows are exhaustive.
#[test]
fn the_intersecting_row_plateaus_and_the_general_one_does_not() {
    // iota(3, g) for g = 3 .. 14. Flat at 10 from six points on.
    let row: Vec<usize> = (3..=14u32)
        .map(|g| {
            let (n, fam, done) = iota(g, 3, BUDGET, 0);
            assert!(done, "iota(3,{g}) did not finish");
            if !fam.is_empty() {
                verify(&fam, 3, true).unwrap_or_else(|e| panic!("iota(3,{g}): {e}"));
            }
            n
        })
        .collect();
    assert_eq!(
        row,
        vec![1, 4, 6, 10, 10, 10, 10, 10, 10, 10, 10, 10],
        "the intersecting row moved"
    );

    // iota(2, g) likewise: flat at 3 from three points on, where the
    // general N(2,g) climbs to 6 and only then stops.
    for g in 3..=13u32 {
        let (n, _, done) = iota(g, 2, BUDGET, 0);
        assert!(done);
        assert_eq!(n, 3, "iota(2,{g}) moved");
    }
    assert_eq!(general(2, 5), 5);
    assert_eq!(general(2, 6), 6);
    assert_eq!(general(2, 13), 6);

    // The divergence itself: equal at six points, apart by eight.
    assert_eq!(general(3, 6), 10);
    assert_eq!(row[3], 10); // iota(3,6)
    assert_eq!(general(3, 7), 12);
    assert_eq!(row[4], 10); // iota(3,7) -- the general row has moved, this one has not
    assert_eq!(general(3, 8), 12);
    assert_eq!(row[5], 10);
    // N(3,9) = 14 is a quarter-hour run and is not recomputed here; it is
    // pinned in `rust/examples/ground_scan.rs` and quoted in
    // `docs/roadmap.md` section 7. iota(3,9) is 10, instantly.
    assert_eq!(row[6], 10);
}

/// 2 and 3. The link degree bound, where it is tight, and what tightness
/// forces.
#[test]
fn the_link_degree_bound_holds_and_is_tight_where_the_family_is_regular() {
    // (b, ground, an attained size). The decision search returns as soon
    // as it finds a family of that size, which is what is wanted here.
    let cases: [(u32, u32, usize); 8] = [
        (2, 3, 3),
        (2, 6, 3),
        (3, 6, 10),
        (3, 7, 10),
        (3, 8, 10),
        (3, 9, 10),
        (4, 8, 24),
        (4, 9, 27),
    ];
    let mut tight: Vec<(u32, u32)> = Vec::new();

    for (b, g, target) in cases {
        let (found, fam, _) = iota_decide(g, b, target, BUDGET);
        assert!(found, "no intersecting family of {target} at b={b}, g={g}");
        verify(&fam, b, true).unwrap_or_else(|e| panic!("witness ({b},{g}): {e}"));
        assert_eq!(fam.len(), target);

        let d = degrees(&fam, g);
        let maxdeg = d.iter().copied().max().unwrap();
        let cap = general(b - 1, g - 1);

        // The theorem: b|F| <= g * N(b-1, g-1).
        assert!(
            b as usize * fam.len() <= g as usize * cap,
            "link degree bound fails at b={b}, g={g}"
        );

        if b as usize * fam.len() == g as usize * cap {
            // Equality forces regularity: the degrees sum to b|F| = g*cap
            // over g points, each capped at cap, so every one is exactly
            // cap. Checked rather than assumed.
            assert!(
                d.iter().all(|x| *x == cap),
                "tight at b={b}, g={g} but the family is not {cap}-regular: {d:?}"
            );
            tight.push((b, g));
        }

        // Diversity: how far the extremal family is from a star. A star
        // would have maxdeg = |F| and diversity 0.
        let diversity = fam.len() - maxdeg;
        assert!(
            diversity * 2 >= fam.len() - 1,
            "b={b}, g={g}: diversity {diversity} is small for |F| = {}",
            fam.len()
        );
    }

    // Four of the eight rows are tight, and they are exactly the ones at
    // the small ground sets -- which is where a ground-set bound has to
    // bite. Pinned so a change is visible.
    assert_eq!(
        tight,
        vec![(2, 3), (3, 6), (4, 8), (4, 9)],
        "the set of tight rows moved"
    );
}

/// What tightness forces, checked rather than inferred.
///
/// Equality in `b|F| <= g N(b-1,g-1)` says every point has degree exactly
/// `N(b-1,g-1)`, so every *link* is a maximum-size sunflower-free
/// `(b-1)`-uniform family on the other `g-1` points. That is a statement
/// about `g` derived families, not about the one family, and it is the
/// structure `docs/roadmap.md` section 7 proposes running backwards: glue
/// extremal `N(b-1,g-1)` families together to build an `iota(b,g)`.
///
/// Verified here on the two tight rows that are cheap, with the links
/// re-checked from scratch by a detector that knows nothing about how
/// they arose.
#[test]
fn at_the_tight_rows_every_link_is_extremal() {
    for (b, g, target) in [(3u32, 6u32, 10usize), (4, 8, 24)] {
        let (found, fam, _) = iota_decide(g, b, target, BUDGET);
        assert!(found);
        let cap = general(b - 1, g - 1);
        assert_eq!(b as usize * fam.len(), g as usize * cap, "row is not tight");

        for x in 0..g {
            // The link at x: members through x, with x removed and the
            // ground set renumbered to skip it.
            let link: Vec<u16> = fam
                .iter()
                .filter(|a| *a >> x & 1 == 1)
                .map(|a| {
                    let low = a & ((1u32 << x) - 1);
                    let high = (a >> (x + 1)) << x;
                    (low | high) as u16
                })
                .collect();
            assert_eq!(
                link.len(),
                cap,
                "link at {x} of the ({b},{g}) witness has {} members, not N({},{}) = {cap}",
                link.len(),
                b - 1,
                g - 1
            );
            // And it really is a sunflower-free (b-1)-uniform family on
            // g-1 points -- so it attains N(b-1,g-1), i.e. it is extremal.
            sunflower_formal::ground::verify(&link, b - 1)
                .unwrap_or_else(|e| panic!("link at {x} of ({b},{g}): {e}"));
        }
    }
}

/// The headline structure fact, on its own: the `b = 3` extremal family
/// is 5-regular on six points with diversity 5 out of 10 -- exactly half.
/// `coq/Intersecting.v:iota3` is the transcription of this family, so the
/// Coq witness and the search agree on more than its size.
#[test]
fn the_extremal_three_uniform_family_is_regular_and_diverse() {
    let (found, fam, _) = iota_decide(6, 3, 10, BUDGET);
    assert!(found);
    verify(&fam, 3, true).unwrap();
    let d = degrees(&fam, 6);
    assert_eq!(d, vec![5; 6], "iota(3,6) witness is not 5-regular");
    assert_eq!(fam.len() - 5, 5, "diversity is not |F|/2");

    // The same family, counted the other way: 10 members x 3 points is
    // 30 incidences, and 6 points x N(2,5) = 5 is also 30. The bound is
    // an identity here, which is what `IotaGround` means by TIGHT.
    assert_eq!(3 * fam.len(), 6 * general(2, 5));
}
