//! Falsification and instrumentation for `coq/Product.v`.
//!
//! Four jobs, in the order the repository's discipline puts them.
//!
//! 1. **Falsify before proving.** Every statement in `coq/Product.v` is
//!    enumerated here against an independent checker before it was
//!    trusted: the cone preserves sunflower-freeness and forces
//!    intersecting-ness; the direct sum of two intersecting families is
//!    intersecting; `link [p] (cone p F) = F`; and the two ground-set
//!    hypotheses relate the way the theorems say. The checker
//!    (`intersecting::verify`, `structure::verify_128`) shares no code
//!    with any construction.
//!
//! 2. **Kill the closed forms.** `docs/roadmap.md` §5 tabulates the
//!    measured `iota` values and the obvious guesses at a formula. Each
//!    guess is evaluated here and each failure is *asserted*, so a future
//!    session cannot re-propose one that the data already refutes.
//!
//! 3. **Pin the structure.** The automorphism group orders, the design
//!    parameters, the per-core link matching numbers and the degree
//!    sequences of every extremal witness. A witness that stopped being
//!    extremal, or an invariant that drifted, is a failing assertion
//!    rather than a silently different table.
//!
//! 4. **Pin the extended table.** `iota(5) >= 54`, `iota(6) >= 300`,
//!    `iota(7) >= 600` come from constructions, not from search, so the
//!    families are rebuilt and re-verified on every run.

use sunflower_formal::{ground, intersecting, link, structure};

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

fn iota4() -> Vec<u32> {
    vec![
        15, 23, 27, 45, 46, 53, 54, 57, 58, 195, 204, 212, 216, 225, 226, 323, 332, 340, 344, 353,
        354, 387, 396, 404, 408, 417, 418,
    ]
}

/// Every `m`-uniform 3-sunflower-free family on `g` points, by DFS over
/// the `m`-subsets in increasing order. The count is returned so a
/// silently-truncated enumeration is a failing assertion rather than a
/// smaller table.
fn for_each_sunflower_free<F: FnMut(&[u32])>(g: u32, m: u32, mut visit: F) -> usize {
    let sets: Vec<u32> = ground::m_subsets(g, m).into_iter().map(u32::from).collect();
    let mut count = 0usize;
    let mut cur: Vec<u32> = Vec::new();
    fn go<F: FnMut(&[u32])>(
        sets: &[u32],
        i: usize,
        cur: &mut Vec<u32>,
        visit: &mut F,
        count: &mut usize,
    ) {
        visit(cur);
        *count += 1;
        for j in i..sets.len() {
            let x = sets[j];
            let mut ok = true;
            for a in 0..cur.len() {
                for b in (a + 1)..cur.len() {
                    if structure::is_sunflower(cur[a], cur[b], x) {
                        ok = false;
                    }
                }
            }
            if ok {
                cur.push(x);
                go(sets, j + 1, cur, visit, count);
                cur.pop();
            }
        }
    }
    go(&sets, 0, &mut cur, &mut visit, &mut count);
    count
}

// ---------------------------------------------------------------------
// 1. Falsification
// ---------------------------------------------------------------------

/// `Product.cone_no_sunflower`, `cone_Intersecting`, `cone_Uniform`,
/// `cone_Distinct`: exhaustively, over every sunflower-free family in
/// range. The apex is a fresh point, as `Product.Fresh` demands.
#[test]
fn the_cone_preserves_sunflower_freeness_and_forces_intersecting() {
    let mut total = 0usize;
    for (g, m) in [(4u32, 2u32), (5, 2), (6, 2), (4, 3), (5, 3), (6, 3)] {
        let seen = for_each_sunflower_free(g, m, |f| {
            if f.is_empty() {
                return;
            }
            let c = structure::cone(f, g);
            // uniformity, distinctness, intersecting-ness, sunflower-freeness
            intersecting::verify(&c, m + 1, true).unwrap_or_else(|e| {
                panic!("cone of {f:?} at (g={g}, m={m}) failed: {e}");
            });
            assert_eq!(c.len(), f.len(), "the cone must keep the size");
        });
        total += seen;
    }
    // Pinned so a truncation reads as a failure, not as a smaller table.
    // 35548 = the number of 3-sunflower-free families (including the empty
    // one) over the six (ground, uniformity) pairs enumerated above.
    assert_eq!(total, 35_548, "the enumeration changed size");
}

/// The cone is exactly the inverse of the link at its apex:
/// `Product.link_of_cone` says `link [p] (cone p F) = F` *literally*.
#[test]
fn the_link_at_the_apex_recovers_the_family() {
    let mut checked = 0usize;
    for (g, m) in [(5u32, 2u32), (6, 2), (5, 3), (6, 3)] {
        for_each_sunflower_free(g, m, |f| {
            let c = structure::cone(f, g);
            assert_eq!(link::link(1 << g, &c), f.to_vec());
            checked += 1;
        });
    }
    assert!(checked > 10_000, "only {checked} families checked");
}

/// And the fibre it recovers is in general **not** intersecting, which is
/// `Product.the_split_fibres_are_not_intersecting`: a splitting argument
/// cannot bound the fibres by `iota`.
#[test]
fn the_fibre_of_a_cone_is_not_intersecting() {
    let tt = two_triangles();
    let c = structure::cone(&tt, 6);
    intersecting::verify(&c, 3, true).expect("the cone is an iota witness");
    let fibre = link::link(1 << 6, &c);
    assert_eq!(fibre, tt);
    assert!(
        !structure::is_intersecting(&fibre),
        "two disjoint triangles are not intersecting"
    );
    // And it is twice iota(2) = 3, so no intersecting bound applies.
    assert_eq!(fibre.len(), 6);
    let (iota2, _, done) = intersecting::iota(6, 2, 4_000_000_000, 0);
    assert!(done);
    assert_eq!(iota2, 3);
}

/// `Product.sum_family_Intersecting` and `iota_supermultiplicative`: the
/// direct sum on disjoint grounds of two intersecting sunflower-free
/// families is one, with the product size.
#[test]
fn the_direct_sum_is_supermultiplicative_for_iota() {
    let seeds: Vec<(u32, u32, Vec<u32>)> = vec![
        (2, 3, triangle()),
        (3, 6, iota3()),
        (4, 9, iota4()),
    ];
    for (a, ga, fa) in &seeds {
        for (b, _, fb) in &seeds {
            if a + b > 8 {
                continue;
            }
            let s = structure::direct_sum(fa, fb, *ga);
            assert_eq!(s.len(), fa.len() * fb.len());
            intersecting::verify(&s, a + b, true)
                .unwrap_or_else(|e| panic!("direct sum at ({a},{b}) failed: {e}"));
        }
    }
}

/// The universal reading of `IotaGroundBounded` is false: the cone of the
/// [FPPTZ24] tree-path family is an intersecting 3-sunflower-free
/// `b`-uniform family with `2^(b-1)` members on `2^b - 1` points, every
/// one of them used.
#[test]
fn an_intersecting_family_can_need_an_exponential_ground_set() {
    for d in 2u32..=6 {
        let tp = structure::tree_paths_128(d);
        let apex = (1u32 << (d + 1)) - 2;
        let h = structure::cone_128(&tp, apex);
        let b = d + 1;
        assert_eq!(h.len(), 1usize << (b - 1));
        assert_eq!(structure::support_count_128(&h), (1u32 << b) - 1);
        structure::verify_128(&h, b, true)
            .unwrap_or_else(|e| panic!("cone of tree_paths({d}) failed: {e}"));
    }
    // The k = 3 instance transcribed into `coq/Product.v` is the b = 4 one:
    // eight 4-sets on fifteen points.
    let h = structure::cone_128(&structure::tree_paths_128(3), 14);
    assert_eq!(h.len(), 8);
    assert_eq!(structure::support_count_128(&h), 15);
}

// ---------------------------------------------------------------------
// 2. Killing the closed forms
// ---------------------------------------------------------------------

fn binom(n: u64, k: u64) -> u64 {
    if k > n {
        return 0;
    }
    let mut r = 1u64;
    for i in 0..k {
        r = r * (n - i) / (i + 1);
    }
    r
}

/// The measured and constructed `iota` row, `b = 1..7`. Entries at
/// `b >= 5` are lower bounds; a closed form is killed by a *lower* bound
/// exceeding it just as well as by an exact value differing from it.
const IOTA: &[(u32, u64, bool)] = &[
    (1, 1, true),
    (2, 3, true),
    (3, 10, true),
    (4, 27, true), // exact at ground 9; grounds >= 10 open
    (5, 54, false),
    (6, 300, false),
    (7, 600, false),
];

#[test]
fn the_obvious_closed_forms_are_dead() {
    // Each candidate: name, formula, and the b where it dies.
    let candidates: Vec<(&str, Box<dyn Fn(u32) -> u64>)> = vec![
        ("C(2b-1, b-1)", Box::new(|b: u32| binom(2 * b as u64 - 1, b as u64 - 1))),
        ("C(2b, b)/2", Box::new(|b: u32| binom(2 * b as u64, b as u64) / 2)),
        ("3^(b-1)", Box::new(|b: u32| 3u64.pow(b - 1))),
        ("2^(b-1)", Box::new(|b: u32| 2u64.pow(b - 1))),
        ("Catalan(b)", Box::new(|b: u32| binom(2 * b as u64, b as u64) / (b as u64 + 1))),
        ("Motzkin-ish 2^b - b", Box::new(|b: u32| 2u64.pow(b) - b as u64)),
        ("b!", Box::new(|b: u32| (1..=b as u64).product())),
        ("C(2b-2, b-1)", Box::new(|b: u32| binom(2 * b as u64 - 2, b as u64 - 1))),
    ];
    for (name, f) in &candidates {
        let mut died_at = None;
        for &(b, v, exact) in IOTA {
            let p = f(b);
            let dead = if exact { p != v } else { p < v };
            if dead {
                died_at = Some((b, p, v, exact));
                break;
            }
        }
        let (b, p, v, exact) = died_at
            .unwrap_or_else(|| panic!("candidate {name} survives the whole measured row"));
        println!(
            "  killed {name:22} at b = {b}: predicts {p}, {} {v}",
            if exact { "truth is" } else { "truth is at least" }
        );
    }
}

/// The specific trap `docs/roadmap.md` warns about: all `b`-subsets of
/// `[2b-1]` is intersecting and has `C(2b-1,b)` members, which matches
/// the complementary-pair ceiling — but it *contains a sunflower* from
/// `b = 3` on, because `{0,..,b-2}` plus any of the `b` remaining points
/// gives `b >= 3` sets with the same pairwise intersection.
#[test]
fn all_b_subsets_of_2b_minus_1_is_intersecting_but_has_a_sunflower() {
    for b in 2u32..=4 {
        let g = 2 * b - 1;
        let f: Vec<u32> = ground::m_subsets(g, b).into_iter().map(u32::from).collect();
        assert!(
            structure::is_intersecting(&f),
            "two b-sets in [2b-1] must meet"
        );
        let has_sunflower = intersecting::verify(&f, b, true).is_err();
        if b == 2 {
            // Three 2-sets of [3] are a triangle: no sunflower.
            assert!(!has_sunflower);
            assert_eq!(f.len(), 3);
        } else {
            assert!(
                has_sunflower,
                "all {b}-subsets of [{g}] should contain a 3-sunflower"
            );
        }
    }
}

/// The complementary-pair ceiling `iota(b, 2b) <= C(2b,b)/2` and where it
/// stops being met. `rust/tests/intersecting.rs` already checks the
/// transversal structure; this pins the *numbers* against the extended
/// row, including that `b = 4` falls short.
#[test]
fn the_complementary_pair_ceiling_is_not_met_from_b_equals_four() {
    let rows: &[(u32, u64)] = &[(2, 3), (3, 10), (4, 24)]; // iota(b, 2b)
    for &(b, v) in rows {
        let ceiling = binom(2 * b as u64, b as u64) / 2;
        assert!(v <= ceiling, "iota({b},{}) exceeds the ceiling", 2 * b);
        if b <= 3 {
            assert_eq!(v, ceiling, "the ceiling is met at b = {b}");
        } else {
            assert!(v < ceiling, "the ceiling should not be met at b = {b}");
        }
    }
}

/// And the Abbott–Hanson–Sauer threshold: the record moves the moment some
/// `b` has `iota(b) > 10^((b-1)/2)`. Every value the table reaches, exact
/// or constructed, sits **below** it — which is what the substitution's
/// own fixed point predicts, and is the reason the extended row is not a
/// new record.
#[test]
fn nothing_in_the_table_beats_the_1972_rate() {
    for &(b, v, _) in IOTA {
        // 10^((b-1)/2) compared without floating point: v^2 vs 10^(b-1).
        let lhs = (v as u128) * (v as u128);
        let rhs = 10u128.pow(b - 1);
        assert!(
            lhs <= rhs,
            "iota({b}) >= {v} would beat AHS: {v}^2 = {lhs} > 10^{} = {rhs}",
            b - 1
        );
    }
}

// ---------------------------------------------------------------------
// 3. Pinning the structure of the extremal families
// ---------------------------------------------------------------------

/// The automorphism group orders, cross-checked against `nauty` by hand
/// (`dreadnaut` input is emitted by `examples/iota_structure --nauty`) and
/// pinned here so a changed witness is a failing test.
#[test]
fn the_extremal_families_have_the_recorded_automorphism_groups() {
    let cases: &[(&str, Vec<u32>, u32, u64)] = &[
        ("iota(2,3)", triangle(), 2, 6),
        ("iota(3,6)", iota3(), 3, 60),
        ("iota(4,9)", iota4(), 4, 1296),
    ];
    for (name, f, b, order) in cases {
        intersecting::verify(f, *b, true).unwrap_or_else(|e| panic!("{name}: {e}"));
        let (o, _) = structure::automorphisms(f);
        assert_eq!(o, *order, "{name} automorphism group order");
    }
}

/// `iota(3) = 10` **is** the unique simple 2-(6,3,2) design: 5-regular on
/// six points with every pair in exactly two blocks, and automorphism
/// group of order 60. That is the "identify the object" item of
/// `docs/roadmap.md` §10 answered at `b = 3`.
#[test]
fn iota_three_is_the_two_six_three_two_design() {
    let f = iota3();
    assert_eq!(structure::design_parameters(&f), Some((6, 3, 2, 5)));
    assert_eq!(structure::automorphisms(&f).0, 60);
    assert_eq!(structure::point_orbit_sizes(&f), vec![6]);
    // Maximally non-star: diversity |F| - maxdeg is half the family.
    assert_eq!(structure::diversity(&f), 5);
}

/// **The uniqueness, verified rather than cited.** `docs/references.md`
/// recorded "that uniqueness is standard design theory and is *taken on
/// the literature's word here*, not verified" — the Handbook of
/// Combinatorial Designs is not open access and the July 2026 reading
/// session could not reach a primary source for it.
///
/// It does not need one. There are only `C(20,10) = 184756` ways to pick
/// ten triples from the twenty on six points, so the question is decided
/// by enumeration: exactly **12** of them are simple 2-(6,3,2) designs,
/// and all 12 lie in a **single** isomorphism class under `Sym(6)`.
/// `720 / 12 = 60` re-derives the automorphism group order a second way,
/// independently of `structure::automorphisms`, which is the point of
/// doing it here rather than trusting the citation.
///
/// (60 is `|PSL(2,5)| = |A_5|` acting on the six points of the projective
/// line over `F_5`; its two orbits on triples are the two complementary
/// 2-(6,3,2) designs, swapped by `PGL(2,5)`. The *order* is what is
/// computed; the isomorphism type is not, and is not claimed.)
#[test]
fn the_two_six_three_two_design_is_unique_and_that_is_checked_not_cited() {
    // All 3-subsets of a 6-set, as bitmasks.
    let triples: Vec<u32> = (0..6u32)
        .flat_map(|a| ((a + 1)..6).flat_map(move |b| ((b + 1)..6).map(move |c| (a, b, c))))
        .map(|(a, b, c)| (1 << a) | (1 << b) | (1 << c))
        .collect();
    assert_eq!(triples.len(), 20);

    let pairs: Vec<u32> = (0..6u32)
        .flat_map(|a| ((a + 1)..6).map(move |b| (1u32 << a) | (1 << b)))
        .collect();
    assert_eq!(pairs.len(), 15);

    // Every simple 2-(6,3,2) design, by exhaustion over C(20,10).
    let mut designs: Vec<Vec<u32>> = Vec::new();
    let mut choice = [0usize; 10];
    fn rec(
        start: usize,
        depth: usize,
        choice: &mut [usize; 10],
        triples: &[u32],
        pairs: &[u32],
        out: &mut Vec<Vec<u32>>,
    ) {
        if depth == 10 {
            let blocks: Vec<u32> = choice.iter().map(|&i| triples[i]).collect();
            // lambda = 2: every pair lies in exactly two blocks.
            if pairs
                .iter()
                .all(|&p| blocks.iter().filter(|&&b| b & p == p).count() == 2)
            {
                out.push(blocks);
            }
            return;
        }
        for i in start..triples.len() {
            choice[depth] = i;
            rec(i + 1, depth + 1, choice, triples, pairs, out);
        }
    }
    rec(0, 0, &mut choice, &triples, &pairs, &mut designs);
    assert_eq!(designs.len(), 12, "labelled simple 2-(6,3,2) designs");

    // Canonical form under Sym(6): the lexicographically least relabelling.
    fn canon(blocks: &[u32]) -> Vec<u32> {
        let mut best: Option<Vec<u32>> = None;
        let mut perm = [0u32; 6];
        fn perms(k: usize, used: u32, perm: &mut [u32; 6], f: &mut impl FnMut(&[u32; 6])) {
            if k == 6 {
                f(perm);
                return;
            }
            for v in 0..6u32 {
                if used & (1 << v) == 0 {
                    perm[k] = v;
                    perms(k + 1, used | (1 << v), perm, f);
                }
            }
        }
        perms(0, 0, &mut perm, &mut |p| {
            let mut img: Vec<u32> = blocks
                .iter()
                .map(|&b| {
                    (0..6u32)
                        .filter(|i| b & (1 << i) != 0)
                        .fold(0u32, |a, i| a | 1 << p[i as usize])
                })
                .collect();
            img.sort_unstable();
            if best.as_ref().is_none_or(|cur| img < *cur) {
                best = Some(img);
            }
        });
        best.unwrap()
    }

    let mut classes: Vec<Vec<u32>> = designs.iter().map(|d| canon(d)).collect();
    classes.sort();
    classes.dedup();
    assert_eq!(classes.len(), 1, "isomorphism classes of simple 2-(6,3,2)");

    // |Aut| = |Sym(6)| / (orbit size), computed without touching
    // structure::automorphisms -- and agreeing with it.
    assert_eq!(720 / designs.len(), 60);
    assert_eq!(structure::automorphisms(&iota3()).0, 60);

    // And the object the search found really is in that class.
    assert_eq!(canon(&iota3()), classes[0]);
}

/// `iota(4,9) = 27` **is** the Abbott–Hanson–Sauer substitution of the
/// triangle into itself. Three triples of points; every union of a pair
/// from one triple with a pair from another. `|Aut| = 6 * 6^3 = 1296` is
/// exactly `Sym(3)` on the triples times `Sym(3)` inside each, which is
/// the symmetry the substitution predicts and nothing else would have.
#[test]
fn iota_four_is_the_substitution_of_the_triangle_into_itself() {
    let f = iota4();
    // Rebuild it from the substitution and check the two agree as sets.
    let groups: [[u32; 3]; 3] = [[0, 1, 5], [2, 3, 4], [6, 7, 8]];
    let mut built: Vec<u32> = Vec::new();
    for i in 0..3 {
        for j in (i + 1)..3 {
            for &(a, b) in &[(0usize, 1usize), (0, 2), (1, 2)] {
                for &(c, d) in &[(0usize, 1usize), (0, 2), (1, 2)] {
                    built.push(
                        (1 << groups[i][a])
                            | (1 << groups[i][b])
                            | (1 << groups[j][c])
                            | (1 << groups[j][d]),
                    );
                }
            }
        }
    }
    built.sort_unstable();
    let mut want = f.clone();
    want.sort_unstable();
    assert_eq!(built.len(), 27);
    assert_eq!(built, want, "iota(4,9) is not the substitution family");
    assert_eq!(structure::automorphisms(&f).0, 6 * 6 * 6 * 6);
    // And the substitution's arithmetic: iota(2) * iota(2)^2 = 3 * 9.
    assert_eq!(3 * 3 * 3, 27);
}

/// The clauses of `LinkCharacterisation.sunflower_iff_link_matching`, one
/// per core, on the extremal witnesses. The measurement `docs/roadmap.md`
/// §10 (the entropy item) asks for: **do the savings from different cores
/// multiply, or repeat?** They repeat — at `iota(4,9)` *every* core of
/// size 1, 2 or 3 with a nonempty link is tight (`nu = 2`), so there is no
/// slack anywhere to trade between cores.
#[test]
fn every_intermediate_core_of_the_extremal_families_is_tight() {
    let cases: &[(&str, Vec<u32>, u32)] = &[
        ("iota(3,6)", iota3(), 3),
        ("iota(4,9)", iota4(), 4),
    ];
    for (name, f, b) in cases {
        let p = structure::link_profile(f);
        assert_eq!(p.max_nu, 2, "{name} must be sunflower-free");
        for j in 1..(*b as usize) {
            let (nonempty, tight, max) = p.by_size[j];
            assert!(nonempty > 0, "{name}: no cores of size {j}");
            assert_eq!(
                tight, nonempty,
                "{name}: only {tight} of {nonempty} cores of size {j} are tight"
            );
            assert_eq!(max, 2);
        }
        // The top level |Y| = b is the members themselves: nu = 1.
        assert_eq!(p.by_size[*b as usize].2, 1);
    }
}

/// A `(b-1)`-set lies in at most **two** members of a sunflower-free
/// `b`-uniform family — the link there is a family of singletons, so its
/// matching number is its size. Counting incidences gives
/// `b|F| <= 2 |shadow_{b-1}(F)| <= 2 C(g, b-1)`, which is *tight* at
/// `(b,g) = (2,3)` and `(3,6)`. Not formalised; recorded here because it
/// is the `|Y| = b-1` end of `IotaGround.link_degree_ground_bound`, whose
/// `|Y| = 1` end is the theorem.
#[test]
fn a_b_minus_one_set_lies_in_at_most_two_members() {
    let cases: &[(&str, Vec<u32>, u32, u32)] = &[
        ("iota(2,3)", triangle(), 2, 3),
        ("iota(3,6)", iota3(), 3, 6),
        ("iota(4,9)", iota4(), 4, 9),
        ("g(2) = two_triangles", two_triangles(), 2, 6),
    ];
    for (name, f, b, g) in cases {
        let sh = structure::shadow_sizes(f);
        // every (b-1)-subset of a member is in at most 2 members
        for &a in f {
            let bits: Vec<u32> = (0..32).filter(|x| a >> x & 1 == 1).collect();
            for skip in 0..bits.len() {
                let y = bits
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| *i != skip)
                    .fold(0u32, |m, (_, &p)| m | 1 << p);
                assert!(
                    structure::deg(f, y) <= 2,
                    "{name}: a (b-1)-set has degree {}",
                    structure::deg(f, y)
                );
            }
        }
        let bound = 2 * binom(*g as u64, *b as u64 - 1) / *b as u64;
        assert!(
            f.len() as u64 <= bound,
            "{name}: {} members against the bound {bound}",
            f.len()
        );
        assert_eq!(sh[*b as usize - 1] * 2, f.len() * *b as usize,
            "{name}: every (b-1)-set in the shadow should have degree exactly 2");
    }
}

// ---------------------------------------------------------------------
// 4. The extended table
// ---------------------------------------------------------------------

/// `iota(5) >= 54`, `iota(6) >= 300`, `iota(7) >= 600`, each rebuilt from
/// the cone and the substitution and re-verified. The previous best at
/// `b = 5` was 42 (SAT at ground 10, `docs/roadmap.md` §9); `b = 6` and
/// `b = 7` had never been computed.
#[test]
fn the_constructed_rows_of_the_iota_table_verify() {
    let tri = triangle();
    let tt = two_triangles();
    let i3 = iota3();

    // b = 5: cone of substitute(g(2), iota(2)), 6 * 3^2 = 54 members.
    let g4 = intersecting::substitute(&tt, 6, &tri, 3);
    assert_eq!(g4.len(), 54);
    let h5 = structure::cone_128(&g4, 18);
    structure::verify_128(&h5, 5, true).expect("iota(5) >= 54");
    assert_eq!(h5.len(), 54);
    assert_eq!(structure::support_count_128(&h5), 19);

    // b = 6: substitute(iota(2), iota(3)), 3 * 10^2 = 300 members.
    let h6 = intersecting::substitute(&tri, 3, &i3, 6);
    assert_eq!(h6.len(), 300);
    structure::verify_128(&h6, 6, true).expect("iota(6) >= 300");
    assert_eq!(structure::support_count_128(&h6), 18);

    // b = 7: cone of substitute(g(2), iota(3)), 6 * 10^2 = 600 members.
    let g6 = intersecting::substitute(&tt, 6, &i3, 6);
    assert_eq!(g6.len(), 600);
    let h7 = structure::cone_128(&g6, 36);
    structure::verify_128(&h7, 7, true).expect("iota(7) >= 600");
    assert_eq!(structure::support_count_128(&h7), 37);

    // The cone beats both previous b = 5 lower bounds: 42 (SAT) and the
    // direct sum's iota(2) * iota(3) = 30.
    assert!(54 > 42 && 54 > 3 * 10);
}

/// The measured multiplicative defect `iota(a+b) / (iota(a) iota(b))`, and
/// the local ratio `iota(b+1)/iota(b)`. `Product.step_bounded_settles_k3`
/// says a bound on the second settles `k = 3`; every value the table
/// reaches sits between 2 and 4, and `Product.step_bounded_needs_D_at_least_three`
/// proves any admissible constant is at least 3.
#[test]
fn the_measured_defect_and_ratio_stay_between_two_and_four() {
    // Only the exhaustively decided values can bound a *ratio* from above.
    let exact: &[(u32, u64)] = &[(1, 1), (2, 3), (3, 10), (4, 27)];
    for w in exact.windows(2) {
        let (_, a) = w[0];
        let (_, b) = w[1];
        let r = b as f64 / a as f64;
        assert!(
            (2.0..=4.0).contains(&r),
            "the ratio iota(b+1)/iota(b) left [2,4]: {r}"
        );
    }
    // The defect, on the pairs both of whose entries are exact.
    for &(a, va) in exact {
        for &(b, vb) in exact {
            if let Some(&(_, vab)) = exact.iter().find(|(x, _)| *x == a + b) {
                let d = vab as f64 / (va * vb) as f64;
                assert!(
                    (2.5..=3.5).contains(&d),
                    "the defect at ({a},{b}) left [2.5,3.5]: {d}"
                );
            }
        }
    }
    // And the cone forces every admissible ratio to be at least 2:
    // iota(b+1) >= g(b) >= 2 iota(b).
    for w in exact.windows(2) {
        assert!(w[1].1 >= 2 * w[0].1, "iota(b+1) >= 2 iota(b) failed");
    }
}
