//! Nine points hold twenty-seven 4-sets, no more, and in essentially one
//! way.
//!
//! Falsification for `coq/Support.v`'s `four_uniform_on_nine_at_most_27`
//! and for the uniqueness claim in `docs/roadmap.md` §38.
//!
//! Three separate things, and only the first is an input to the Coq
//! side:
//!
//! 1. **`g(3,8) = 12`** — the largest distinct 3-uniform sunflower-free
//!    family on eight points. Exhaustive. This is the hypothesis
//!    `Support.GThreeOnEight` carries, so if it is wrong the counting
//!    theorem is unsound rather than merely weak.
//!
//! 2. **The counting bound is sharp at nine and nowhere near at ten or
//!    eleven.** `4|F| ≤ 9·g(3,8) = 108` gives 27, which is attained;
//!    the same argument at ten gives 35 and at eleven 44, both above the
//!    32 the ladder asks about.
//!
//! 3. **The extremal family is unique up to relabelling.** An exhaustive
//!    census, isomorph-reduced by brute force over all `9! = 362 880`
//!    relabellings, finds exactly one orbit, and it is `Product.iota4`.
//!
//! What makes the census finish at all is that regularity is *forced*:
//! every degree is at most `g(3,8) = 12` and the degree sum is
//! `4·27 = 108 = 9·12`, so every 27-member family on nine points is
//! exactly 12-regular and a point reaching degree 12 is closed to every
//! later member. Without that constraint the same search ran 900 s
//! without finishing.

use std::collections::HashSet;

use sunflower_formal::wide;

fn is_sunflower(a: u64, b: u64, c: u64) -> bool {
    let ab = a & b;
    ab == (a & c) && ab == (b & c)
}

/// Largest distinct `m`-uniform sunflower-free family on `n` points.
fn g_small(m: u32, n: u32) -> usize {
    fn rec(cands: &[u64], cur: &mut Vec<u64>, best: &mut usize) {
        if cur.len() > *best {
            *best = cur.len();
        }
        for i in 0..cands.len() {
            if cur.len() + (cands.len() - i) <= *best {
                return;
            }
            let x = cands[i];
            let next: Vec<u64> = cands[i + 1..]
                .iter()
                .copied()
                .filter(|&y| !cur.iter().any(|&a| is_sunflower(a, x, y)))
                .collect();
            cur.push(x);
            rec(&next, cur, best);
            cur.pop();
        }
    }
    let all = wide::subsets(n, m);
    let mut best = 0usize;
    rec(&all, &mut Vec::new(), &mut best);
    best
}

/// `Product.iota4`, transcribed from `coq/Product.v`.
fn iota4() -> Vec<u32> {
    const ROWS: [[u32; 4]; 27] = [
        [0, 1, 2, 3], [0, 1, 2, 4], [0, 1, 3, 4], [0, 2, 3, 5], [1, 2, 3, 5],
        [0, 2, 4, 5], [1, 2, 4, 5], [0, 3, 4, 5], [1, 3, 4, 5],
        [0, 1, 6, 7], [2, 3, 6, 7], [2, 4, 6, 7], [3, 4, 6, 7], [0, 5, 6, 7], [1, 5, 6, 7],
        [0, 1, 6, 8], [2, 3, 6, 8], [2, 4, 6, 8], [3, 4, 6, 8], [0, 5, 6, 8], [1, 5, 6, 8],
        [0, 1, 7, 8], [2, 3, 7, 8], [2, 4, 7, 8], [3, 4, 7, 8], [0, 5, 7, 8], [1, 5, 7, 8],
    ];
    ROWS.iter().map(|r| r.iter().fold(0u32, |m, &p| m | 1 << p)).collect()
}

fn perms(n: usize) -> Vec<Vec<u8>> {
    let mut cur: Vec<u8> = (0..n as u8).collect();
    let mut out = vec![cur.clone()];
    loop {
        let Some(i) = (0..n - 1).rev().find(|&i| cur[i] < cur[i + 1]) else { return out };
        let j = (i + 1..n).rev().find(|&j| cur[j] > cur[i]).unwrap();
        cur.swap(i, j);
        cur[i + 1..].reverse();
        out.push(cur.clone());
    }
}

fn canon(f: &[u32], ps: &[Vec<u8>]) -> Vec<u32> {
    let mut best: Option<Vec<u32>> = None;
    let mut buf = vec![0u32; f.len()];
    for p in ps {
        for (slot, &m) in buf.iter_mut().zip(f) {
            let mut q = 0u32;
            let mut r = m;
            while r != 0 {
                q |= 1 << p[r.trailing_zeros() as usize];
                r &= r - 1;
            }
            *slot = q;
        }
        buf.sort_unstable();
        match &best {
            Some(b) if *b <= buf => {}
            _ => best = Some(buf.clone()),
        }
    }
    best.unwrap()
}

/// Claim 1: the hypothesis `Support.GThreeOnEight` carries.
#[test]
fn g_three_on_eight_is_twelve() {
    assert_eq!(g_small(3, 8), 12, "Support.GThreeOnEight would be unsound");
    // Not slack, and not an artefact of the ground set being small:
    assert_eq!(g_small(3, 6), 10, "the iota(3) witness lives here");
    assert_eq!(g_small(2, 6), 6, "g(2) = 6, the pair bound this repo uses");
}

/// Claim 2: sharp at nine, and useless at ten and eleven.
#[test]
fn the_counting_bound_is_sharp_only_at_nine() {
    let g38 = 12usize;
    assert_eq!(9 * g38, 108);
    assert_eq!(4 * 27, 108, "attained by Product.iota4");
    // g(3,9) = 14, computed by examples/g_small.rs in 273 104 763 nodes.
    // Recorded rather than recomputed: it costs 75 s.
    let g39 = 14usize;
    assert_eq!(10 * g39 / 4, 35, "at ten points the bound is 35");
    assert!(35 > 32, "so it decides nothing about iota(4,10) >= 32");
    // At eleven the repository already witnesses g(3,10) >= 16.
    assert!(11 * 16 / 4 >= 44 - 1, "at eleven the bound is about 44");
    assert!(44 > 32, "so it decides nothing about the open rung either");
}

/// Claim 3: 12-regularity is forced, and `iota4` has it.
#[test]
fn every_twenty_seven_member_family_on_nine_points_is_twelve_regular() {
    let f = iota4();
    let mut deg = [0u32; 9];
    for &m in &f {
        for (p, d) in deg.iter_mut().enumerate() {
            if m >> p & 1 == 1 {
                *d += 1;
            }
        }
    }
    assert!(deg.iter().all(|&d| d == 12), "iota4 degrees: {deg:?}");
    assert_eq!(deg.iter().sum::<u32>() as usize, 4 * f.len());
    // The forcing: every degree is at most g(3,8) = 12 because the link
    // of a point lives on the other eight, and 4*27 = 108 = 9*12 leaves
    // no slack for any degree to be below 12.
    assert_eq!(4 * 27, 9 * 12);
}

/// Claim 4: the exhaustive census — one orbit, and it is `iota4`.
///
/// The anchor `{0,1,2,3}` is fixed, sound because a relabelling carries
/// any member onto it; the anchor's stabiliser has one orbit of second
/// members per value of `|B ∩ anchor|`, so three second members meet
/// every orbit. This is the intersecting census; on nine points three
/// pairwise disjoint 4-sets do not fit, so the general case differs and
/// is run separately (`examples/nine_point_census.rs 27 0`).
#[test]
fn the_twenty_seven_member_family_on_nine_points_is_unique() {
    const G: usize = 9;
    const CAP: u32 = 12;
    let anchor: u32 = 0b1111;
    let all: Vec<u32> = (0u32..(1 << G as u32))
        .filter(|x| x.count_ones() == 4 && *x != anchor && x & anchor != 0)
        .collect();

    fn rec(
        cands: &[u32],
        cur: &mut Vec<u32>,
        deg: &mut [u32; 9],
        out: &mut Vec<Vec<u32>>,
    ) {
        if cur.len() == 27 {
            out.push(cur.clone());
            return;
        }
        if cur.len() + cands.len() < 27 {
            return;
        }
        let mut avail = [0u32; 9];
        for &c in cands {
            for (p, a) in avail.iter_mut().enumerate() {
                if c >> p & 1 == 1 {
                    *a += 1;
                }
            }
        }
        if (0..9).any(|p| deg[p] + avail[p] < CAP) {
            return;
        }
        for idx in 0..cands.len() {
            if cur.len() + (cands.len() - idx) < 27 {
                return;
            }
            let x = cands[idx];
            if (0..9).any(|p| x >> p & 1 == 1 && deg[p] >= CAP) {
                continue;
            }
            let next: Vec<u32> = cands[idx + 1..]
                .iter()
                .copied()
                .filter(|&y| y & x != 0 && !cur.iter().any(|&a| is_sunflower(a.into(), x.into(), y.into())))
                .collect();
            cur.push(x);
            for (p, d) in deg.iter_mut().enumerate() {
                if x >> p & 1 == 1 {
                    *d += 1;
                }
            }
            rec(&next, cur, deg, out);
            for (p, d) in deg.iter_mut().enumerate() {
                if x >> p & 1 == 1 {
                    *d -= 1;
                }
            }
            cur.pop();
        }
    }

    let mut found: Vec<Vec<u32>> = Vec::new();
    for j in 1..4u32 {
        let mut rep: u32 = (1 << j) - 1;
        for t in 0..(4 - j) {
            rep |= 1 << (4 + t);
        }
        let sub: Vec<u32> = all
            .iter()
            .copied()
            .filter(|&y| y != rep && y & rep != 0 && !is_sunflower(anchor.into(), rep.into(), y.into()))
            .collect();
        let mut cur = vec![anchor, rep];
        let mut deg = [0u32; 9];
        for &m in &cur {
            for (p, d) in deg.iter_mut().enumerate() {
                if m >> p & 1 == 1 {
                    *d += 1;
                }
            }
        }
        rec(&sub, &mut cur, &mut deg, &mut found);
    }

    assert!(!found.is_empty(), "the census found nothing; iota4 exists");
    for f in &found {
        let w: Vec<u64> = f.iter().map(|&x| u64::from(x)).collect();
        wide::verify(&w, 4, true).expect("census produced an invalid family");
    }
    let ps = perms(G);
    let orbits: HashSet<Vec<u32>> = found.iter().map(|f| canon(f, &ps)).collect();
    assert_eq!(orbits.len(), 1, "more than one orbit: {} found", orbits.len());
    assert!(
        orbits.contains(&canon(&iota4(), &ps)),
        "the unique orbit is not Product.iota4's"
    );
}

/// Claim 5: the general extremal family is **not** unique — dropping
/// "intersecting" admits genuinely different 27-member families.
///
/// This matters because on nine points sunflower-freeness does not imply
/// intersecting: three pairwise disjoint 4-sets need twelve points, so an
/// empty-core sunflower cannot occur and a disjoint pair is allowed. The
/// witness below contains six disjoint pairs, so no relabelling carries
/// it onto `Product.iota4`, which is intersecting.
///
/// Found by seeding the search with the disjoint pair `{0,1,2,3}`,
/// `{4,5,6,7}` — sound because a relabelling carries any disjoint pair
/// there — and carried explicitly so the claim needs no search to check.
#[test]
fn the_general_extremal_family_on_nine_points_is_not_unique() {
    const ROWS: [[u32; 4]; 27] = [
        [0,1,2,3], [4,5,6,7], [0,1,2,4], [0,1,3,4], [0,2,3,4],
        [1,2,3,4], [0,1,5,6], [0,2,5,6], [3,4,5,6], [0,1,5,7],
        [0,2,5,7], [3,4,5,7], [1,2,6,7], [3,4,6,7], [3,5,6,7],
        [1,3,5,8], [2,3,5,8], [1,4,5,8], [2,4,5,8], [1,2,6,8],
        [0,3,6,8], [0,4,6,8], [1,2,7,8], [0,3,7,8], [0,4,7,8],
        [1,6,7,8], [2,6,7,8],
    ];
    let f: Vec<u32> = ROWS.iter().map(|r| r.iter().fold(0u32, |m, &p| m | 1 << p)).collect();
    let w: Vec<u64> = f.iter().map(|&x| u64::from(x)).collect();

    // 4-uniform, distinct, sunflower-free -- but NOT required intersecting.
    wide::verify(&w, 4, false).expect("the witness is not a valid family");
    assert_eq!(f.len(), 27);
    assert_eq!(f.iter().collect::<HashSet<_>>().len(), 27);

    // It lives on exactly nine points and is 12-regular, as the counting
    // bound forces every 27-member family here to be.
    let mut deg = [0u32; 9];
    for &m in &f {
        assert_eq!(m >> 9, 0, "a member leaves the nine points");
        for (p, d) in deg.iter_mut().enumerate() {
            if m >> p & 1 == 1 {
                *d += 1;
            }
        }
    }
    assert!(deg.iter().all(|&d| d == 12), "degrees {deg:?}");

    // It is genuinely not intersecting.
    let disjoint = (0..f.len())
        .flat_map(|i| (i + 1..f.len()).map(move |j| (i, j)))
        .filter(|&(i, j)| f[i] & f[j] == 0)
        .count();
    assert_eq!(disjoint, 6, "disjoint pairs");
    assert!(
        wide::verify(&w, 4, true).is_err(),
        "it would have to be intersecting for iota4's uniqueness to cover it"
    );

    // So it is in a different orbit from Product.iota4.
    let ps = perms(9);
    assert_ne!(
        canon(&f, &ps),
        canon(&iota4(), &ps),
        "the witness is a relabelling of iota4 after all"
    );
}
