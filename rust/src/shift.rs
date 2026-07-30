//! Compression, and why it is the wrong tool here.
//!
//! The `(i,j)`-shift is *the* instrument of extremal set theory: it is how
//! Erdős–Ko–Rado, Hilton–Milner and most of Frankl's work are proved. For
//! `i < j` it replaces `A` by `(A \ {j}) ∪ {i}` whenever `j ∈ A`, `i ∉ A`
//! and the image is not already present. It preserves `|F|`, preserves
//! uniformity, preserves *intersecting*-ness, and terminates — so any
//! family can be pushed to a **left-compressed** one of the same size,
//! supported on an initial segment of the ground set, which is where the
//! structure comes from.
//!
//! This module asks whether it survives contact with sunflower-freeness.
//! It does not, and the way it fails is sharp enough to be the point:
//!
//! * **It does not preserve 3-sunflower-freeness** — `shift_family`
//!   applied to a five-cycle produces a star.
//! * **The maximum is not attained by a compressed family either**, which
//!   is the weaker statement one would actually want. A left-compressed
//!   3-sunflower-free `m`-uniform family has at most `m + 1` members
//!   (`max_left_compressed`), against `g(m) ≥ 2·ι(m)`, which is
//!   exponential. Compression does not lose a constant here; it collapses
//!   the problem from exponential to linear.
//! * **What it preserves is exactly the empty core.** Sunflower-freeness
//!   is "every link has matching number `≤ 2`"
//!   (`LinkCharacterisation.sunflower_iff_link_matching`). Shifting
//!   preserves that at the empty link — the standard fact that it does
//!   not increase the matching number — and destroys it at every other
//!   core. Intersecting-ness is the *single* empty-link condition
//!   `ν ≤ 1`, which is why the tool works for Erdős–Ko–Rado and cannot
//!   work here.
//!
//! Sets are bitmasks, so `ground ≤ 32`.

use crate::spread::{matching_number, Mask};

/// The `(i,j)`-shift of one member, ignoring the family: replace `j` by
/// `i` when `j` is present and `i` is not. Returns `a` unchanged
/// otherwise.
#[inline]
pub fn shift_set(a: Mask, i: u32, j: u32) -> Mask {
    if a >> j & 1 == 1 && a >> i & 1 == 0 {
        (a & !(1 << j)) | (1 << i)
    } else {
        a
    }
}

/// The `(i,j)`-shift of a family: `S_ij(A)` is taken only when the image
/// is not already in `F`, which is what makes the map injective and the
/// size invariant.
///
/// Order of the output follows the input, so the shift of a family is
/// comparable member-by-member with the family it came from.
pub fn shift_family(f: &[Mask], i: u32, j: u32) -> Vec<Mask> {
    f.iter()
        .map(|&a| {
            let b = shift_set(a, i, j);
            if b != a && f.contains(&b) {
                a
            } else {
                b
            }
        })
        .collect()
}

/// Is `f` a fixed point of every `(i,j)`-shift with `i < j < ground`?
///
/// Equivalently — and this is `adjacent_shifts_generate` in the test
/// suite — a fixed point of every *adjacent* shift `(j-1, j)`, and
/// equivalently a down-set in the dominance order on `m`-sets.
pub fn is_left_compressed(f: &[Mask], ground: u32) -> bool {
    for &a in f {
        for j in 0..ground {
            if a >> j & 1 == 0 {
                continue;
            }
            for i in 0..j {
                if a >> i & 1 == 1 {
                    continue;
                }
                let b = (a & !(1 << j)) | (1 << i);
                if !f.contains(&b) {
                    return false;
                }
            }
        }
    }
    true
}

/// The same test using only adjacent shifts `(j-1, j)`.
pub fn is_left_compressed_adjacent(f: &[Mask], ground: u32) -> bool {
    for &a in f {
        for j in 1..ground {
            if a >> j & 1 == 1 && a >> (j - 1) & 1 == 0 {
                let b = (a & !(1 << j)) | (1 << (j - 1));
                if !f.contains(&b) {
                    return false;
                }
            }
        }
    }
    true
}

/// Dominance: `b ≤ a` when the sorted elements of `b` are pointwise at
/// most those of `a`. Defined for equal-size sets.
pub fn dominates(a: Mask, b: Mask) -> bool {
    if a.count_ones() != b.count_ones() {
        return false;
    }
    let (mut ea, mut eb) = (elements(a), elements(b));
    ea.sort_unstable();
    eb.sort_unstable();
    ea.iter().zip(eb.iter()).all(|(x, y)| y <= x)
}

/// Is `f` a down-set in the dominance order?
pub fn is_dominance_downset(f: &[Mask], ground: u32, m: u32) -> bool {
    for &a in f {
        for b in subsets_of_size(ground, m) {
            if dominates(a, b) && !f.contains(&b) {
                return false;
            }
        }
    }
    true
}

/// The compression potential: `Σ_{A ∈ F} Σ_{x ∈ A} x`. Every shift that
/// moves anything strictly decreases it, which is why the process
/// terminates.
pub fn potential(f: &[Mask]) -> u32 {
    f.iter().map(|&a| elements(a).into_iter().sum::<u32>()).sum()
}

/// Shift repeatedly until nothing moves. Returns the compressed family
/// (sorted) and the number of shifts applied.
///
/// The result is left-compressed and has the same size as the input:
/// each individual shift is injective. `shift_closure_is_compressed` in
/// the test suite checks both on every family it enumerates.
pub fn shift_closure(f: &[Mask], ground: u32) -> (Vec<Mask>, usize) {
    let mut cur: Vec<Mask> = f.to_vec();
    let mut steps = 0usize;
    loop {
        let mut moved = false;
        'outer: for j in 0..ground {
            for i in 0..j {
                let next = shift_family(&cur, i, j);
                if next != cur {
                    cur = next;
                    steps += 1;
                    moved = true;
                    break 'outer;
                }
            }
        }
        if !moved {
            break;
        }
    }
    cur.sort_unstable();
    (cur, steps)
}

/// A shift that a sunflower-free family does not survive, if there is
/// one: the pair `(i,j)` and the family it produces.
pub fn breaking_shift(f: &[Mask], ground: u32) -> Option<(u32, u32, Vec<Mask>)> {
    for j in 0..ground {
        for i in 0..j {
            let next = shift_family(f, i, j);
            if next != f && !is_sunflower_free(&next) {
                return Some((i, j, next));
            }
        }
    }
    None
}

// ---------------------------------------------------------------------
// The extremal question: how large can a compressed family be?
// ---------------------------------------------------------------------

/// The largest left-compressed 3-sunflower-free `m`-uniform family on
/// `ground` points, and a witness attaining it.
///
/// Exhaustive. The search enumerates down-sets rather than families: the
/// `m`-sets are visited in increasing order of `Σ x`, which is a linear
/// extension of dominance, so a set may be taken only when all of its
/// lower covers — the adjacent shifts `(x-1, x)` of it — have already
/// been taken. Excluding a set therefore forces out everything above it,
/// and the tree stays small.
///
/// `intersecting` additionally demands that every two members meet, so
/// the same routine answers the question for `ι`.
///
/// Returns `(size, witness, nodes)`.
pub fn max_left_compressed(ground: u32, m: u32, intersecting: bool) -> (usize, Vec<Mask>, u64) {
    let mut sets = subsets_of_size(ground, m);
    sets.sort_by_key(|&a| (elements(a).into_iter().sum::<u32>(), a));
    let index: std::collections::HashMap<Mask, usize> =
        sets.iter().enumerate().map(|(n, &a)| (a, n)).collect();

    // Lower covers: replace some x ∈ A by x-1 when x-1 ∉ A.
    let covers: Vec<Vec<usize>> = sets
        .iter()
        .map(|&a| {
            elements(a)
                .into_iter()
                .filter(|&x| x >= 1 && a >> (x - 1) & 1 == 0)
                .map(|x| index[&((a & !(1 << x)) | (1 << (x - 1)))])
                .collect()
        })
        .collect();

    struct S {
        best: usize,
        witness: Vec<Mask>,
        nodes: u64,
    }
    fn rec(
        idx: usize,
        sets: &[Mask],
        covers: &[Vec<usize>],
        taken: &mut Vec<bool>,
        cur: &mut Vec<Mask>,
        intersecting: bool,
        s: &mut S,
    ) {
        s.nodes += 1;
        if cur.len() > s.best {
            s.best = cur.len();
            s.witness = cur.clone();
        }
        if idx == sets.len() {
            return;
        }
        let x = sets[idx];
        let ok = covers[idx].iter().all(|&c| taken[c])
            && !creates_sunflower(cur, x)
            && (!intersecting || cur.iter().all(|&a| a & x != 0));
        if ok {
            taken[idx] = true;
            cur.push(x);
            rec(idx + 1, sets, covers, taken, cur, intersecting, s);
            cur.pop();
            taken[idx] = false;
        }
        rec(idx + 1, sets, covers, taken, cur, intersecting, s);
    }

    let mut s = S {
        best: 0,
        witness: Vec::new(),
        nodes: 0,
    };
    let mut taken = vec![false; sets.len()];
    let mut cur = Vec::new();
    rec(0, &sets, &covers, &mut taken, &mut cur, intersecting, &mut s);
    (s.best, s.witness, s.nodes)
}

/// All `m`-subsets of an `(m+1)`-set: the family the bound above is
/// attained by. Left-compressed, sunflower-free, intersecting for
/// `m ≥ 2`, and of size `m + 1`.
pub fn initial_segment_witness(m: u32) -> Vec<Mask> {
    let full: Mask = (1 << (m + 1)) - 1;
    (0..=m).map(|x| full & !(1 << x)).collect()
}

// ---------------------------------------------------------------------
// Small helpers, kept local so this module can be read on its own.
// ---------------------------------------------------------------------

pub fn elements(a: Mask) -> Vec<u32> {
    (0..32).filter(|x| a >> x & 1 == 1).collect()
}

pub fn subsets_of_size(ground: u32, m: u32) -> Vec<Mask> {
    (0u32..(1 << ground)).filter(|x| x.count_ones() == m).collect()
}

#[inline]
pub fn is_sunflower(a: Mask, b: Mask, c: Mask) -> bool {
    let ab = a & b;
    ab == (a & c) && ab == (b & c)
}

#[inline]
pub fn creates_sunflower(cur: &[Mask], x: Mask) -> bool {
    for i in 0..cur.len() {
        for j in (i + 1)..cur.len() {
            if is_sunflower(cur[i], cur[j], x) {
                return true;
            }
        }
    }
    false
}

/// Distinct and containing no 3-sunflower.
pub fn is_sunflower_free(f: &[Mask]) -> bool {
    for i in 0..f.len() {
        for j in (i + 1)..f.len() {
            if f[i] == f[j] {
                return false;
            }
            for l in (j + 1)..f.len() {
                if is_sunflower(f[i], f[j], f[l]) {
                    return false;
                }
            }
        }
    }
    true
}

pub fn is_intersecting(f: &[Mask]) -> bool {
    for i in 0..f.len() {
        for j in (i + 1)..f.len() {
            if f[i] & f[j] == 0 {
                return false;
            }
        }
    }
    true
}

/// The link `{A \ Y : Y ⊆ A ∈ F}`, deduplicated.
pub fn link(y: Mask, f: &[Mask]) -> Vec<Mask> {
    let mut out: Vec<Mask> = f
        .iter()
        .filter(|&&a| a & y == y)
        .map(|&a| a & !y)
        .collect();
    out.sort_unstable();
    out.dedup();
    out
}

/// The largest matching number over all links: `2` exactly when `F` is
/// sunflower-free, by the link characterisation. Ranges over subsets of
/// `ground`.
pub fn max_link_matching(f: &[Mask], ground: u32) -> (usize, Mask) {
    let mut best = 0;
    let mut arg = 0;
    for y in 0u32..(1 << ground) {
        let l = link(y, f);
        if l.is_empty() {
            continue;
        }
        let nu = matching_number(&l);
        if nu > best {
            best = nu;
            arg = y;
        }
    }
    (best, arg)
}

// ---------------------------------------------------------------------
// The same question at every sunflower size
// ---------------------------------------------------------------------

/// Are the `k` sets at `idx` a `k`-sunflower? All pairwise intersections
/// equal.
pub fn is_k_sunflower_masks(sets: &[Mask]) -> bool {
    if sets.len() < 2 {
        return false;
    }
    let core = sets[0] & sets[1];
    for i in 0..sets.len() {
        for j in (i + 1)..sets.len() {
            if sets[i] & sets[j] != core {
                return false;
            }
        }
    }
    true
}

/// Would adding `x` to `cur` complete a `k`-sunflower?
pub fn creates_k_sunflower(cur: &[Mask], x: Mask, k: usize) -> bool {
    if cur.len() + 1 < k {
        return false;
    }
    let mut idx: Vec<usize> = (0..(k - 1)).collect();
    let n = cur.len();
    loop {
        let mut petals: Vec<Mask> = idx.iter().map(|&i| cur[i]).collect();
        petals.push(x);
        if is_k_sunflower_masks(&petals) {
            return true;
        }
        let mut p = k - 1;
        loop {
            if p == 0 {
                return false;
            }
            p -= 1;
            if idx[p] < n - (k - 1 - p) {
                idx[p] += 1;
                for q in (p + 1)..(k - 1) {
                    idx[q] = idx[q - 1] + 1;
                }
                break;
            }
        }
    }
}

/// The largest left-compressed `k`-sunflower-free `m`-uniform family on
/// `ground` points, and a witness. Same down-set enumeration as
/// `max_left_compressed`, which is the `k = 3` case.
pub fn max_left_compressed_k(ground: u32, m: u32, k: usize) -> (usize, Vec<Mask>, u64) {
    let mut sets = subsets_of_size(ground, m);
    sets.sort_by_key(|&a| (elements(a).into_iter().sum::<u32>(), a));
    let index: std::collections::HashMap<Mask, usize> =
        sets.iter().enumerate().map(|(n, &a)| (a, n)).collect();
    let covers: Vec<Vec<usize>> = sets
        .iter()
        .map(|&a| {
            elements(a)
                .into_iter()
                .filter(|&x| x >= 1 && a >> (x - 1) & 1 == 0)
                .map(|x| index[&((a & !(1 << x)) | (1 << (x - 1)))])
                .collect()
        })
        .collect();

    struct S {
        best: usize,
        witness: Vec<Mask>,
        nodes: u64,
    }
    fn rec(
        idx: usize,
        sets: &[Mask],
        covers: &[Vec<usize>],
        taken: &mut Vec<bool>,
        cur: &mut Vec<Mask>,
        k: usize,
        s: &mut S,
    ) {
        s.nodes += 1;
        if cur.len() > s.best {
            s.best = cur.len();
            s.witness = cur.clone();
        }
        if idx == sets.len() {
            return;
        }
        let x = sets[idx];
        if covers[idx].iter().all(|&c| taken[c]) && !creates_k_sunflower(cur, x, k) {
            taken[idx] = true;
            cur.push(x);
            rec(idx + 1, sets, covers, taken, cur, k, s);
            cur.pop();
            taken[idx] = false;
        }
        rec(idx + 1, sets, covers, taken, cur, k, s);
    }

    let mut s = S { best: 0, witness: Vec::new(), nodes: 0 };
    let mut taken = vec![false; sets.len()];
    let mut cur = Vec::new();
    rec(0, &sets, &covers, &mut taken, &mut cur, k, &mut s);
    (s.best, s.witness, s.nodes)
}

/// All `m`-subsets of an `(m + k - 2)`-set: the conjectured extremal
/// left-compressed `k`-sunflower-free family, of size `C(m+k-2, m)`.
pub fn initial_segment_witness_k(m: u32, k: usize) -> Vec<Mask> {
    let g = m + (k as u32) - 2;
    subsets_of_size(g, m)
}
