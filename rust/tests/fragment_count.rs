//! Claim 3.4's *count*, falsified before it is proved.
//!
//! `coq/Fragment.v` proves the encoding and its injectivity;
//! `docs/roadmap.md` §31.5 names what is left — the assembly of the four
//! counting steps, and the fibred counting lemma `coq/Counting.v` needs
//! for it. This file checks the assembled bound on small instances, in
//! the order §1 prescribes: testbed first.
//!
//! The bound, from [Lovett] p. 13 rendered, with `|M| = m` fixed:
//!
//! > 1. The number of choices for `Z` is `C(N, qN+m) ≤ C(N,qN) q^{-m}`.
//! > 2. The set `S'` is uniquely defined given `Z`.
//! > 3. Given `S'`, there are at most `C(n,m) ≤ 2^n` options for
//! >    `M = M(S,V) ⊂ S'`.
//! > 4. Given `M`, there are `|F_M| ≤ |F| k^{-m}` choices for `S \ M`
//! >    (here is where we are using the assumption that `F` is
//! >    `k`-spread!)
//!
//! Stated without `q`, which is what the formal version will say — write
//! `j` for `|V|`, and let `B(j,m)` be the pairs `(S,V)` with `S ∈ F`,
//! `|V| = j` and `|M(S,V)| = m`:
//!
//! ```text
//!   |B(j,m)|  <=  C(N, j+m) * C(n, m) * max_{|M| = m} deg M F
//! ```
//!
//! Four claims:
//!
//! 1. **The fibred bound.** Every fibre of `(S,V) ↦ (Z,M)` has at most
//!    `deg M F` elements — this is the lemma `Counting.v` is missing,
//!    checked here before it is written.
//! 2. **The assembled bound** above, over every small family.
//! 3. **Each of the four factors is needed**: dropping any one of them
//!    makes the bound false, with a witness. So none is slack.
//! 4. **The spread step.** With `F` `k`-spread in the fractional sense
//!    (`k^{|T|} · deg T F ≤ |F|`, which is `Spread.Spread`), the fourth
//!    factor is at most `|F| / k^m`, so `k^m · |B(j,m)| ≤ C(N,j+m) ·
//!    C(n,m) · |F|` — the form that stays in `nat`.

type Mask = u32;

fn all_sets(n: u32) -> Vec<Mask> {
    (0..(1u32 << n)).collect()
}

fn binom(n: usize, j: usize) -> u128 {
    if j > n {
        return 0;
    }
    let j = j.min(n - j);
    let mut acc: u128 = 1;
    for i in 0..j {
        acc = acc * ((n - i) as u128);
        acc /= (i + 1) as u128;
    }
    acc
}

fn minimal_fragment(f: &[Mask], s: Mask, v: Mask) -> Mask {
    f.iter()
        .filter(|&&sp| sp & !(s | v) == 0)
        .map(|&sp| sp & !v)
        .reduce(|best, c| if c.count_ones() < best.count_ones() { c } else { best })
        .expect("S in F is always a candidate")
}

/// `deg M F` = the size of the link of `M` = the number of members of
/// `F` containing `M`. (`Spread.length_link`.)
fn deg(f: &[Mask], m: Mask) -> usize {
    f.iter().filter(|&&t| m & !t == 0).count()
}

/// Every family of at most `k` distinct subsets of an `n`-set.
fn families(n: u32, k: usize) -> Vec<Vec<Mask>> {
    let sets = all_sets(n);
    let mut out = Vec::new();
    let mut cur = Vec::new();
    fn rec(start: usize, k: usize, sets: &[Mask], cur: &mut Vec<Mask>, out: &mut Vec<Vec<Mask>>) {
        if !cur.is_empty() {
            out.push(cur.clone());
        }
        if cur.len() == k {
            return;
        }
        for i in start..sets.len() {
            cur.push(sets[i]);
            rec(i + 1, k, sets, cur, out);
            cur.pop();
        }
    }
    rec(0, k, &sets, &mut cur, &mut out);
    out
}

/// The largest member size in `F` — Lovett's `n` ("sets of size at
/// most `n`").
fn uniformity(f: &[Mask]) -> usize {
    f.iter().map(|s| s.count_ones() as usize).max().unwrap_or(0)
}

const BOXES: [(u32, usize); 2] = [(4, 3), (3, 4)];

// ---------------------------------------------------------------------------
// 1. The fibred bound — the lemma Counting.v is missing
// ---------------------------------------------------------------------------

#[test]
fn every_fibre_of_z_and_m_is_at_most_the_degree_of_m() {
    // (S,V) |-> (Z,M) with Z = V u M. Given (Z,M): V = Z \ M is
    // determined, and S = M u (S\M) with S\M in the link of M. So the
    // fibre injects into the link, and |fibre| <= deg M F.
    let mut checked = 0usize;
    for (n, kf) in BOXES {
        for f in families(n, kf) {
            let mut fibres: Vec<((Mask, Mask), usize)> = Vec::new();
            for &s in &f {
                for v in all_sets(n) {
                    let m = minimal_fragment(&f, s, v);
                    let z = v | m;
                    match fibres.iter_mut().find(|(key, _)| *key == (z, m)) {
                        Some((_, c)) => *c += 1,
                        None => fibres.push(((z, m), 1)),
                    }
                }
            }
            for ((_, m), c) in &fibres {
                assert!(
                    *c <= deg(&f, *m),
                    "fibre at M={m:b} has {c} elements, deg M F = {}",
                    deg(&f, *m)
                );
                checked += 1;
            }
        }
    }
    assert!(checked > 5_000, "only {checked} fibres exercised");
}

// ---------------------------------------------------------------------------
// 2. The assembled bound
// ---------------------------------------------------------------------------

/// `|B(j,m)|` — pairs `(S,V)` with `S ∈ F`, `|V| = j`, `|M(S,V)| = m`.
fn bad_count(f: &[Mask], n: u32, j: u32, m: u32) -> u128 {
    let mut c = 0u128;
    for &s in f {
        for v in all_sets(n) {
            if v.count_ones() == j && minimal_fragment(f, s, v).count_ones() == m {
                c += 1;
            }
        }
    }
    c
}

/// `max_{|M| = m} deg M F`, the fourth factor.
fn max_deg_at_size(f: &[Mask], n: u32, m: u32) -> u128 {
    all_sets(n)
        .into_iter()
        .filter(|t| t.count_ones() == m)
        .map(|t| deg(f, t) as u128)
        .max()
        .unwrap_or(0)
}

#[test]
fn the_assembled_bound_of_claim_three_four() {
    let mut nontrivial = 0usize;
    for (n, kf) in BOXES {
        for f in families(n, kf) {
            let unif = uniformity(&f);
            for j in 0..=n {
                for m in 0..=n {
                    let lhs = bad_count(&f, n, j, m);
                    let rhs = binom(n as usize, (j + m) as usize)
                        * binom(unif, m as usize)
                        * max_deg_at_size(&f, n, m);
                    assert!(
                        lhs <= rhs,
                        "Claim 3.4's count fails: n={n} F={f:?} j={j} m={m}: \
                         {lhs} > {rhs}"
                    );
                    if lhs > 0 {
                        nontrivial += 1;
                    }
                }
            }
        }
    }
    assert!(nontrivial > 5_000, "only {nontrivial} nonempty B(j,m) seen");
}

// ---------------------------------------------------------------------------
// 3. None of the four factors is slack
// ---------------------------------------------------------------------------

#[test]
fn each_factor_of_the_bound_is_needed() {
    // Dropping any one factor makes the bound false somewhere. Recorded
    // as counts so that a future weakening of the Coq statement shows up
    // as a changed number rather than as a still-passing test.
    let (mut no_z, mut no_m, mut no_deg) = (0usize, 0usize, 0usize);
    for (n, kf) in BOXES {
        for f in families(n, kf) {
            let unif = uniformity(&f);
            for j in 0..=n {
                for m in 0..=n {
                    let lhs = bad_count(&f, n, j, m);
                    let bz = binom(n as usize, (j + m) as usize);
                    let bm = binom(unif, m as usize);
                    let bd = max_deg_at_size(&f, n, m);
                    if lhs > bm * bd {
                        no_z += 1;
                    }
                    if lhs > bz * bd {
                        no_m += 1;
                    }
                    if lhs > bz * bm {
                        no_deg += 1;
                    }
                }
            }
        }
    }
    assert!(no_z > 0, "the C(N,j+m) factor was never needed");
    assert!(no_m > 0, "the C(n,m) factor was never needed");
    assert!(no_deg > 0, "the deg M F factor was never needed");
}

// ---------------------------------------------------------------------------
// 4. The spread step, in the cleared-denominator form
// ---------------------------------------------------------------------------

/// `Spread.Spread F k` : `k^|T| * deg T F <= |F|` for every `T`.
fn is_spread(f: &[Mask], n: u32, k: u128) -> bool {
    all_sets(n).into_iter().all(|t| {
        k.pow(t.count_ones()) * (deg(f, t) as u128) <= f.len() as u128
    })
}

#[test]
fn the_spread_hypothesis_gives_the_fourth_factor() {
    // k^m * |B(j,m)| <= C(N,j+m) * C(n,m) * |F| whenever F is k-spread.
    // This is the form that stays in nat: no q^{-m}, no k^{-m}.
    let mut witnessed = 0usize;
    for (n, kf) in BOXES {
        for f in families(n, kf) {
            let unif = uniformity(&f);
            for k in 1..=3u128 {
                if !is_spread(&f, n, k) {
                    continue;
                }
                for j in 0..=n {
                    for m in 0..=n {
                        let lhs = k.pow(m) * bad_count(&f, n, j, m);
                        let rhs = binom(n as usize, (j + m) as usize)
                            * binom(unif, m as usize)
                            * (f.len() as u128);
                        assert!(
                            lhs <= rhs,
                            "spread form fails: n={n} k={k} F={f:?} j={j} m={m}: \
                             {lhs} > {rhs}"
                        );
                        witnessed += 1;
                    }
                }
            }
        }
    }
    assert!(witnessed > 5_000, "only {witnessed} spread instances seen");
}
