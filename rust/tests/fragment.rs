//! Stage B of the spread lemma, falsified before it is proved —
//! the minimal fragment, Claim 3.3, and the encoding of Claim 3.4.
//!
//! `docs/roadmap.md` §1 says, under "What the testbed buys here":
//! *"an encoding is a map to run over the exhaustive enumeration in
//! `rust/src/testbed.rs` and check injective. Use it — the cost of
//! finding out a lemma is false after half a session of proof is the
//! main way this campaign goes wrong."* This is that, run before
//! `coq/Fragment.v` was written.
//!
//! Everything is quoted from [Lovett] pp. 12–13, **rendered**
//! (`pdftoppm -png -r 150`, sha256 of the PDF matching
//! `docs/papers/manifest.json`), not from a summary:
//!
//! > **Def 3.2** `M(S,V)` is a minimum-size element of
//! > `{S' \ V : S' ∈ F, S' ⊂ S ∪ V}`.
//! >
//! > 1. `M(S,V) ⊂ S`.
//! > 2. `M(S,V)` is disjoint from `V`.
//! > 3. `M(S,V) = ∅` iff there exists `S' ∈ F` with `S' ⊂ V`.
//! >
//! > **Claim 3.3.** Define `Z = V ∪ M(S,V)` and
//! > `F' = {S' ∈ F : S' ⊂ Z}`. Then: 1. `F'` is not empty.
//! > 2. Any `S' ∈ F'` satisfies `S' \ V = M(S,V)`. In particular
//! > `M(S,V) ⊂ S'`.
//! >
//! > **Claim 3.4** (the encoding). `φ(S,V) = (Z, S', M, S \ M)`.
//! > *"Note that we can decode `(S,V)` given `φ(S,V)` since
//! > `S = M ∪ (S \ M)` and `V = Z \ M`."*
//!
//! Six claims are checked here, exhaustively over small universes:
//!
//! 1. `M(S,V)` is well defined for `S ∈ F` — `S` is always a candidate,
//!    so the candidate list is never empty and the Coq definition needs
//!    no junk default.
//! 2. Observations 1–3, verbatim.
//! 3. Claim 3.3, both parts.
//! 4. **`ψ(φ(S,V)) = (S,V)`** for `ψ(Z,S',M,R) = (M ∪ R, Z \ M)` — the
//!    obligation §1 identifies as *an equation, not a case analysis*.
//! 5. **`S'` is a function of `Z` alone** — Claim 3.4 step 2, which is
//!    what makes that component of the encoding free.
//! 6. **`|Z| = |V| + |M|`**, so the `Z` component ranges over the
//!    layer of size `qN + m` and step 1 of the count is exactly
//!    `Counting.binom_ratio`.

type Mask = u32;

/// Every subset of a `n`-element universe.
fn all_sets(n: u32) -> Vec<Mask> {
    (0..(1u32 << n)).collect()
}

/// The candidate fragments of `(S,V)`: `{S' \ V : S' ∈ F, S' ⊆ S ∪ V}`.
fn candidates(f: &[Mask], s: Mask, v: Mask) -> Vec<Mask> {
    f.iter()
        .filter(|&&sp| sp & !(s | v) == 0)
        .map(|&sp| sp & !v)
        .collect()
}

/// `M(S,V)`: a minimum-size candidate, ties broken by *first in the
/// enumeration*, which is what turns Lovett's "breaking ties
/// arbitrarily" into a function.
fn minimal_fragment(f: &[Mask], s: Mask, v: Mask) -> Option<Mask> {
    candidates(f, s, v)
        .into_iter()
        .reduce(|best, c| if c.count_ones() < best.count_ones() { c } else { best })
}

/// The first member of `F` contained in `Z`, in the family's own order.
fn first_in(f: &[Mask], z: Mask) -> Option<Mask> {
    f.iter().copied().find(|&sp| sp & !z == 0)
}

/// **Exhaustive** family enumeration: every family of at most `k` distinct
/// subsets of an `n`-element universe. Repeats are allowed by Lovett
/// (p. 13, *"it will be convenient to allow families to have repeated
/// sets"*) and change nothing here, so distinct ones suffice.
fn families(n: u32, k: usize) -> Vec<Vec<Mask>> {
    let sets = all_sets(n);
    let mut out: Vec<Vec<Mask>> = Vec::new();
    let mut cur: Vec<Mask> = Vec::new();
    fn rec(
        start: usize,
        k: usize,
        sets: &[Mask],
        cur: &mut Vec<Mask>,
        out: &mut Vec<Vec<Mask>>,
    ) {
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

/// The boxes swept below: (universe size, max family size). Every family
/// of that shape, every member as `S`, every subset as `V`.
const BOXES: [(u32, usize); 4] = [(3, 3), (4, 3), (2, 4), (1, 2)];

/// The exact number of (F, S, V) triples the boxes above contain. Pinned
/// so that a change to BOXES is a visible diff rather than a silent one.
const SWEEP_SIZE: usize = 32_968;

/// Run `body` over every (F, S, V) in every box, returning the count.
fn sweep(mut body: impl FnMut(&[Mask], Mask, Mask)) -> usize {
    let mut instances = 0usize;
    for (n, k) in BOXES {
        for f in families(n, k) {
            for &s in &f {
                for v in all_sets(n) {
                    body(&f, s, v);
                    instances += 1;
                }
            }
        }
    }
    instances
}

// ---------------------------------------------------------------------------
// 1 & 2. Well-definedness, and the three observations
// ---------------------------------------------------------------------------

#[test]
fn the_minimal_fragment_is_defined_and_the_three_observations_hold() {
    let instances = sweep(|f, s, v| {
        // 1. `S` is itself a candidate, so `M(S,V)` exists.
        let m = minimal_fragment(f, s, v)
            .expect("S in F is always a candidate, so M(S,V) exists");
        // Observation 1: M(S,V) ⊆ S
        assert_eq!(m & !s, 0, "Obs 1 fails: S={s:b} V={v:b} M={m:b}");
        // Observation 2: M(S,V) disjoint from V
        assert_eq!(m & v, 0, "Obs 2 fails: S={s:b} V={v:b} M={m:b}");
        // Observation 3: M = ∅ iff some S' ∈ F has S' ⊆ V
        let some_inside_v = f.iter().any(|&sp| sp & !v == 0);
        assert_eq!(m == 0, some_inside_v, "Obs 3 fails: S={s:b} V={v:b} M={m:b}");
    });
    assert_eq!(instances, SWEEP_SIZE, "the sweep changed size");
}

// ---------------------------------------------------------------------------
// 3. Claim 3.3
// ---------------------------------------------------------------------------

#[test]
fn claim_three_three() {
    let instances = sweep(|f, s, v| {
        let m = minimal_fragment(f, s, v).unwrap();
        let z = v | m;
        let fprime: Vec<Mask> = f.iter().copied().filter(|&sp| sp & !z == 0).collect();
        // (1) F' is not empty
        assert!(!fprime.is_empty(), "Claim 3.3(1) fails: S={s:b} V={v:b} Z={z:b}");
        // (2) every S' in F' has S' \ V = M, in particular M ⊆ S'
        for &sp in &fprime {
            assert_eq!(
                sp & !v, m,
                "Claim 3.3(2) fails: S={s:b} V={v:b} S'={sp:b} M={m:b}"
            );
            assert_eq!(m & !sp, 0, "M subset S' fails");
        }
    });
    assert_eq!(instances, SWEEP_SIZE);
}

// ---------------------------------------------------------------------------
// 4. The encoding decodes — the obligation §1 calls an equation
// ---------------------------------------------------------------------------

/// `φ(S,V) = (Z, S', M, S \ M)`.
fn phi(f: &[Mask], s: Mask, v: Mask) -> (Mask, Mask, Mask, Mask) {
    let m = minimal_fragment(f, s, v).unwrap();
    let z = v | m;
    let sp = first_in(f, z).expect("Claim 3.3(1): F' is not empty");
    (z, sp, m, s & !m)
}

/// `ψ(Z, S', M, R) = (M ∪ R, Z \ M)` — Lovett's two identities,
/// `S = M ∪ (S \ M)` and `V = Z \ M`. Note it never reads `S'`.
fn psi(z: Mask, _sp: Mask, m: Mask, r: Mask) -> (Mask, Mask) {
    (m | r, z & !m)
}

#[test]
fn the_encoding_decodes() {
    let instances = sweep(|f, s, v| {
        let (z, sp, m, r) = phi(f, s, v);
        assert_eq!(
            psi(z, sp, m, r),
            (s, v),
            "psi(phi(S,V)) != (S,V) at S={s:b} V={v:b}"
        );
    });
    assert_eq!(instances, SWEEP_SIZE, "the sweep changed size");
}

#[test]
fn the_encoding_is_therefore_injective() {
    // Decodability is what the count needs; injectivity is its corollary.
    // Checked directly here so that the Coq side's route
    // (psi ∘ phi = id  ⟹  injective) is verified end to end.
    for (n, k) in BOXES {
        for f in families(n, k) {
            let mut seen: Vec<((Mask, Mask, Mask, Mask), (Mask, Mask))> = Vec::new();
            for &s in &f {
                for v in all_sets(n) {
                    let code = phi(&f, s, v);
                    if let Some((_, prev)) = seen.iter().find(|(c, _)| *c == code) {
                        assert_eq!(*prev, (s, v), "phi collides: code={code:?}");
                    }
                    seen.push((code, (s, v)));
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// 5 & 6. What makes the count work
// ---------------------------------------------------------------------------

#[test]
fn the_second_component_is_a_function_of_z_alone() {
    // Claim 3.4 step 2: "The set S' is uniquely defined given Z." That is
    // why S' contributes a factor of 1 to the count rather than |F|.
    for (n, k) in BOXES {
        for f in families(n, k) {
            let mut by_z: Vec<(Mask, Mask)> = Vec::new();
            for &s in &f {
                for v in all_sets(n) {
                    let (z, sp, _, _) = phi(&f, s, v);
                    if let Some((_, prev)) = by_z.iter().find(|(zz, _)| *zz == z) {
                        assert_eq!(*prev, sp, "S' is not a function of Z at Z={z:b}");
                    } else {
                        by_z.push((z, sp));
                    }
                }
            }
        }
    }
}

#[test]
fn the_z_component_lives_in_the_layer_of_size_v_plus_m() {
    // |Z| = |V| + |M|, because V and M are disjoint (Obs 2). So the Z
    // component ranges over C(N, qN+m) sets, and step 1 of Claim 3.4's
    // count -- C(N, qN+m) <= q^{-m} C(N, qN) -- is exactly
    // `Counting.binom_ratio` with q = c/d.
    sweep(|f, s, v| {
        let m = minimal_fragment(f, s, v).unwrap();
        let z = v | m;
        assert_eq!(
            z.count_ones(),
            v.count_ones() + m.count_ones(),
            "|Z| = |V| + |M| fails at S={s:b} V={v:b} M={m:b}"
        );
    });
}

#[test]
fn the_fourth_component_lives_in_the_link_of_m() {
    // Claim 3.4 step 5: "Given M = M(S,V), we have M ⊂ S and hence
    // S \ M ∈ F_M." The link is where the k^{-m} saving comes from --
    // the spread hypothesis bounds |F_M|, not |F|.
    sweep(|f, s, v| {
        let m = minimal_fragment(f, s, v).unwrap();
        let link: Vec<Mask> = f
            .iter()
            .copied()
            .filter(|&t| m & !t == 0)
            .map(|t| t & !m)
            .collect();
        assert!(
            link.contains(&(s & !m)),
            "S-minus-M must lie in the link of M: S={s:b} M={m:b}"
        );
        assert!(link.len() <= f.len());
    });
}
