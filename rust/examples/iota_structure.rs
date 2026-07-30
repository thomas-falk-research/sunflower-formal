//! Dump the extremal `iota` families and everything computable about them.
//!
//! `docs/roadmap.md` §10 asks for "identify the object" and the repository
//! has only ever recorded sizes. This prints, for every extremal witness:
//! the family, its automorphism group order and point orbits, its degree
//! and pair-degree sequences, whether it is a 2-design, the per-core link
//! matching numbers of
//! `LinkCharacterisation.sunflower_iff_link_matching`, the shadow sizes,
//! the VC dimension, and the anchor decomposition.
//!
//! The witnesses are **cached**, not recomputed: `iota(4,9)` takes nine
//! and a half minutes of branch-and-bound (`examples/iota_witnesses.rs`
//! is what produced them, and prints the lines pasted below). Every one
//! is re-verified by `intersecting::verify` here before anything is
//! computed from it, so a stale paste is a failed run rather than a wrong
//! table.
//!
//! Run with `cargo run --release --example iota_structure`.
//! `--nauty` also emits dreadnaut input, so the group orders can be
//! checked against an independent implementation.

use sunflower_formal::{ground, intersecting, structure};

/// `(b, ground, iota(b,ground), witness)`, every entry exhaustive.
/// Produced by `examples/iota_witnesses.rs --max-b 4 --max-g 9`.
const WITNESSES: &[(u32, u32, &[u32])] = &[
    (1, 1, &[1]),
    (2, 3, &[3, 5, 6]),
    (3, 4, &[7, 11, 13, 14]),
    (3, 5, &[7, 11, 13, 22, 26, 28]),
    (3, 6, &[7, 11, 21, 26, 28, 38, 41, 44, 49, 50]),
    (4, 5, &[15, 23, 27, 29, 30]),
    (4, 6, &[15, 23, 27, 45, 46, 53, 54, 57, 58]),
    (
        4,
        7,
        &[15, 23, 27, 45, 53, 58, 60, 78, 86, 89, 92, 105, 106, 113, 114],
    ),
    (
        4,
        8,
        &[
            15, 23, 27, 45, 54, 78, 89, 99, 102, 105, 116, 120, 149, 154, 163, 165, 172, 178, 184,
            195, 202, 204, 209, 212,
        ],
    ),
    (
        4,
        9,
        &[
            15, 23, 27, 45, 46, 53, 54, 57, 58, 195, 204, 212, 216, 225, 226, 323, 332, 340, 344,
            353, 354, 387, 396, 404, 408, 417, 418,
        ],
    ),
];

fn main() {
    let want_nauty = std::env::args().any(|a| a == "--nauty");

    println!("=== the iota table, from the cached exhaustive witnesses ===\n");
    println!("   b    g   iota(b,g)   iota^(1/b)   iota^(1/(b-1))");
    for &(b, g, w) in WITNESSES {
        if let Err(e) = intersecting::verify(w, b, true) {
            panic!("cached witness for (b={b}, g={g}) is not valid: {e}");
        }
        let n = w.len();
        let r1 = (n as f64).powf(1.0 / (b as f64));
        let r2 = if b > 1 {
            format!("{:.4}", (n as f64).powf(1.0 / ((b - 1) as f64)))
        } else {
            "   -  ".into()
        };
        println!("  {b:>2}   {g:>2}   {n:>9}   {r1:>10.4}   {r2:>14}");
    }

    println!("\n=== structure of each extremal family ===\n");
    for &(b, g, w) in WITNESSES {
        if w.len() < 3 {
            continue;
        }
        print!(
            "{}",
            structure::report(&format!("iota({b},{g}) = {}", w.len()), w, b)
        );
        println!("  Coq literal: {}", structure::fmt_coq(w));
        if want_nauty {
            println!("  --- dreadnaut input (pipe to `dreadnaut`) ---");
            print!("{}", structure::dreadnaut_input(w));
        }
        println!();
    }

    println!("=== the general row N(m,g), for the cone comparison ===\n");
    for m in 1u32..=3 {
        print!("  m = {m}:");
        for g in m..=9 {
            let (n, _, done) = ground::max_sunflower_free(g, m, 4_000_000_000);
            print!(" g={g}:{}{}", n, if done { "" } else { "+" });
        }
        println!();
    }

    println!("\n=== the cone: iota(m+1) >= g(m), checked on the extremal N(m,g) ===\n");
    println!("  m   g   N(m,g)   cone verified as intersecting + sunflower-free");
    for m in 1u32..=3 {
        for g in [6u32, 7, 8, 9] {
            if g < m {
                continue;
            }
            let (n, w, done) = ground::max_sunflower_free(g, m, 4_000_000_000);
            if !done || w.is_empty() {
                continue;
            }
            let w32: Vec<u32> = w.iter().map(|&x| u32::from(x)).collect();
            let c = structure::cone(&w32, g);
            let ok = intersecting::verify(&c, m + 1, true);
            println!(
                "  {m}   {g}   {n:>6}   {}",
                match ok {
                    Ok(()) => format!("yes ({} members, {}-uniform)", c.len(), m + 1),
                    Err(e) => format!("NO: {e}"),
                }
            );
        }
    }

    println!(
        "\n=== the cone of the tree paths: an intersecting family needing 2^b - 1 points ===\n"
    );
    println!("  b   members   support   2^b - 1   c*b for c=4   intersecting+sunflower-free");
    for d in 2u32..=6 {
        let tp = structure::tree_paths(d);
        let apex = (1u32 << (d + 1)) - 2; // first label above every edge
        let c = structure::cone(&tp, apex);
        let b = d + 1;
        let sup = structure::support_points(&c).len();
        let ok = intersecting::verify(&c, b, true);
        println!(
            "  {b}   {:>7}   {sup:>7}   {:>7}   {:>11}   {}",
            c.len(),
            (1u32 << b) - 1,
            4 * b,
            match ok {
                Ok(()) => "yes".to_string(),
                Err(e) => format!("NO ({e})"),
            }
        );
    }

    println!("\n=== supermultiplicativity, and the measured defect ===\n");
    // The best value per b that the exhaustive table reaches.
    let mut best: Vec<(u32, usize, Vec<u32>, u32)> = Vec::new();
    for &(b, g, w) in WITNESSES {
        match best.iter_mut().find(|(bx, _, _, _)| *bx == b) {
            Some(e) if e.1 < w.len() => {
                e.1 = w.len();
                e.2 = w.to_vec();
                e.3 = g;
            }
            Some(_) => {}
            None => best.push((b, w.len(), w.to_vec(), g)),
        }
    }
    println!("   a   b   iota(a)   iota(b)   product   iota(a+b) known   defect");
    for i in 0..best.len() {
        for j in i..best.len() {
            let (a, na, ref fa, ga) = best[i];
            let (bb, nb, ref fb, _) = best[j];
            let s = structure::direct_sum(fa, fb, ga);
            let ok = intersecting::verify(&s, a + bb, true);
            assert!(
                ok.is_ok(),
                "the direct sum of two intersecting sunflower-free families must be one: {ok:?}"
            );
            assert_eq!(s.len(), na * nb);
            let known = best.iter().find(|(bx, _, _, _)| *bx == a + bb).map(|e| e.1);
            println!(
                "   {a}   {bb}   {na:>7}   {nb:>7}   {:>7}   {:>15}   {}",
                na * nb,
                known.map(|k| k.to_string()).unwrap_or("?".into()),
                known
                    .map(|k| format!("{:.4}", k as f64 / (na * nb) as f64))
                    .unwrap_or(">= 1".into())
            );
        }
    }

    println!("\n=== the ratio iota(b+1)/iota(b), which is the whole conjecture ===\n");
    println!("  b   iota(b)   iota(b+1)   ratio   (bounded ratio D settles k = 3, with c(3) = 2D)");
    for i in 0..best.len().saturating_sub(1) {
        let (b, nb, _, _) = &best[i];
        let (_, nb1, _, _) = &best[i + 1];
        println!(
            "  {b}   {nb:>7}   {nb1:>9}   {:.4}",
            *nb1 as f64 / *nb as f64
        );
    }
}
