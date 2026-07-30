//! Extend the `iota` table past where the search reaches, by construction.
//!
//! Exhaustive search decides `iota(b,g)` up to `(4,9)` and stops: `(4,10)`
//! took 74 minutes to answer one decision question and the SAT layer did
//! not settle the next rung in an hour (`docs/roadmap.md` §9). Past that
//! the only certified values are *lower* bounds from constructions, and
//! there are three:
//!
//! * **the cone** — `iota(m+1) >= g(m)`: add a fresh point to every member
//!   of a sunflower-free family. New in `coq/Product.v`;
//! * **the doubling** — `g(b) >= 2 iota(b)` (`Intersecting.doubling_lower_bound`);
//! * **the substitution** — `iota(ab) >= iota(a) * iota(b)^a`, the
//!   Abbott–Hanson–Sauer construction with both families intersecting.
//!   Verified, not formalised (`docs/roadmap.md` §5 item 2).
//!
//! Every family this prints is handed to `structure::verify_128`, which
//! shares no code with the constructions: uniformity, distinctness,
//! intersecting-ness and sunflower-freeness are all re-checked from
//! scratch. A construction that were wrong would fail here rather than
//! enter the table.

use sunflower_formal::{intersecting, structure};

fn masks(sets: &[&[u32]]) -> Vec<u32> {
    sets.iter()
        .map(|s| s.iter().fold(0u32, |a, &x| a | 1 << x))
        .collect()
}

fn main() {
    // The three seeds, all exhaustive maxima.
    let triangle = masks(&[&[0, 1], &[0, 2], &[1, 2]]); // iota(2) = 3 on 3 points
    let two_triangles = masks(&[
        &[0, 1],
        &[1, 2],
        &[0, 2],
        &[3, 4],
        &[4, 5],
        &[3, 5],
    ]); // g(2) = 6 on 6 points
    let iota3 = masks(&[
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
    ]); // iota(3) = 10 on 6 points
    let iota4: Vec<u32> = vec![
        15, 23, 27, 45, 46, 53, 54, 57, 58, 195, 204, 212, 216, 225, 226, 323, 332, 340, 344, 353,
        354, 387, 396, 404, 408, 417, 418,
    ]; // iota(4,9) = 27 on 9 points

    for (name, f, b, inter) in [
        ("triangle = iota(2)", &triangle, 2u32, true),
        ("two_triangles = g(2)", &two_triangles, 2, false),
        ("iota3 = iota(3)", &iota3, 3, true),
        ("iota4 = iota(4,9)", &iota4, 4, true),
    ] {
        let r = intersecting::verify(f, b, inter);
        println!(
            "  seed {name:24} {} members, {} points: {}",
            f.len(),
            structure::support_points(f).len(),
            match r {
                Ok(()) => "verified".to_string(),
                Err(e) => panic!("seed {name} invalid: {e}"),
            }
        );
    }
    println!();

    // Each row: (b, members, ground, route). Everything re-verified.
    let mut rows: Vec<(u32, usize, u32, String)> = Vec::new();

    // b = 5: cone of the substitution g(4) >= g(2) * iota(2)^2 = 6 * 9 = 54.
    {
        let g4 = intersecting::substitute(&two_triangles, 6, &triangle, 3);
        let apex = 6 * 3;
        let h = structure::cone_128(&g4, apex);
        structure::verify_128(&h, 5, true).expect("cone of substitute(g(2), iota(2))");
        rows.push((
            5,
            h.len(),
            structure::support_count_128(&h),
            "cone(substitute(g(2), iota(2)))".into(),
        ));
    }

    // b = 6: substitution iota(6) >= iota(2) * iota(3)^2 = 3 * 100 = 300.
    {
        let h = intersecting::substitute(&triangle, 3, &iota3, 6);
        structure::verify_128(&h, 6, true).expect("substitute(iota(2), iota(3))");
        rows.push((
            6,
            h.len(),
            structure::support_count_128(&h),
            "substitute(iota(2), iota(3))".into(),
        ));
    }

    // b = 7: cone of the substitution g(6) >= g(2) * iota(3)^2 = 6 * 100 = 600.
    {
        let g6 = intersecting::substitute(&two_triangles, 6, &iota3, 6);
        let apex = 6 * 6;
        let h = structure::cone_128(&g6, apex);
        structure::verify_128(&h, 7, true).expect("cone of substitute(g(2), iota(3))");
        rows.push((
            7,
            h.len(),
            structure::support_count_128(&h),
            "cone(substitute(g(2), iota(3)))".into(),
        ));
    }

    // b = 8: substitution iota(8) >= iota(2) * iota(4)^2 = 3 * 729 = 2187.
    // Stated, not verified: 2187 members means C(2187,3) = 1.7e9 triples,
    // and the ground set is 3 * 9 = 27 which fits, but the check does not.
    // Recorded as unverified rather than run.

    println!("=== the iota table, extended by construction ===\n");
    println!("   b   iota(b) >=   points   iota^(1/b)   route");
    let known: &[(u32, usize, u32, &str)] = &[
        (1, 1, 1, "exhaustive"),
        (2, 3, 3, "exhaustive"),
        (3, 10, 6, "exhaustive"),
        (4, 27, 9, "exhaustive at g = 9; g >= 10 open"),
    ];
    for &(b, n, g, r) in known {
        println!(
            "  {b:>2}   {n:>10}   {g:>6}   {:>10.4}   {r}",
            (n as f64).powf(1.0 / b as f64)
        );
    }
    for (b, n, g, r) in &rows {
        println!(
            "  {b:>2}   {n:>10}   {g:>6}   {:>10.4}   {r} (verified)",
            (*n as f64).powf(1.0 / *b as f64)
        );
    }
    println!(
        "   8   {:>10}   {:>6}   {:>10.4}   substitute(iota(2), iota(4,9)) -- NOT verified here",
        3 * 27 * 27,
        3 * 9,
        (3.0f64 * 27.0 * 27.0).powf(1.0 / 8.0)
    );

    println!("\n  The previous best lower bounds at b = 5 were 42 (SAT, ground 10,");
    println!("  docs/roadmap.md §9) and 30 (the direct sum iota(2)*iota(3)).");
    println!("  Both are beaten by the cone.\n");

    println!("=== what these give for f(n,3) through the doubling g(b) >= 2 iota(b) ===\n");
    println!("   b   2*iota(b)   rate (2 iota(b))^(1/b)");
    for &(b, n, _, _) in known {
        println!(
            "  {b:>2}   {:>9}   {:>10.4}",
            2 * n,
            (2.0 * n as f64).powf(1.0 / b as f64)
        );
    }
    for (b, n, _, _) in &rows {
        println!(
            "  {b:>2}   {:>9}   {:>10.4}",
            2 * n,
            (2.0 * *n as f64).powf(1.0 / *b as f64)
        );
    }
    println!("\n  For comparison: the repository's headline is 20^(1/3) = 2.7144,");
    println!("  and Abbott-Hanson-Sauer reach 10^(1/2) = 3.1623 asymptotically.");

    println!("\n=== the cone of the tree paths, in 128 bits ===\n");
    println!("  b   members   support   2^b - 1   verified");
    for d in 2u32..=6 {
        let tp = structure::tree_paths_128(d);
        let apex = (1u32 << (d + 1)) - 2;
        let h = structure::cone_128(&tp, apex);
        let b = d + 1;
        let sup = structure::support_count_128(&h);
        let ok = structure::verify_128(&h, b, true);
        println!(
            "  {b}   {:>7}   {sup:>7}   {:>7}   {}",
            h.len(),
            (1u32 << b) - 1,
            match ok {
                Ok(()) => "yes".to_string(),
                Err(e) => format!("NO ({e})"),
            }
        );
    }
    println!("\n  So an intersecting 3-sunflower-free b-uniform family can need");
    println!("  2^b - 1 ground points, every one of them used: the *universal*");
    println!("  reading of IotaGroundBounded is false for every constant.");
}
