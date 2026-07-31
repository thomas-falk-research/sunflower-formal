//! Is the Erdős–Rado ratio `rho(F) = |F| / maxdeg(F)` bounded?
//!
//! A constant bound settles the sunflower conjecture at `k = 3`
//! outright: `g(b) <= c g(b-1)` gives `g(b) <= 2 c^(b-1)`. The measured
//! row in `rust/tests/iota_sandwich.rs` — worst 2, 3, 2.75 at
//! uniformities 1, 2, 3 against the proved `2b` — looks flat.
//!
//! This asks whether it stays flat. Run with
//! `cargo run --release --example star_defect`.

use sunflower_formal::{intersecting, ratio, structure};

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

/// Two disjoint copies: `|2F| = 2|F|` and the degrees do not change, so
/// `rho` doubles. Only valid when `F` is intersecting.
fn doubled_128(f: &[u128], shift: u32) -> Vec<u128> {
    let mut out = f.to_vec();
    out.extend(f.iter().map(|&a| a << shift));
    out
}

fn row(name: &str, f: &[u128], b: u32, intersecting: bool) {
    structure::verify_128(f, b, intersecting)
        .unwrap_or_else(|e| panic!("{name} does not verify: {e}"));
    let (n, d) = ratio::rho_128(f);
    let chain = ratio::greedy_chain(f, b);
    let (max, geo) = ratio::chain_profile(&chain);
    // The product telescopes: each level's `deg` is the next level's
    // `size`, so the product of the rationals is `|F| / (last deg)`.
    // Computing it as a running integer product would truncate --
    // `27/12` is not an integer -- so it is checked as a telescope.
    for w in chain.windows(2) {
        assert_eq!(w[0].deg, w[1].size, "the chain does not telescope");
    }
    let prod = chain.last().map(|l| n / l.deg.max(1)).unwrap_or(0);
    println!(
        "  {name:<38} b={b:<3} |F|={n:<6} maxdeg={d:<6} rho={:<7.4} chain max={max:<7.4} geo={geo:<7.4} prod={prod}",
        n as f64 / d as f64
    );
    let ratios: Vec<String> = chain
        .iter()
        .map(|l| format!("{}/{}", l.size, l.deg))
        .collect();
    println!("      chain: {}", ratios.join("  "));
}

fn main() {
    let tri = triangle();
    let tt = two_triangles();
    let i3 = iota3();
    let i4 = iota4();

    println!("=== rho = |F| / maxdeg, and the chain it controls ===");
    println!("    the proved bound is rho <= 2b (sunflower-free) and rho <= b (intersecting)\n");

    row("iota(2) = triangle", &structure::widen(&tri), 2, true);
    row("g(2) = two_triangles", &structure::widen(&tt), 2, false);
    row("iota(3) = 10", &structure::widen(&i3), 3, true);
    row("iota(4,9) = 27", &structure::widen(&i4), 4, true);
    row(
        "double(iota(3)) = 20, g(3) witness",
        &doubled_128(&structure::widen(&i3), 6),
        3,
        false,
    );
    row(
        "double(iota(4,9)) = 54, g(4) witness",
        &doubled_128(&structure::widen(&i4), 9),
        4,
        false,
    );
    println!();

    println!("=== is rho multiplicative under the substitution? ===\n");
    let cases: &[(&str, &[u32], u32, &[u32], u32)] = &[
        ("substitute(iota(2), iota(2)) = 27", &tri, 3, &tri, 3),
        ("substitute(iota(2), iota(3)) = 300", &tri, 3, &i3, 6),
        ("substitute(iota(3), iota(2)) = 80", &i3, 6, &tri, 3),
        ("substitute(iota(3), iota(3)) = 10000", &i3, 6, &i3, 6),
        ("substitute(g(2), iota(2)) = 54", &tt, 6, &tri, 3),
        ("substitute(g(2), iota(3)) = 600", &tt, 6, &i3, 6),
    ];
    println!("  construction                          rho(G)   rho(H)   product   measured   agree");
    for &(name, g, vg, h, wg) in cases {
        let gg = structure::widen(g);
        let hh = structure::widen(h);
        let f = intersecting::substitute(g, vg, h, wg);
        let (gn, gd) = ratio::rho_128(&gg);
        let (hn, hd) = ratio::rho_128(&hh);
        let (fn_, fd) = ratio::rho_128(&f);
        // Exact rational comparison: rho(G) rho(H) == rho(F).
        let agree = gn * hn * fd == fn_ * gd * hd;
        println!(
            "  {name:<36}  {:>6.4}   {:>6.4}   {:>7.4}   {:>8.4}   {}",
            gn as f64 / gd as f64,
            hn as f64 / hd as f64,
            (gn * hn) as f64 / (gd * hd) as f64,
            fn_ as f64 / fd as f64,
            if agree { "yes" } else { "NO" }
        );
        assert!(agree, "rho is not multiplicative on {name}");
    }
    println!();

    println!("=== the tower, and what it does to rho ===\n");
    println!("  Iterating the substitution on iota(3): b = 3^k, rho = 2^k.");
    println!("  b       members            rho (predicted)   verified");
    // b = 3, 9 are buildable; 27 has 10^13 members and is arithmetic only.
    {
        let f3 = structure::widen(&i3);
        let (n, d) = ratio::rho_128(&f3);
        println!("    3   {:>16}   {:>15.4}   {} (rho = {n}/{d})", f3.len(), 2.0, "yes");
        let f9 = intersecting::substitute(&i3, 6, &i3, 6);
        structure::verify_128(&f9, 9, true).expect("b = 9 tower does not verify");
        let (n9, d9) = ratio::rho_128(&f9);
        println!(
            "    9   {:>16}   {:>15.4}   {} (rho = {n9}/{d9})",
            f9.len(),
            4.0,
            if n9 == 4 * d9 { "yes" } else { "NO" }
        );
        assert_eq!(n9, 4 * d9, "rho at b = 9 is not 4");
        println!(
            "   27   {:>16}   {:>15.4}   {}",
            "10^13",
            8.0,
            "arithmetic only (10^13 members)"
        );
    }
    println!();
    println!("  rho = 2^k at b = 3^k, so rho = b^(log_3 2) = b^0.6309...");
    println!("  UNBOUNDED. There is no constant c with rho(F) <= c, and the");
    println!("  family that refutes it is the 1972 construction itself.\n");

    println!("=== what survives: the chain, not the maximum ===\n");
    println!("  On the tower the product of the b chain ratios is 10^((b-1)/2),");
    println!("  so the geometric mean tends to sqrt(10) = 3.1623 while the");
    println!("  largest single factor grows like b^0.63.\n");
    println!("   b    product          geometric mean   largest factor (rho)");
    for k in 1..=3u32 {
        let b = 3u32.pow(k);
        let prod = 10f64.powf((b as f64 - 1.0) / 2.0);
        println!(
            "  {b:>2}   {prod:>14.4}   {:>14.4}   {:>10.4}",
            prod.powf(1.0 / b as f64),
            2f64.powi(k as i32)
        );
    }
    println!("\n  So the conjecture is a statement about the *average* of the");
    println!("  chain ratios, and a per-level constant is provably unavailable.");
}
