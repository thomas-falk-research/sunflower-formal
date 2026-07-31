//! Is the 1972 construction maximal? — the campaign, run.
//!
//! `docs/roadmap.md` §12 tabulates what it takes to beat
//! Abbott–Hanson–Sauer at each uniformity. At `b = 9` the substitution
//! `substitute(iota(3), iota(3))` builds 10,000 members and the
//! threshold is 10,001, so **one** addable 9-set would beat 1972
//! outright. Nobody had asked.
//!
//! `extend.rs` explains why the question is finite: a candidate `C`
//! interacts with the family only through `C ∩ support(F)`, so
//! enumerating traces answers the question for every ground set at
//! once. This runs it, five ways, and cross-checks each verdict.
//!
//! Run with `cargo run --release --example extend_ahs`.

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

fn fmt(m: u128) -> String {
    let pts: Vec<u32> = (0..128).filter(|x| m >> x & 1 == 1).collect();
    format!(
        "{{{}}}",
        pts.iter().map(|p| p.to_string()).collect::<Vec<_>>().join(",")
    )
}

/// A pure substitution: intersecting, so the *meeting* condition alone
/// decides, and that is the stronger negative -- nothing can be added
/// even ignoring sunflower-freeness.
fn pure(name: &str, f: &[u128], b: usize, brute: bool) {
    println!("--- {name}");
    let sup = extend::support_points_128(f);
    structure::verify_128(f, b as u32, true).expect("the family itself does not verify");
    println!(
        "  {} members, uniformity {b}, support {} points, verified intersecting + sunflower-free",
        f.len(),
        sup.len()
    );

    // Covering number, and what the minimum hitting sets are.
    let (hs, exhaustive) = extend::minimal_hitting_sets(f, b, 200_000_000);
    assert!(exhaustive, "the hitting-set enumeration ran out of budget");
    let tau = hs.iter().map(|s| s.count_ones() as usize).min().unwrap();
    let minimum: Vec<u128> = hs
        .iter()
        .copied()
        .filter(|s| s.count_ones() as usize == tau)
        .collect();
    let all_members = minimum.iter().all(|s| f.contains(s));
    println!(
        "  tau(F) = {tau} (= b? {}), minimum hitting sets: {}, all of them members? {}",
        tau == b,
        minimum.len(),
        all_members
    );
    println!(
        "  minimal hitting sets of size <= b: {} (members: {})",
        hs.len(),
        f.len()
    );

    // Brute force over every trace, where it is affordable.
    if brute {
        let traces = extend::addable_traces_brute(f, b, true, false);
        println!(
            "  brute force over every trace: {} addable (0 = maximal on every ground set)",
            traces.len()
        );
        for t in traces.iter().take(5) {
            println!("      {}", fmt(*t));
        }
    } else {
        println!("  brute force skipped: sum_j C({}, j) for j <= {b} is out of reach", sup.len());
    }

    // SAT, always.
    match extend::addable_sat(f, b, true, false, 600, name) {
        Ok(extend::Extension::Maximal) => {
            println!("  SAT (two solvers agreeing): UNSAT -- MAXIMAL on every ground set")
        }
        Ok(extend::Extension::Found(t, m)) => println!(
            "  SAT: FOUND an addable set, trace {} full member {}",
            fmt(t),
            fmt(m)
        ),
        Ok(extend::Extension::Undecided) => println!("  SAT: undecided within the budget"),
        Err(e) => println!("  SAT: solver error {e}"),
    }
    println!();
}

/// A cone `cone_p(F)`: the apex is in every member, so *every* candidate
/// containing it meets everything for free and the question is entirely
/// about sunflower-freeness. Two cases, and `extend.rs`'s trace reduction
/// covers both:
///
/// * `p in C`: then `C = {p} ∪ D` and the condition is exactly that `D`
///   extends the **base** family `F` as a sunflower-free family -- which
///   is the question asked here;
/// * `p not in C`: then `A ∩ C` misses `p` while `(A ∩ B) ∪ {p}` has it,
///   so no triple can be a sunflower and the only condition is that `C`
///   hits every member of `F`. That needs `tau(F) <= b`, and the
///   covering number is printed so the reader can see it does not hold.
fn cone_base(name: &str, f: &[u128], m: usize, brute: bool) {
    println!("--- {name}");
    let sup = extend::support_points_128(f);
    structure::verify_128(f, m as u32, false).expect("the base family does not verify");
    println!(
        "  base: {} members, uniformity {m}, support {} points, verified sunflower-free",
        f.len(),
        sup.len()
    );
    match extend::covering_number(f, m + 2, 200_000_000) {
        Some(t) => println!("  tau(base) = {t}; the apex-free case needs tau <= {}", m + 1),
        None => println!(
            "  tau(base) > {} -- so the apex-free case is empty",
            m + 1
        ),
    }
    if brute {
        let traces = extend::addable_traces_brute(f, m, false, true);
        println!(
            "  brute force over every trace: {} addable (as a sunflower-free family)",
            traces.len()
        );
        for t in traces.iter().take(5) {
            println!("      {}", fmt(*t));
        }
    }
    match extend::addable_sat(f, m, false, true, 900, name) {
        Ok(extend::Extension::Maximal) => println!(
            "  SAT (two solvers agreeing): UNSAT -- the base is a MAXIMAL sunflower-free family, \
             so the cone is maximal too"
        ),
        Ok(extend::Extension::Found(t, mm)) => println!(
            "  SAT: FOUND an addable set, trace {} full member {} \
             -- so iota({}) >= {}",
            fmt(t),
            fmt(mm),
            m + 1,
            f.len() + 1
        ),
        Ok(extend::Extension::Undecided) => println!("  SAT: undecided within the budget"),
        Err(e) => println!("  SAT: solver error {e}"),
    }
    println!();
}

/// Maximal is not maximum, and this is the witness hunt.
///
/// The results above say the substitution families cannot be extended.
/// They do **not** say the substitution is optimal — a *maximal* family
/// can be far smaller than a *maximum* one, and if that happens at a
/// uniformity the repository can decide, it should be recorded rather
/// than left as a caveat.
///
/// So: grow random greedy families at `b = 3`, where the maximum is the
/// exhaustively known `iota(3) = 10`, and test each for maximality with
/// the same trace enumeration used above — which is complete over every
/// ground set, not just the one it was grown on. The smallest maximal
/// family found is the witness.
fn maximal_is_not_maximum(b: u32, ground: u32, rounds: u32, known_max: usize) {
    println!("--- maximal is not maximum: random greedy at b = {b}, ground {ground}");
    let all: Vec<u128> = (0..(1u128 << ground))
        .filter(|m| m.count_ones() == b)
        .collect();
    let mut best: Option<Vec<u128>> = None;
    // A fixed-seed xorshift, so the run is reproducible.
    let mut state: u64 = 0x2545_f491_4f6c_dd1d;
    let mut next = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    for _ in 0..rounds {
        let mut order: Vec<u128> = all.clone();
        for i in (1..order.len()).rev() {
            let j = (next() % (i as u64 + 1)) as usize;
            order.swap(i, j);
        }
        let mut fam: Vec<u128> = Vec::new();
        for &x in &order {
            let mut ok = fam.iter().all(|&a| a & x != 0);
            if ok {
                'pairs: for i in 0..fam.len() {
                    for j in (i + 1)..fam.len() {
                        let ab = fam[i] & fam[j];
                        if ab == (fam[i] & x) && ab == (fam[j] & x) {
                            ok = false;
                            break 'pairs;
                        }
                    }
                }
            }
            if ok {
                fam.push(x);
            }
        }
        // Maximal over *every* ground set, not only this one.
        if !extend::addable_traces_brute(&fam, b as usize, true, true).is_empty() {
            continue;
        }
        if best.as_ref().map(|f| fam.len() < f.len()).unwrap_or(true) {
            best = Some(fam);
        }
    }
    match best {
        Some(f) => {
            structure::verify_128(&f, b, true).expect("the witness does not verify");
            println!(
                "  smallest maximal family found: {} members against the maximum {known_max}",
                f.len()
            );
            println!("  members: {}", f.iter().map(|&m| fmt(m)).collect::<Vec<_>>().join(" "));
            println!(
                "  so maximality is worth nothing numerically: {} < {known_max}",
                f.len()
            );
        }
        None => println!("  no maximal family found in {rounds} rounds"),
    }
    println!();
}

fn main() {
    let tri = triangle();
    let tt = two_triangles();
    let i3 = iota3();

    println!("=== the pure Abbott-Hanson-Sauer substitutions ===");
    println!("    intersecting, so the meeting condition alone decides:");
    println!("    a maximal family here cannot be extended even if");
    println!("    sunflower-freeness is ignored entirely.\n");

    let b4 = intersecting::substitute(&tri, 3, &tri, 3);
    pure("substitute(iota(2), iota(2)) = iota(4,9) = 27", &b4, 4, true);

    let b6 = intersecting::substitute(&tri, 3, &i3, 6);
    pure("substitute(iota(2), iota(3)) = 300 at b = 6", &b6, 6, true);

    let b9 = intersecting::substitute(&i3, 6, &i3, 6);
    pure(
        "substitute(iota(3), iota(3)) = 10000 at b = 9  <-- one more beats 1972",
        &b9,
        9,
        false,
    );

    println!("=== the cone rows of the iota table ===");
    println!("    the apex meets everything, so here the question is");
    println!("    whether the *base* extends as a sunflower-free family.\n");

    let g4 = intersecting::substitute(&tt, 6, &tri, 3);
    cone_base("base of the b = 5 row: substitute(g(2), iota(2)), 54 at m = 4", &g4, 4, true);

    let g6 = intersecting::substitute(&tt, 6, &i3, 6);
    cone_base("base of the b = 7 row: substitute(g(2), iota(3)), 600 at m = 6", &g6, 6, false);

    println!("=== and what maximality is *not* ===\n");
    maximal_is_not_maximum(3, 9, 4000, 10);
}
