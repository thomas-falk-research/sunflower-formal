//! Exploration: what does compression do to sunflower-freeness?
//!
//! Prints, and asserts nothing. `tests/shifting.rs` pins whatever this
//! finds.

use sunflower_formal::ground::max_sunflower_free;
use sunflower_formal::shift::*;
use sunflower_formal::spread::matching_number;

/// Smallest sunflower-free `m`-uniform family on `ground` points that
/// some single shift destroys. Enumerates by increasing size, so the
/// first hit is minimal in `|F|`.
fn smallest_breaker(ground: u32, m: u32, max_size: usize) -> Option<(Vec<u32>, u32, u32, Vec<u32>)> {
    let sets = subsets_of_size(ground, m);
    for size in 3..=max_size.min(sets.len()) {
        let mut hit = None;
        for_each_combination(sets.len(), size, &mut |idx: &[usize]| {
            if hit.is_some() {
                return false;
            }
            let fam: Vec<u32> = idx.iter().map(|&i| sets[i]).collect();
            if is_sunflower_free(&fam) {
                if let Some((i, j, next)) = breaking_shift(&fam, ground) {
                    hit = Some((fam, i, j, next));
                    return false;
                }
            }
            true
        });
        if hit.is_some() {
            return hit;
        }
    }
    None
}

/// Every `size`-subset of `[n]` in lexicographic order. `visit` returns
/// false to stop.
fn for_each_combination(n: usize, size: usize, visit: &mut dyn FnMut(&[usize]) -> bool) {
    if size > n {
        return;
    }
    let mut idx: Vec<usize> = (0..size).collect();
    loop {
        if !visit(&idx) {
            return;
        }
        let mut p = size;
        loop {
            if p == 0 {
                return;
            }
            p -= 1;
            if idx[p] < n - (size - p) {
                idx[p] += 1;
                for q in (p + 1)..size {
                    idx[q] = idx[q - 1] + 1;
                }
                break;
            }
        }
    }
}

fn show(f: &[u32]) -> String {
    let mut v: Vec<String> = f.iter().map(|&a| format!("{:?}", elements(a))).collect();
    v.sort();
    v.join(" ")
}

fn main() {
    println!("== (a) does a single shift preserve 3-sunflower-freeness? ==");
    for (m, g, cap) in [(2u32, 4u32, 6usize), (2, 5, 6), (2, 6, 6), (3, 6, 6), (3, 7, 5), (3, 8, 5)] {
        match smallest_breaker(g, m, cap) {
            Some((f, i, j, next)) => {
                println!(
                    "  m={m} g={g}: NO. smallest breaker has {} members\n     F  = {}\n     ({i},{j})-shift -> {}",
                    f.len(),
                    show(&f),
                    show(&next)
                );
                println!(
                    "     nu(F) = {}, nu(shift F) = {}   (matching number, the empty link)",
                    matching_number(&f),
                    matching_number(&next)
                );
            }
            None => println!("  m={m} g={g}: no breaker up to size {cap}"),
        }
    }

    println!();
    println!("== (b) is the maximum attained by a left-compressed family? ==");
    println!("  m  g   N(m,g)  left-compressed max   iota-style (intersecting)");
    for m in 1u32..=4 {
        for g in m..=(2 * m + 3).min(11) {
            let (lc, w, nodes) = max_left_compressed(g, m, false);
            let (lci, _, _) = max_left_compressed(g, m, true);
            // Only the cheap corner of the general table: N(3,9) is a
            // quarter of an hour and N(4,g) worse. The published row is
            // in docs/roadmap.md §7.
            let gen = if m <= 2 || (m == 3 && g <= 8) {
                let (n, _, done) = max_sunflower_free(g, m, 200_000_000_000);
                if done {
                    format!("{n}")
                } else {
                    "?".into()
                }
            } else {
                "-".into()
            };
            println!(
                "  {m}  {g:2}   {gen:>5}   {lc:>17}   {lci:>22}      nodes={nodes} witness={}",
                show(&w)
            );
        }
    }

    println!();
    println!("== (c) the compressed witness at each m ==");
    for m in 1u32..=6 {
        let w = initial_segment_witness(m);
        println!(
            "  m={m}: {} members, sunflower-free={}, intersecting={}, left-compressed={}",
            w.len(),
            is_sunflower_free(&w),
            is_intersecting(&w),
            is_left_compressed(&w, m + 1)
        );
    }

    println!();
    println!("== (d) what shifting preserves: the empty link only ==");
    // Take a known extremal family and watch its links.
    let two_triangles: Vec<u32> = vec![
        0b000011, 0b000101, 0b000110, 0b011000, 0b101000, 0b110000,
    ];
    println!("  two_triangles: sunflower-free={}", is_sunflower_free(&two_triangles));
    let (nu, y) = max_link_matching(&two_triangles, 6);
    println!("    max link matching = {nu} (at core {:?})", elements(y));
    for j in 0..6u32 {
        for i in 0..j {
            let next = shift_family(&two_triangles, i, j);
            if next == two_triangles {
                continue;
            }
            let (nu2, y2) = max_link_matching(&next, 6);
            println!(
                "    ({i},{j}): nu(empty link) {} -> {}, max link matching {nu} -> {nu2} at {:?}, sunflower-free={}",
                matching_number(&two_triangles),
                matching_number(&next),
                elements(y2),
                is_sunflower_free(&next)
            );
        }
    }

    println!();
    println!("== (e) the closure of an extremal family ==");
    let (cl, steps) = shift_closure(&two_triangles, 6);
    println!(
        "  two_triangles -> {} in {steps} shifts; size {} -> {}, sunflower-free={}",
        show(&cl),
        two_triangles.len(),
        cl.len(),
        is_sunflower_free(&cl)
    );
}
