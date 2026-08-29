//! Are the 27-member families a random fill finds on nine points the
//! Abbott–Hanson–Sauer substitution family, or something else?
//!
//! `Product.iota_four_at_least_27` witnesses `iota(4) >= 27` with one
//! explicit family on `[9]`, and `Substitution.triangle_squared_is_maximal`
//! shows it is maximal. Nothing in this development says it is the
//! *only* 27-member family, and the question has never been asked here.
//!
//! A pure fill (`plateau::search` with no force moves) reaches 27 about
//! nineteen times in a million runs. This driver collects those hits and
//! sorts them into orbits under the full symmetric group on the nine
//! points, by brute force over all `9! = 362880` relabellings.

use sunflower_formal::{plateau, wide};

/// `Product.iota4`, as bitmasks.
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

/// Every permutation of `[n]`, in lexicographic order.
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

/// Lexicographically least relabelling of `f`, as a sorted mask list.
fn canon(f: &[u32], ps: &[Vec<u8>]) -> Vec<u32> {
    let mut best: Option<Vec<u32>> = None;
    let mut buf = vec![0u32; f.len()];
    for p in ps {
        for (slot, &m) in buf.iter_mut().zip(f) {
            let mut q = 0u32;
            let mut r = m;
            while r != 0 {
                let bit = r.trailing_zeros() as usize;
                q |= 1 << p[bit];
                r &= r - 1;
            }
            *slot = q;
        }
        buf.sort_unstable();
        match &best {
            Some(bst) if *bst <= buf => {}
            _ => best = Some(buf.clone()),
        }
    }
    best.unwrap()
}

fn main() {
    let runs: u64 = std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(5_000_000);
    let (b, n, target) = (4u32, 9u32, 27usize);

    let mut raw: Vec<Vec<u32>> = Vec::new();
    for s in 0..runs {
        let f = plateau::search(n, b, 0, s.wrapping_mul(0x9E3779B97F4A7C15) ^ 0xC0FFEE, &[], true, |_, _| {});
        if f.best >= target {
            let mut v = f.family.clone();
            v.sort_unstable();
            let wide: Vec<u64> = v.iter().map(|&x| u64::from(x)).collect();
            wide::verify(&wide, b, true).expect("fill produced an invalid family");
            assert_eq!(v.len(), target);
            raw.push(v);
        }
    }
    println!("{runs} fills at (b={b}, n={n}); {} reached {target}", raw.len());
    let mut distinct = raw.clone();
    distinct.sort();
    distinct.dedup();
    println!("distinct as labelled families: {}", distinct.len());

    let ps = perms(n as usize);
    let ahs = canon(&iota4(), &ps);
    let mut orbits: Vec<Vec<u32>> = Vec::new();
    let mut ahs_hits = 0usize;
    for f in &distinct {
        let c = canon(f, &ps);
        if c == ahs {
            ahs_hits += 1;
        }
        if !orbits.contains(&c) {
            orbits.push(c);
        }
    }
    println!("orbits under S_{n}: {}", orbits.len());
    println!("of the {} distinct, {ahs_hits} are relabellings of Product.iota4", distinct.len());
    for (i, o) in orbits.iter().enumerate() {
        println!("  orbit {i}{}: {:?}", if *o == ahs { " (= iota4)" } else { "" }, o);
    }
}
