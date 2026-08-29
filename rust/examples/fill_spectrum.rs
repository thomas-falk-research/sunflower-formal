//! The size spectrum a pure random fill reaches at `(b, n)`, and the
//! witnesses at the top of it.
//!
//! A fill stops at a *maximal* family, so every size it reports is the
//! size of some maximal intersecting sunflower-free family on `[n]`. A
//! size the fill never reaches is weak evidence that no maximal family
//! has that size; a size it reaches is a proof that one does, and the
//! witness is printed so `wide::verify` can check it.

use sunflower_formal::{plateau, wide};

fn main() {
    let mut a = std::env::args().skip(1);
    let b: u32 = a.next().and_then(|s| s.parse().ok()).unwrap_or(4);
    let n: u32 = a.next().and_then(|s| s.parse().ok()).unwrap_or(9);
    let runs: u64 = a.next().and_then(|s| s.parse().ok()).unwrap_or(1_000_000);
    let show: usize = a.next().and_then(|s| s.parse().ok()).unwrap_or(25);

    let mut hist = vec![0u64; 128];
    let mut wit: Vec<(usize, Vec<u32>)> = Vec::new();
    for s in 0..runs {
        let f = plateau::search(n, b, 0, s.wrapping_mul(0x9E3779B97F4A7C15) ^ 0xC0FFEE, &[], true, |_, _| {});
        hist[f.best.min(127)] += 1;
        if f.best >= show && wit.iter().all(|(k, _)| *k != f.best) {
            wit.push((f.best, f.family.clone()));
        }
    }
    let lo = hist.iter().position(|&c| c > 0).unwrap();
    let hi = 127 - hist.iter().rev().position(|&c| c > 0).unwrap();
    println!("b={b} n={n} runs={runs}");
    for i in lo..=hi {
        println!("  {i:3}  {:>9}", hist[i]);
    }
    wit.sort_by_key(|(k, _)| *k);
    for (k, f) in &wit {
        let wide: Vec<u64> = f.iter().map(|&x| u64::from(x)).collect();
        let ok = wide::verify(&wide, b, true);
        println!("  witness {k}: {:?}  verify={:?}", f, ok);
    }
}
