//! How large can `|A| + |B|` be for cross-intersecting Rao(r)-spread
//! families at a given uniformity?
//!
//!     cross_pair_scan <u> <r> <ground> <restarts> [seed] [mode]
//!
//! `mode` is 0 (default, unconstrained) or 1 (only score configurations
//! in which *neither* side is a star -- the case that decided `u = 2`).
//!
//! `CrossRefined.cross_pair_two_exact` settles `u = 2` exactly:
//! `max(2r+1, 6)`. At `u = 3` the same question is open, and the
//! candidate shapes disagree about which is extremal — one member of `B`
//! against three full stars gives `3r² + 1`, three pairwise disjoint
//! members of `B` against the triples meeting all of them gives
//! `3·min(r², 3r) + 3`, and the second is bigger at small `r`.
//!
//! This is a stochastic maximiser, not an exhaustive search: every row it
//! prints is a **lower** bound on the true maximum on that ground, and a
//! lower bound on the true maximum over all grounds. It is deliberately
//! not called a measurement of the maximum.

use sunflower_formal::spread::{mask_to_set, rao_witness_cands, Mask};

/// A deterministic xorshift, so a printed seed reproduces a run.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % (n as u64)) as usize
    }
}

fn blocks(u: u32, ground: u32) -> Vec<Mask> {
    (0u32..(1u32 << ground))
        .filter(|b| b.count_ones() == u)
        .map(|b| b as Mask)
        .collect()
}

/// Can `x` join `f` and leave it Rao(r)-spread? Uses the sublists-of-
/// members enumeration rather than the whole power set of the ground:
/// `Reflect.rao_witness_agrees` proves the two verdicts coincide, and
/// this one does not grow with the ground.
fn fits(u: u32, f: &[Mask], x: Mask, r: u64) -> bool {
    let mut g: Vec<Mask> = f.to_vec();
    g.push(x);
    rao_witness_cands(u, &g, r).is_none()
}

fn main() {
    let a: Vec<String> = std::env::args().skip(1).collect();
    let u: u32 = a[0].parse().unwrap();
    let r: u64 = a[1].parse().unwrap();
    let ground: u32 = a[2].parse().unwrap();
    let restarts: usize = a[3].parse().unwrap();
    let seed: u64 = a.get(4).and_then(|s| s.parse().ok()).unwrap_or(0x2545F491_4F6CDD1D);
    let mode: u32 = a.get(5).and_then(|s| s.parse().ok()).unwrap_or(0);
    let pointed = |f: &[Mask]| (0..ground).any(|v| f.iter().all(|&c| c & (1u32 << v) != 0));

    let all = blocks(u, ground);
    let mut rng = Rng(seed | 1);
    let mut best = 0usize;
    let mut best_pair: (Vec<Mask>, Vec<Mask>) = (Vec::new(), Vec::new());
    let t = std::time::Instant::now();

    for _ in 0..restarts {
        // start from one random member on each side that meet
        let mut fa: Vec<Mask> = Vec::new();
        let mut fb: Vec<Mask> = Vec::new();
        loop {
            let x = all[rng.below(all.len())];
            let y = all[rng.below(all.len())];
            if x & y != 0 {
                fa.push(x);
                fb.push(y);
                break;
            }
        }
        // grow greedily in random order, then kick and regrow
        for round in 0..400 {
            let mut grew = true;
            while grew {
                grew = false;
                let start = rng.below(all.len());
                for i in 0..all.len() {
                    let x = all[(start + i) % all.len()];
                    if !fa.contains(&x)
                        && fb.iter().all(|&y| x & y != 0)
                        && fits(u, &fa, x, r)
                    {
                        fa.push(x);
                        grew = true;
                    }
                    if !fb.contains(&x)
                        && fa.iter().all(|&y| x & y != 0)
                        && fits(u, &fb, x, r)
                    {
                        fb.push(x);
                        grew = true;
                    }
                }
            }
            let ok = mode == 0 || (!pointed(&fa) && !pointed(&fb));
            if ok && fa.len() + fb.len() > best {
                best = fa.len() + fb.len();
                best_pair = (fa.clone(), fb.clone());
            }
            if round + 1 == 400 {
                break;
            }
            // kick: drop a few members at random from both sides
            for _ in 0..(1 + rng.below(3)) {
                if fa.len() > 1 {
                    let i = rng.below(fa.len());
                    fa.remove(i);
                }
                if fb.len() > 1 {
                    let i = rng.below(fb.len());
                    fb.remove(i);
                }
            }
        }
    }

    println!("# u={u} r={r} ground={ground} restarts={restarts} seed={seed} mode={mode}");
    println!("#   candidate closed forms: 3r^2+1 = {}, 3*min(r^2,3r)+3 = {}",
             3 * r * r + 1,
             3 * std::cmp::min(r * r, 3 * r) + 3);
    println!("  best |A| + |B| found: {best}  (|A| = {}, |B| = {})  [{:.0}s]",
             best_pair.0.len(), best_pair.1.len(), t.elapsed().as_secs_f64());
    let sa: Vec<Vec<u32>> = best_pair.0.iter().map(|&c| mask_to_set(c)).collect();
    let sb: Vec<Vec<u32>> = best_pair.1.iter().map(|&c| mask_to_set(c)).collect();
    println!("    A = {sa:?}");
    println!("    B = {sb:?}");
    println!("  LOWER BOUND ONLY -- this search is stochastic, not exhaustive.");
}
