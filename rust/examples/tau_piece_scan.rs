//! How large can the covering-number-3 piece be?
//!
//!     tau_piece_scan <m> <r> <g_lo> <g_hi> [budget]
//!
//! `CrossIntersecting.star_extremal_from_tau_three` leaves one constant
//! open at each uniformity: the largest `m`-uniform intersecting
//! Rao(`r`)-spread family whose covering number is at least 3. At `m = 3`
//! it is 10 and `TauThree.tau_three_bound` proves 16 without the Rao
//! condition at all. At `m = 4` there is no bound whatever without it
//! (`CrossIntersecting.tau_three_piece_unbounded_at_four`), and
//! `r_star_four_at_most_five_from_tau_three` turns the value 125 into
//! `r*(4,3) <= 5`.
//!
//! This searches for the maximum on a fixed ground set. A ground set is a
//! restriction, so every row is a **lower** bound on the true maximum
//! unless the search exhausts, and even an exhausted row only settles the
//! question on that ground.

use sunflower_formal::spread::{is_rao_spread, mask_to_set, Mask};

/// Covering number at least 3: no two points meet every member.
fn tau_at_least_three(fam: &[Mask], ground: u32) -> bool {
    for p in 0..ground {
        for q in p..ground {
            let cover = (1u32 << p) | (1u32 << q);
            if fam.iter().all(|&c| c as u32 & cover != 0) {
                return false;
            }
        }
    }
    true
}

fn main() {
    let a: Vec<String> = std::env::args().skip(1).collect();
    let m: u32 = a[0].parse().unwrap();
    let r: u64 = a[1].parse().unwrap();
    let lo: u32 = a[2].parse().unwrap();
    let hi: u32 = a[3].parse().unwrap();
    let budget: u64 = a.get(4).and_then(|s| s.parse().ok()).unwrap_or(u64::MAX);
    println!("# m={m} r={r}: the constant star_extremal_from_tau_three leaves open");
    println!("# star = r^(m-1) = {}", r.pow(m - 1));
    for g in lo..=hi {
        let blocks: Vec<Mask> = (0u32..(1u32 << g))
            .filter(|b| b.count_ones() == m)
            .map(|b| b as Mask)
            .collect();
        let mut best: Vec<Mask> = Vec::new();
        let mut cur: Vec<Mask> = Vec::new();
        let mut nodes: u64 = 0;
        let mut hit = false;
        let t = std::time::Instant::now();

        // Depth-first over the blocks in order, keeping the family
        // intersecting and Rao-spread at every step; tau >= 3 is not
        // monotone, so it is tested at every node rather than pruned on.
        fn rec(
            blocks: &[Mask],
            from: usize,
            m: u32,
            r: u64,
            g: u32,
            cur: &mut Vec<Mask>,
            best: &mut Vec<Mask>,
            nodes: &mut u64,
            budget: u64,
            hit: &mut bool,
        ) {
            *nodes += 1;
            if *nodes > budget {
                *hit = true;
                return;
            }
            if cur.len() > best.len() && tau_at_least_three(cur, g) {
                *best = cur.clone();
            }
            if cur.len() + (blocks.len() - from) <= best.len() {
                return;
            }
            for i in from..blocks.len() {
                if *hit {
                    return;
                }
                let x = blocks[i];
                if cur.iter().any(|&c| c & x == 0) {
                    continue;
                }
                cur.push(x);
                if is_rao_spread(m, cur, r, g) {
                    rec(blocks, i + 1, m, r, g, cur, best, nodes, budget, hit);
                }
                cur.pop();
            }
        }
        rec(
            &blocks, 0, m, r, g, &mut cur, &mut best, &mut nodes, budget, &mut hit,
        );

        println!(
            "  ground {g}: max = {}{}  ({nodes} nodes, {:.0}s)",
            best.len(),
            if hit { "  (TRUNCATED, lower bound)" } else { "  (exhausted on this ground)" },
            t.elapsed().as_secs_f64()
        );
        if !best.is_empty() {
            let sets: Vec<Vec<u32>> = best.iter().map(|&c| mask_to_set(c)).collect();
            println!("    witness: {sets:?}");
        }
        use std::io::Write;
        std::io::stdout().flush().ok();
    }
}
