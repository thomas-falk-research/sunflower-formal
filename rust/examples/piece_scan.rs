//! How much slack is in `intersecting_piece_bound`?
//!
//!     piece_scan <m> <r> <g_lo> <g_hi> [budget]

use sunflower_formal::rstar::max_intersecting_piece;
use sunflower_formal::spread::mask_to_set;

fn main() {
    let a: Vec<String> = std::env::args().skip(1).collect();
    let m: u32 = a[0].parse().unwrap();
    let r: u64 = a[1].parse().unwrap();
    let lo: u32 = a[2].parse().unwrap();
    let hi: u32 = a[3].parse().unwrap();
    let budget: u64 = a.get(4).and_then(|s| s.parse().ok()).unwrap_or(u64::MAX);
    let bound = r.pow(m - 1) + u64::from((m - 1) * (m - 1)) * r.pow(m - 2);
    println!("# m={m} r={r}: intersecting_piece_bound = {bound}, star = {}", r.pow(m - 1));
    for g in lo..=hi {
        let t = std::time::Instant::now();
        let (best, fam, nodes, exh) = max_intersecting_piece(m, r, g, budget);
        println!(
            "  ground {g}: max = {best}{}  (bound {bound}, {nodes} nodes, {:.0}s)",
            if exh { "" } else { " (TRUNCATED, lower bound)" },
            t.elapsed().as_secs_f64()
        );
        if exh {
            let sets: Vec<Vec<u32>> = fam.iter().map(|&c| mask_to_set(c)).collect();
            println!("    witness: {sets:?}");
        }
        use std::io::Write;
        std::io::stdout().flush().ok();
    }
}
