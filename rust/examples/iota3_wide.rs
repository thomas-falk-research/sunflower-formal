//! `iota(3) = 10`: the support bound plus one exhaustive search.
//!
//! An 11-member intersecting 3-uniform sunflower-free family would have
//! support at most `3 + 2*10 = 23` (`Ground.iota_support_bound`), so the
//! whole unbounded question is this one query.
use std::io::Write;
use sunflower_formal::wide;
fn main() {
    for (b, n) in [(3u32, 11u32), (3, 12)] {
        let g = wide::support_bound(b, n);
        let t = std::time::Instant::now();
        let (found, fam, done) = wide::iota_decide(g, b, n as usize, 200_000_000_000);
        println!(
            "iota({b}) >= {n}?  ground bound {g}: found={found} exhaustive={done}  ({:.0}s)",
            t.elapsed().as_secs_f64()
        );
        if found {
            wide::verify(&fam, b, true).expect("witness invalid");
            println!("  WITNESS {:?}", fam);
        }
        std::io::stdout().flush().ok();
    }
}
