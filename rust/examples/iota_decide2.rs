//! Does `iota(4)` reach 32? Decision framing plus the second-member
//! orbit reduction.
//!
//! 32 is the value that would put `b = 4` above the Abbott-Hanson-Sauer
//! rate of `10^(1/2) = 3.1623`, since the rate is `iota(b)^(1/(b-1))`.
use sunflower_formal::intersecting::{iota, iota_decide, verify};

fn main() {
    let target: usize = std::env::args()
        .nth(1)
        .and_then(|s| s.parse().ok())
        .unwrap_or(32);
    let budget: u64 = std::env::args()
        .nth(2)
        .and_then(|s| s.parse().ok())
        .unwrap_or(4_000_000_000_000);

    // Agreement first. On the grounds where the plain maximum search
    // finishes, the decision search must give the same verdict at every
    // target -- the orbit reduction is the step most likely to be
    // subtly wrong, and this is what would catch it.
    for g in 5u32..=9 {
        let (exact, _, d1) = iota(g, 4, 40_000_000_000, 0);
        assert!(d1, "max search did not finish at ground {g}");
        for t in [2usize, 5, 10, 16, 24, 25, 27, 28, 32] {
            let (reached, fam, d2) = iota_decide(g, 4, t, 40_000_000_000);
            assert!(d2, "decide did not finish at ground {g}, target {t}");
            assert_eq!(
                reached,
                exact >= t,
                "decide says {reached} but iota(4,{g}) = {exact} against target {t}"
            );
            if reached {
                verify(&fam, 4, true).expect("bad witness");
                assert!(fam.len() >= t);
            }
        }
    }
    println!("agreement: decision search matches the maximum search, grounds 5-9");
    println!();
    println!(
        "b = 4, target {target} (rate {:.4}; AHS is 3.1623)",
        (target as f64).powf(1.0 / 3.0)
    );
    for g in 9u32..=13 {
        let t = std::time::Instant::now();
        let (reached, fam, done) = iota_decide(g, 4, target, budget);
        let secs = t.elapsed().as_secs_f64();
        if reached {
            verify(&fam, 4, true).expect("witness invalid");
            println!("  ground {g:>2}: FOUND {} members  ({secs:.0}s)", fam.len());
            println!(
                "    {:?}",
                fam.iter()
                    .map(|m| (0..16u32).filter(|x| m >> x & 1 == 1).collect::<Vec<_>>())
                    .collect::<Vec<_>>()
            );
            return;
        }
        println!(
            "  ground {g:>2}: no  ({})  ({secs:.0}s)",
            if done {
                "exhaustive"
            } else {
                "BUDGET EXHAUSTED -- inconclusive"
            },
            secs = secs
        );
        if !done {
            return;
        }
    }
}
