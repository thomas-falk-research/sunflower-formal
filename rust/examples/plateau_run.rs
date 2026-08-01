//! Long-running plateau search: `plateau_run <b> <ground> <steps> <seed> [log]`.
//!
//! Seeds from the best construction the repository can build at these
//! parameters (`iota_extend`'s families, restricted to the ground set when
//! they fit) and then walks. Every improvement is verified by
//! `intersecting::verify` and appended to the log immediately, so a run
//! killed by a container restart still leaves its record behind.
use std::io::Write;
use sunflower_formal::intersecting::{self, verify};
use sunflower_formal::plateau;
use sunflower_formal::structure;

/// Narrow a 128-bit family to `u32`, which is possible exactly when it
/// lives on at most 32 points.
fn narrow_128(f: &[u128]) -> Option<Vec<u32>> {
    if f.iter().any(|&s| s >> 32 != 0) {
        return None;
    }
    Some(f.iter().map(|&s| s as u32).collect())
}

/// The best seed available at `(b, ground)` from the constructions.
///
/// `iota(2) = 3` on three points and `iota(3) = 10` on six are the
/// exhaustive maxima the Abbott-Hanson-Sauer substitution is built from;
/// `substitute(G, H)` at `(a, b)` has `|G| * |H|^a` members on
/// `g_G * g_H` points.
fn seed_for(b: u32, ground: u32) -> Vec<u32> {
    let (_, i2, _) = intersecting::iota(3, 2, 10_000_000, 0);
    let (_, i3, _) = intersecting::iota(6, 3, 200_000_000, 0);
    // iota(4,9) = 27 is the substitution of the triangle into itself, so
    // build it rather than re-running the fifty-second exhaustive search
    // on every invocation.
    let i4: Vec<u32> = intersecting::substitute(&i2, 3, &i2, 3)
        .iter()
        .map(|&s| s as u32)
        .collect();
    let mut candidates: Vec<(Vec<u32>, u32, u32)> = vec![
        (i2.clone(), 2, 3),
        (i3.clone(), 3, 6),
        (i4.clone(), 4, 9),
    ];
    for (g, gg, h, hg) in [
        (&i2, 3u32, &i2, 3u32),
        (&i2, 3, &i3, 6),
        (&i3, 6, &i2, 3),
        (&i2, 3, &i4, 9),
        (&i4, 9, &i2, 3),
    ] {
        let fam = intersecting::substitute(g, gg, h, hg);
        let bb = (g[0].count_ones()) * (h[0].count_ones());
        if let Some(narrow) = narrow_128(&fam) {
            candidates.push((narrow, bb, gg * hg));
        }
    }
    let mut best: Vec<u32> = Vec::new();
    for (fam, fb, fg) in candidates {
        if fb == b && fg <= ground && fam.len() > best.len() && verify(&fam, b, true).is_ok() {
            best = fam;
        }
    }
    best
}

/// The best *general* (not necessarily intersecting) seed at
/// `(b, ground)`: the doubling of the best intersecting family, which is
/// `g(b) >= 2 iota(b)`.
fn general_seed_for(b: u32, ground: u32) -> Vec<u32> {
    let (_, i2, _) = intersecting::iota(3, 2, 10_000_000, 0);
    let (_, i3, _) = intersecting::iota(6, 3, 200_000_000, 0);
    let i4: Vec<u32> = intersecting::substitute(&i2, 3, &i2, 3)
        .iter()
        .map(|&s| s as u32)
        .collect();
    let mut best: Vec<u32> = Vec::new();
    for (fam, fb, fg) in [(i2, 2u32, 3u32), (i3, 3, 6), (i4, 4, 9)] {
        if fb != b || 2 * fg > ground {
            continue;
        }
        let doubled = intersecting::doubled(&fam, fg);
        if doubled.len() > best.len() && verify(&doubled, b, false).is_ok() {
            best = doubled;
        }
    }
    best
}

fn main() {
    let mut args = std::env::args().skip(1);
    let b: u32 = args.next().and_then(|s| s.parse().ok()).unwrap_or(4);
    let ground: u32 = args.next().and_then(|s| s.parse().ok()).unwrap_or(11);
    let steps: u64 = args.next().and_then(|s| s.parse().ok()).unwrap_or(100_000);
    let rng_seed: u64 = args.next().and_then(|s| s.parse().ok()).unwrap_or(1);
    let log = args.next().unwrap_or_else(|| "-".to_string());
    // A trailing "general" switches off the intersecting condition: the
    // cone gives `iota(b) >= g(b-1)`, so a large *general* family one
    // uniformity down beats 1972 exactly as an intersecting one here
    // would.
    let intersecting = args.next().as_deref() != Some("general");

    // Intersecting at uniformity b beats 1972 at 10^((b-1)/2); a general
    // family at uniformity b feeds the cone at b+1, so its threshold is
    // the one for b+1.
    let exponent = if intersecting { b as f64 - 1.0 } else { b as f64 };
    let target = (10f64.powf(exponent / 2.0)).floor() as usize + 1;
    let seed = if intersecting {
        seed_for(b, ground)
    } else {
        general_seed_for(b, ground)
    };

    let mut sink: Box<dyn Write> = if log == "-" {
        Box::new(std::io::stdout())
    } else {
        Box::new(
            std::fs::OpenOptions::new()
                .create(true)
                .append(true)
                .open(&log)
                .expect("cannot open log"),
        )
    };
    writeln!(
        sink,
        "# plateau b={b} ground={ground} steps={steps} rng={rng_seed} seed_family={} target={target} intersecting={intersecting}",
        seed.len()
    )
    .ok();
    sink.flush().ok();

    let t = std::time::Instant::now();
    let mut last = 0usize;
    let found = plateau::search(ground, b, steps, rng_seed, &seed, intersecting, |n, fam| {
        if n <= last {
            return;
        }
        last = n;
        verify(fam, b, intersecting).expect("plateau produced an invalid family");
        writeln!(
            sink,
            "{n}\t{:.0}s\tsupport={}\t{}",
            t.elapsed().as_secs_f64(),
            structure::support(fam).count_ones(),
            if n >= target { "*** BEATS 1972 ***" } else { "" }
        )
        .ok();
        // Dump the family on *every* improvement, not only on a record.
        // The first pass logged sizes alone and a killed run left a best
        // of 78 at b = 5 with no witness to show for it.
        writeln!(sink, "FAMILY {n} {fam:?}").ok();
        sink.flush().ok();
    });
    verify(&found.family, b, intersecting).expect("final family invalid");
    let rate = (found.best as f64).powf(1.0 / exponent);
    writeln!(
        sink,
        "# done b={b} ground={ground} best={} rate={rate:.4} steps={} {:.0}s",
        found.best,
        found.steps,
        t.elapsed().as_secs_f64()
    )
    .ok();
    // Always dump the final family: a run that did not beat the target
    // still produced the best object at these parameters, and losing it
    // to a container restart has happened before.
    writeln!(sink, "FINAL {:?}", found.family).ok();
    sink.flush().ok();
}
