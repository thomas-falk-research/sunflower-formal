//! How a cube's degree-sequence split distributes over a shorter prefix —
//! the measurement that says whether a `--seqprefix` is a usable
//! granularity, as opposed to how many pieces it makes.
//!
//! ```text
//!   cargo run --release --example seq_buckets -- 11 4 32 13
//! ```
//!
//! # Why the sub-cube count is not enough
//!
//! §49.2a chose a prefix per cube by keeping the sub-cube count under a
//! few hundred, on the evidence that 144 pieces beat the cube whole at ten
//! points and 1939 lost. That reads the split as a number of solver
//! startups, and startups are not what a hard cube costs. A prefix-`k`
//! sub-cube has to decide *everything underneath it*, so what it costs is
//! governed by how many full sub-cubes it covers — and that is wildly
//! uneven. At `(b,g,t) = (4,11,32)`, `deg(0) = 13`, prefix three makes 27
//! pieces, which looks ideal, and the largest of them covers 559 of the
//! 1949 full sub-cubes, which is a monolith with a small number written on
//! it. §52.2 is that mistake, made and paid for.
//!
//! Two things this prints that the count alone hides:
//!
//! * **the bucket sizes**, so the biggest piece can be costed against the
//!   per-sub-cube times the ladder files already record; and
//! * **the enumeration order**, because sub-cubes come out
//!   lexicographically descending and a budget-limited pass takes them in
//!   that order. If the big buckets are at the front, the pass spends its
//!   whole budget there and banks nothing — which is exactly what
//!   `docs/ladder/iota4_11.deg13.p3.tsv` recorded and did not explain.
//!
//! The split is a partition either way, so this changes no verdict; it
//! only says which granularity is worth spending a budget on.
use std::collections::BTreeMap;
use sunflower_formal::symbreak::{encode, sequence_cubes, SymOptions};

fn main() {
    let a: Vec<String> = std::env::args().collect();
    if a.len() < 5 {
        eprintln!("usage: seq_buckets <ground> <b> <target> <deg0> [prefix=3]");
        std::process::exit(2);
    }
    let g: u32 = a[1].parse().unwrap();
    let b: u32 = a[2].parse().unwrap();
    let t: usize = a[3].parse().unwrap();
    let d0: usize = a[4].parse().unwrap();
    let prefix: usize = a.get(5).map_or(3, |s| s.parse().unwrap());

    let o = SymOptions::default();
    let inst = encode(g, b, t, o);
    let cap = 10_000_000;
    let Some(full) = sequence_cubes(&inst, o, &[d0], g as usize, cap) else {
        println!("the full split of deg(0) = {d0} exceeds {cap}; nothing to bucket against");
        return;
    };
    let coarse = sequence_cubes(&inst, o, &[d0], prefix, cap).unwrap();

    let mut buckets: BTreeMap<Vec<usize>, usize> = BTreeMap::new();
    for (seq, _) in &full {
        *buckets.entry(seq[..prefix].to_vec()).or_insert(0) += 1;
    }
    println!(
        "b={b} ground={g} target={t} deg(0)={d0}: full split {} sub-cubes, \
         prefix-{prefix} split {}",
        full.len(),
        coarse.len()
    );
    println!("(all_points_used = {}, which is what the driver runs)", o.all_points_used);
    println!("\n idx  prefix-{prefix} cube          full sub-cubes underneath");
    let order: Vec<usize> =
        coarse.iter().map(|(s, _)| buckets[&s[..prefix].to_vec()]).collect();
    for (i, (s, _)) in coarse.iter().enumerate() {
        let n = buckets[&s[..prefix].to_vec()];
        let bar = "#".repeat((n * 40 / *order.iter().max().unwrap()).max(1));
        println!("  {i:3}  {:?}  {n:6}  {bar}", &s[..prefix]);
    }

    let mx = *order.iter().max().unwrap();
    let mean = full.len() as f64 / coarse.len() as f64;
    let front: usize = order.iter().take(4).sum();
    println!("\n  mean bucket        {mean:.1}");
    println!("  largest bucket     {mx}  (at index {})", order.iter().position(|&n| n == mx).unwrap());
    println!(
        "  first four         {front} of {} ({:.0}% of the cube in four pieces)",
        full.len(),
        100.0 * front as f64 / full.len() as f64
    );
    println!(
        "  singleton buckets  at indices {:?}",
        order.iter().enumerate().filter(|(_, &n)| n == 1).map(|(i, _)| i).collect::<Vec<_>>()
    );
    println!(
        "\n  READ IT LIKE THIS: a budget-limited pass takes these in index\n  \
         order. If the largest buckets are at the front, it spends the\n  \
         budget there and banks nothing. Cost the largest bucket against\n  \
         the per-sub-cube times in docs/ladder/ before choosing a prefix."
    );
}
