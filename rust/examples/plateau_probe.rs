//! Quality probe: unseeded plateau runs at parameters with a known
//! exhaustive maximum. `plateau_probe <b> <ground> <steps> <runs>`.
use sunflower_formal::plateau;
fn main() {
    let a: Vec<String> = std::env::args().skip(1).collect();
    let b: u32 = a[0].parse().unwrap();
    let g: u32 = a[1].parse().unwrap();
    let steps: u64 = a[2].parse().unwrap();
    let runs: u64 = a[3].parse().unwrap();
    let t = std::time::Instant::now();
    let mut best = 0;
    for s in 0..runs {
        let f = plateau::search(g, b, steps, 1000 + s, &[], true, |_, _| {});
        best = best.max(f.best);
    }
    println!("b={b} g={g} steps={steps} runs={runs}: best={best}  ({:.1}s)", t.elapsed().as_secs_f64());
}
