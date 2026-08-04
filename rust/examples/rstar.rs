//! Drive the `r*(m,3)` search.
//!
//!     cargo run --release --example rstar -- <m> <r> <ground> [nu] [lazy] [seconds]
//!
//! Prints one line per question and, for a counterexample, dumps the
//! family so it survives a container restart.

use sunflower_formal::rstar::{decide, encode, Outcome, Question, Ternary};
use sunflower_formal::spread::mask_to_set;

fn main() {
    let a: Vec<String> = std::env::args().skip(1).collect();
    if a.len() < 3 {
        eprintln!("usage: rstar <m> <r> <ground> [nu=2] [eager|lazy] [seconds=0]");
        std::process::exit(2);
    }
    let m: u32 = a[0].parse().unwrap();
    let r: u64 = a[1].parse().unwrap();
    let ground: u32 = a[2].parse().unwrap();
    let nu: usize = a.get(3).and_then(|s| s.parse().ok()).unwrap_or(2);
    let ternary = match a.get(4).map(|s| s.as_str()) {
        Some("lazy") => Ternary::Lazy,
        _ => Ternary::Eager,
    };
    let seconds: u64 = a.get(5).and_then(|s| s.parse().ok()).unwrap_or(0);

    let mut q = Question::new(m, r, ground);
    q.nu = nu;
    q.ternary = ternary;

    let t = std::time::Instant::now();
    let inst = encode(&q);
    eprintln!(
        "[encode] {} sets, {} vars, {} clauses ({} binary, {} ternary) in {:.1}s",
        inst.sets.len(),
        inst.cnf.nvars,
        inst.cnf.clauses.len(),
        inst.binary_clauses,
        inst.ternary_clauses,
        t.elapsed().as_secs_f64()
    );
    drop(inst);

    let rep = decide(&q, seconds).expect("solver");
    println!("{}", rep.line());
    if let Outcome::Counterexample(f) = &rep.outcome {
        println!("family ({} members):", f.len());
        for &c in f {
            println!("  {:?}", mask_to_set(c));
        }
        println!("masks: {:?}", f);
    }
}
