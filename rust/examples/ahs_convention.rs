//! Which parameter convention does [Kup25] use for the [AHS72]
//! evaluation at uniformity 2, and does the quoted formula match this
//! repository's own Chvatal-Hanson table?
//!
//! It does, with the offset the survey's stated definition predicts:
//! [Kup25] forbids a Delta(s+1)-system, so its phi(2,s) is this
//! repository's f(2, s+1) - 1 = CH(s,s). Every s from 2 to 8 agrees.
//! See docs/references.md.
use sunflower_formal::chvatal_hanson::{ch, f_2_k};

fn quoted(s: u64) -> u64 {
    if s % 2 == 0 { s * (s + 1) } else { s * s + (s - 1) / 2 }
}

fn main() {
    println!("  s   [Kup25]'s quoted phi(2,s)   CH(s,s)   this repo's f(2,s+1)-1   agree");
    for s in 2u64..=8 {
        let q = quoted(s);
        let c = ch(s, s);
        let r = f_2_k(s + 1) - 1;
        println!("  {s}   {q:24}   {c:7}   {r:22}   {}", q == c && c == r);
    }
}
