//! `g(m, n)`: the largest distinct `m`-uniform 3-sunflower-free family on
//! `n` points, exhaustively.
//!
//! Wanted for one purpose: the link of a point in a 4-uniform family on
//! nine points is a 3-uniform sunflower-free family on the other eight,
//! so `g(3,8)` is an upper bound on every point degree there. With
//! `sum of degrees = 4 * 27 = 108 = 9 * 12`, a bound of 12 would force
//! every 27-member family on nine points to be 12-regular.

fn is_sunflower(a: u64, b: u64, c: u64) -> bool {
    let ab = a & b;
    ab == (a & c) && ab == (b & c)
}

struct S {
    best: usize,
    best_fam: Vec<u64>,
    nodes: u64,
}

impl S {
    fn rec(&mut self, cands: &[u64], cur: &mut Vec<u64>) {
        self.nodes += 1;
        if cur.len() > self.best {
            self.best = cur.len();
            self.best_fam = cur.clone();
        }
        for i in 0..cands.len() {
            if cur.len() + (cands.len() - i) <= self.best {
                return;
            }
            let x = cands[i];
            let next: Vec<u64> = cands[i + 1..]
                .iter()
                .copied()
                .filter(|&y| !cur.iter().any(|&a| is_sunflower(a, x, y)))
                .collect();
            cur.push(x);
            self.rec(&next, cur);
            cur.pop();
        }
    }
}

fn main() {
    let m: u32 = std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(3);
    let n: u32 = std::env::args().nth(2).and_then(|s| s.parse().ok()).unwrap_or(8);
    let all: Vec<u64> = sunflower_formal::wide::subsets(n, m);
    let mut s = S { best: 0, best_fam: Vec::new(), nodes: 0 };
    let mut cur = Vec::new();
    s.rec(&all, &mut cur);
    println!("g({m},{n}) = {}   ({} candidates, {} nodes)", s.best, all.len(), s.nodes);
    let f: Vec<Vec<u32>> = s
        .best_fam
        .iter()
        .map(|&x| (0..n).filter(|i| x >> i & 1 == 1).collect())
        .collect();
    println!("  witness: {f:?}");
}
