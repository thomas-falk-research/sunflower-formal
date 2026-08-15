//! Every 27-member intersecting 3-sunflower-free 4-uniform family on nine
//! points, exhaustively, and how many there are up to relabelling.
//!
//! `Product.iota_four_at_least_27` exhibits one and
//! `Substitution.triangle_squared_is_maximal` shows it is maximal.
//! Neither says it is the only one. Five million random fills found 50
//! distinct 27-member families all lying in a single orbit, which is
//! evidence and not a census. This is the census.
//!
//! ## What makes it finish
//!
//! Regularity, forced. The link of a point is a 3-uniform sunflower-free
//! family on the other eight points, so every degree is at most
//! `g(3,8) = 12` — computed exhaustively by `examples/g_small.rs`. The
//! degree sum is `4 * 27 = 108 = 9 * 12`, so **every such family is
//! exactly 12-regular**, and a point that reaches degree 12 is closed to
//! every later member. That single constraint is what turns a search
//! that ran for 900 s without finishing into one that finishes.
//!
//! The anchor `{0,1,2,3}` is fixed throughout, sound because a
//! relabelling carries any member onto it and preserves everything. The
//! anchor's stabiliser has one orbit of second members per value of
//! `|B ∩ anchor| = 1, 2, 3`, so three second members meet every orbit.

use std::collections::HashSet;

use sunflower_formal::wide;

fn is_sunflower(a: u32, b: u32, c: u32) -> bool {
    let ab = a & b;
    ab == (a & c) && ab == (b & c)
}

const G: usize = 9;
const CAP: u32 = 12;

struct Census {
    inter: bool,
    target: usize,
    deg: [u32; G],
    found: Vec<Vec<u32>>,
    nodes: u64,
}

impl Census {
    fn place(&mut self, x: u32, add: bool) {
        for (p, d) in self.deg.iter_mut().enumerate() {
            if x >> p & 1 == 1 {
                if add {
                    *d += 1;
                } else {
                    *d -= 1;
                }
            }
        }
    }

    /// Every point must still be able to reach degree 12 using the
    /// candidates that remain.
    fn reachable(&self, cands: &[u32]) -> bool {
        let mut avail = [0u32; G];
        for &c in cands {
            for (p, a) in avail.iter_mut().enumerate() {
                if c >> p & 1 == 1 {
                    *a += 1;
                }
            }
        }
        (0..G).all(|p| self.deg[p] + avail[p] >= CAP)
    }

    fn rec(&mut self, cands: &[u32], cur: &mut Vec<u32>) {
        self.nodes += 1;
        if cur.len() == self.target {
            self.found.push(cur.clone());
            return;
        }
        if cur.len() + cands.len() < self.target || !self.reachable(cands) {
            return;
        }
        for idx in 0..cands.len() {
            if cur.len() + (cands.len() - idx) < self.target {
                return;
            }
            let x = cands[idx];
            // Degree cap: a point already at 12 admits nothing more.
            if (0..G).any(|p| x >> p & 1 == 1 && self.deg[p] >= CAP) {
                continue;
            }
            let next: Vec<u32> = cands[idx + 1..]
                .iter()
                .copied()
                .filter(|&y| (!self.inter || y & x != 0) && !cur.iter().any(|&a| is_sunflower(a, x, y)))
                .collect();
            cur.push(x);
            self.place(x, true);
            self.rec(&next, cur);
            self.place(x, false);
            cur.pop();
        }
    }
}

fn perms(n: usize) -> Vec<Vec<u8>> {
    let mut cur: Vec<u8> = (0..n as u8).collect();
    let mut out = vec![cur.clone()];
    loop {
        let Some(i) = (0..n - 1).rev().find(|&i| cur[i] < cur[i + 1]) else { return out };
        let j = (i + 1..n).rev().find(|&j| cur[j] > cur[i]).unwrap();
        cur.swap(i, j);
        cur[i + 1..].reverse();
        out.push(cur.clone());
    }
}

fn canon(f: &[u32], ps: &[Vec<u8>]) -> Vec<u32> {
    let mut best: Option<Vec<u32>> = None;
    let mut buf = vec![0u32; f.len()];
    for p in ps {
        for (slot, &m) in buf.iter_mut().zip(f) {
            let mut q = 0u32;
            let mut r = m;
            while r != 0 {
                q |= 1 << p[r.trailing_zeros() as usize];
                r &= r - 1;
            }
            *slot = q;
        }
        buf.sort_unstable();
        match &best {
            Some(b) if *b <= buf => {}
            _ => best = Some(buf.clone()),
        }
    }
    best.unwrap()
}

fn main() {
    let target: usize = std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(27);
    // Second argument: 1 = require intersecting, 0 = general families.
    // On nine points three pairwise disjoint 4-sets do not fit, so an
    // empty-core sunflower is impossible and a sunflower-free family here
    // need NOT be intersecting. The general census is the stronger one.
    let inter: bool = std::env::args().nth(2).map(|s| s != "0").unwrap_or(true);
    let b = 4u32;
    let anchor: u32 = (1u32 << b) - 1;
    let all: Vec<u32> = (0u32..(1u32 << G as u32))
        .filter(|x| x.count_ones() == b && *x != anchor && (!inter || x & anchor != 0))
        .collect();

    let mut c = Census { inter, target, deg: [0; G], found: Vec::new(), nodes: 0 };
    let jlo = if inter { 1 } else { 0 };
    for j in jlo..b {
        let mut rep: u32 = if j == 0 { 0 } else { (1u32 << j) - 1 };
        for t in 0..(b - j) {
            rep |= 1u32 << (b + t);
        }
        let sub: Vec<u32> = all
            .iter()
            .copied()
            .filter(|&y| y != rep && (!inter || y & rep != 0) && !is_sunflower(anchor, rep, y))
            .collect();
        let mut cur = vec![anchor, rep];
        c.deg = [0; G];
        c.place(anchor, true);
        c.place(rep, true);
        c.rec(&sub, &mut cur);
    }
    println!(
        "target {target}, {}: {} families found, {} nodes",
        if inter { "intersecting" } else { "general" },
        c.found.len(),
        c.nodes
    );
    for f in &c.found {
        let w: Vec<u64> = f.iter().map(|&x| u64::from(x)).collect();
        wide::verify(&w, b, inter).expect("census produced an invalid family");
    }
    let ps = perms(G);
    let mut orbits: HashSet<Vec<u32>> = HashSet::new();
    for f in &c.found {
        orbits.insert(canon(f, &ps));
    }
    println!("orbits under S_{G}: {}", orbits.len());
    for o in &orbits {
        println!("  {o:?}");
    }
}
