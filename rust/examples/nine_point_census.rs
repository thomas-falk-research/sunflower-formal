//! Every 27-member intersecting sunflower-free 4-uniform family on nine
//! points, exhaustively, and how many there are up to relabelling.
//!
//! `Product.iota_four_at_least_27` exhibits one such family and
//! `Substitution.triangle_squared_is_maximal` shows it is maximal.
//! Neither says it is the only one. A random fill reaches 27 about
//! nineteen times in a million and every hit so far has been a
//! relabelling of `Product.iota4`, which is evidence and not a census.
//! This is the census.
//!
//! The anchor `{0,1,2,3}` is fixed throughout, which is sound because a
//! relabelling carries any member onto it and preserves uniformity,
//! distinctness, intersecting-ness and sunflower-freeness. So every
//! family on nine points of size `target` has a relabelling that this
//! search visits.

use std::collections::HashSet;

use sunflower_formal::wide;

fn is_sunflower(a: u32, b: u32, c: u32) -> bool {
    let ab = a & b;
    ab == (a & c) && ab == (b & c)
}

/// The pairs of a `b`-set, as indices into a `ground x ground` table.
fn pairs_of(m: u32, ground: u32) -> Vec<usize> {
    let pts: Vec<u32> = (0..ground).filter(|&i| m >> i & 1 == 1).collect();
    let mut out = Vec::new();
    for i in 0..pts.len() {
        for j in i + 1..pts.len() {
            out.push((pts[i] * ground + pts[j]) as usize);
        }
    }
    out
}

struct Census {
    target: usize,
    ground: u32,
    /// `Support.link_at_pair_bounded` with `GAtMost 2 6`: the link of a
    /// 2-set is a 2-uniform sunflower-free family, so a pair lies in at
    /// most `g(2) = 6` members. Kernel-backed, and the only prune here
    /// that is not pure bookkeeping.
    pair_cap: u32,
    pair_count: Vec<u32>,
    slack: u32,
    per_member: u32,
    found: Vec<Vec<u32>>,
    nodes: u64,
}

impl Census {
    fn place(&mut self, x: u32, add: bool) {
        for p in pairs_of(x, self.ground) {
            if add {
                self.pair_count[p] += 1;
                self.slack -= 1;
            } else {
                self.pair_count[p] -= 1;
                self.slack += 1;
            }
        }
    }

    fn fits(&self, x: u32) -> bool {
        pairs_of(x, self.ground)
            .into_iter()
            .all(|p| self.pair_count[p] < self.pair_cap)
    }

    fn rec(&mut self, cands: &[u32], cur: &mut Vec<u32>) {
        self.nodes += 1;
        if cur.len() == self.target {
            self.found.push(cur.clone());
            return;
        }
        let need = (self.target - cur.len()) as u32;
        if need * self.per_member > self.slack {
            return;
        }
        for idx in 0..cands.len() {
            if cur.len() + (cands.len() - idx) < self.target {
                return;
            }
            let x = cands[idx];
            if !self.fits(x) {
                continue;
            }
            let next: Vec<u32> = cands[idx + 1..]
                .iter()
                .copied()
                .filter(|&y| y & x != 0 && !cur.iter().any(|&a| is_sunflower(a, x, y)))
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
            Some(bst) if *bst <= buf => {}
            _ => best = Some(buf.clone()),
        }
    }
    best.unwrap()
}

fn main() {
    let mut a = std::env::args().skip(1);
    let ground: u32 = a.next().and_then(|s| s.parse().ok()).unwrap_or(9);
    let b: u32 = a.next().and_then(|s| s.parse().ok()).unwrap_or(4);
    let target: usize = a.next().and_then(|s| s.parse().ok()).unwrap_or(27);

    let anchor: u32 = (1u32 << b) - 1;
    let cands: Vec<u32> = (0u32..(1u32 << ground))
        .filter(|x| x.count_ones() == b && *x != anchor && x & anchor != 0)
        .collect();
    let per_member = (b * (b - 1) / 2) as u32;
    let pair_cap = 6u32; // g(2) = 6
    let npairs = (ground * (ground - 1) / 2) as u32;

    // The stabiliser of the anchor has one orbit on candidates per value
    // of |B ∩ anchor| = 1, ..., b-1, so every family containing the
    // anchor has a relabelling containing the anchor and one of these
    // `b-1` representatives. That covers every orbit under S_ground,
    // which is what the census is counting.
    let mut c = Census {
        target,
        ground,
        pair_cap,
        pair_count: vec![0; (ground * ground) as usize],
        slack: npairs * pair_cap,
        per_member,
        found: Vec::new(),
        nodes: 0,
    };
    for j in 1..b {
        if b + (b - j) > ground {
            continue;
        }
        let mut rep: u32 = (1u32 << j) - 1;
        for t in 0..(b - j) {
            rep |= 1u32 << (b + t);
        }
        let sub: Vec<u32> = cands
            .iter()
            .copied()
            .filter(|&y| y != rep && y & rep != 0 && !is_sunflower(anchor, rep, y))
            .collect();
        let mut cur = vec![anchor, rep];
        c.pair_count.iter_mut().for_each(|v| *v = 0);
        c.slack = npairs * pair_cap;
        c.place(anchor, true);
        c.place(rep, true);
        c.rec(&sub, &mut cur);
    }
    println!(
        "ground={ground} b={b} target={target}: {} families found, {} nodes",
        c.found.len(),
        c.nodes
    );
    for f in &c.found {
        let w: Vec<u64> = f.iter().map(|&x| u64::from(x)).collect();
        wide::verify(&w, b, true).expect("census produced an invalid family");
    }
    let ps = perms(ground as usize);
    let mut orbits: HashSet<Vec<u32>> = HashSet::new();
    for f in &c.found {
        orbits.insert(canon(f, &ps));
    }
    println!("orbits under S_{ground}: {}", orbits.len());
    for o in &orbits {
        println!("  {o:?}");
    }
}
