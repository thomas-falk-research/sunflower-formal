//! Is every 27-member 4-uniform 3-sunflower-free family on nine points
//! intersecting?
//!
//! The general census is a much larger search than the intersecting one,
//! but the *gap* between them is small and can be attacked directly. A
//! family that is not intersecting contains two disjoint members, and a
//! relabelling carries them onto `{0,1,2,3}` and `{4,5,6,7}` — sound,
//! since relabelling preserves uniformity, distinctness and
//! sunflower-freeness. So seeding the search with that pair and finding
//! nothing decides the question.
//!
//! Note what does *not* happen on nine points: three pairwise disjoint
//! 4-sets need twelve, so an empty-core sunflower cannot occur and
//! disjointness is not itself forbidden. The question is whether the
//! degree budget survives it.
//!
//! The same forced regularity as the intersecting census applies: every
//! degree is at most `g(3,8) = 12` and `4·27 = 108 = 9·12`, so the family
//! is exactly 12-regular.

const G: usize = 9;
const CAP: u32 = 12;

fn is_sunflower(a: u32, b: u32, c: u32) -> bool {
    let ab = a & b;
    ab == (a & c) && ab == (b & c)
}

struct S {
    target: usize,
    deg: [u32; G],
    found: usize,
    fams: Vec<Vec<u32>>,
    nodes: u64,
}

impl S {
    fn shift(&mut self, x: u32, up: bool) {
        for (p, d) in self.deg.iter_mut().enumerate() {
            if x >> p & 1 == 1 {
                if up {
                    *d += 1;
                } else {
                    *d -= 1;
                }
            }
        }
    }

    fn rec(&mut self, cands: &[u32], cur: &mut Vec<u32>) {
        self.nodes += 1;
        if cur.len() == self.target {
            self.found += 1;
            self.fams.push(cur.clone());
            return;
        }
        if cur.len() + cands.len() < self.target {
            return;
        }
        let mut avail = [0u32; G];
        for &c in cands {
            for (p, a) in avail.iter_mut().enumerate() {
                if c >> p & 1 == 1 {
                    *a += 1;
                }
            }
        }
        if (0..G).any(|p| self.deg[p] + avail[p] < CAP) {
            return;
        }
        for idx in 0..cands.len() {
            if cur.len() + (cands.len() - idx) < self.target {
                return;
            }
            let x = cands[idx];
            if (0..G).any(|p| x >> p & 1 == 1 && self.deg[p] >= CAP) {
                continue;
            }
            let next: Vec<u32> = cands[idx + 1..]
                .iter()
                .copied()
                .filter(|&y| !cur.iter().any(|&a| is_sunflower(a, x, y)))
                .collect();
            cur.push(x);
            self.shift(x, true);
            self.rec(&next, cur);
            self.shift(x, false);
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
    let a: u32 = 0b0000_1111; // {0,1,2,3}
    let b: u32 = 0b1111_0000; // {4,5,6,7}
    assert_eq!(a & b, 0, "the seed pair must be disjoint");
    let all: Vec<u32> = (0u32..(1 << G as u32))
        .filter(|x| x.count_ones() == 4 && *x != a && *x != b)
        .filter(|&y| !is_sunflower(a, b, y))
        .collect();
    let mut s = S { target, deg: [0; G], found: 0, fams: Vec::new(), nodes: 0 };
    let mut cur = vec![a, b];
    s.shift(a, true);
    s.shift(b, true);
    s.rec(&all, &mut cur);
    println!(
        "target {target} with a disjoint pair seeded: {} families, {} nodes",
        s.found, s.nodes
    );
    // Orbit count under the full symmetric group on the nine points.
    let ps = perms(G);
    let mut orbits: std::collections::HashSet<Vec<u32>> = std::collections::HashSet::new();
    for f in &s.fams {
        let w: Vec<u64> = f.iter().map(|&x| u64::from(x)).collect();
        sunflower_formal::wide::verify(&w, 4, false).expect("invalid family");
        orbits.insert(canon(f, &ps));
    }
    println!("orbits under S_{G} among these: {}", orbits.len());
    if s.found == 0 {
        println!("  => every {target}-member family on nine points IS intersecting,");
        println!("     so the intersecting census settles the general question too.");
    }
}
