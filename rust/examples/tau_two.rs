//! `tau = 2` at the `iota(4,11)` rung, reduced to a pair of 3-uniform
//! families and then decided exhaustively.
//!
//! ## The reduction
//!
//! Let `F` be 4-uniform, intersecting, sunflower-free on `[11]`, with a
//! 2-cover `{p, q}` — every member contains `p` or `q`. Split it:
//!
//! ```text
//!   S_p = members containing p        C = members containing both
//!   S_q = members containing q        |F| = |S_p| + |S_q| - |C|
//! ```
//!
//! and take links:
//!
//! ```text
//!   X = { A \ {p} : A in S_p \ C }    3-sets on the other nine points
//!   Y = { B \ {q} : B in S_q \ C }    3-sets on the other nine points
//!   D = { A \ {p,q} : A in C }        2-sets on the other nine points
//!   |F| = |X| + |Y| + |C|
//! ```
//!
//! Three facts make this a small problem.
//!
//! 1. **`F` is sunflower-free iff `L_p` and `L_q` are.** A triple whose
//!    members do not all share `p` and do not all share `q` can never be
//!    a sunflower: two of them meet in something containing `p` (or `q`)
//!    while a third intersection does not, so the three pairwise
//!    intersections cannot coincide. Checked exhaustively over the mixed
//!    shapes — 67 375 triples, zero sunflowers — in
//!    `rust/tests/tau_two.rs`. So there are no constraints coupling the
//!    two sides beyond the ones below.
//!
//! 2. **`X` and `Y` are cross-intersecting.** `A` in `S_p \ C` has no `q`
//!    and `B` in `S_q \ C` has no `p`, so `A ∩ B` lies outside `{p, q}`,
//!    and it is non-empty because `F` is intersecting.
//!
//! 3. **`|C| ≤ g(2) = 6`.** Members of `C` all contain `{p, q}`, so a
//!    sunflower among them is exactly a sunflower among the 2-sets `D`,
//!    and the largest sunflower-free graph has six edges (two triangles).
//!
//! Hence `|F| ≤ max(|X| + |Y|) + 6`, the maximum being over
//! cross-intersecting pairs of sunflower-free 3-uniform families on nine
//! points. **If that maximum is at most 25, then `|F| ≤ 31 < 32` and
//! `tau = 2` cannot host the 32-member family the rung is looking for.**
//!
//! ## What this program does
//!
//! Computes `max(|X| + |Y|)` exactly. It branches over `X` only, and
//! scores each `X` by `maxSF(N(X))` — the largest sunflower-free family
//! among the triples still meeting all of `X`. Nothing is lost by not
//! branching on `Y`: for a fixed `X` the best `Y` *is* `maxSF(N(X))`, and
//! a 3-set is allowed to sit in both sides, since `{p} ∪ T` and
//! `{q} ∪ T` are different members of `F`.
//!
//! A first version branched over all four states per candidate — neither,
//! `X` only, `Y` only, both. It agrees with this one on `n = 5, 6, 7`
//! (12, 20, 20), which is how this one was checked, and it is far slower:
//! at `n = 7` it took 6 502 694 424 nodes and 293 s against 203 622 nodes
//! and 20 s here. The difference is the bound in `Search`.
//!
//! Both are deliberately different from the SAT route in
//! `tools/tau2.py`, so the routes are an independent check on each other
//! rather than one restating the other.
//!
//! Run:
//!
//! ```text
//!   cargo run --release --example tau_two -- 9         # exact max at n = 9
//!   cargo run --release --example tau_two -- 9 25      # only: does it exceed 25?
//!   cargo run --release --example tau_two -- 5 6 7 8 9 # the whole pattern
//! ```
//!
//! ## The floor
//!
//! A second argument seeds `best` with a floor. The search then only ever
//! looks for something that *beats* it, so the bound prunes from the first
//! node instead of having to climb. For the rung the question is not what
//! the maximum is but whether it can reach 26, so
//! `-- 9 25` decides `tau = 2` and is far cheaper than computing the exact
//! value. If it reports no improvement, `max(|X|+|Y|) <= 25` and hence
//! `|F| <= 31 < 32`.

fn is_sunflower(a: u32, b: u32, c: u32) -> bool {
    let ab = a & b;
    ab == (a & c) && ab == (b & c)
}

/// Triples of `[n]` as bitmasks, in a fixed order.
fn triples(n: u32) -> Vec<u32> {
    let mut out = Vec::new();
    for a in 0..n {
        for b in a + 1..n {
            for c in b + 1..n {
                out.push(1 << a | 1 << b | 1 << c);
            }
        }
    }
    out
}

/// The largest sunflower-free subfamily of `cands`, exactly. Used both as
/// the per-side cap and, on the full candidate set, as `g(3,n)`.
fn max_sunflower_free(cands: &[u32]) -> usize {
    fn rec(cands: &[u32], cur: &mut Vec<u32>, best: &mut usize) {
        if cur.len() > *best {
            *best = cur.len();
        }
        for i in 0..cands.len() {
            if cur.len() + (cands.len() - i) <= *best {
                return;
            }
            let x = cands[i];
            let next: Vec<u32> = cands[i + 1..]
                .iter()
                .copied()
                .filter(|&y| !cur.iter().any(|&a| is_sunflower(a, x, y)))
                .collect();
            cur.push(x);
            rec(&next, cur, best);
            cur.pop();
        }
    }
    let mut best = 0;
    rec(cands, &mut Vec::new(), &mut best);
    best
}

/// Search over `X` alone, scoring each `X` by the largest sunflower-free
/// family that still meets all of it.
///
/// The bound that makes this finish: for any extension `X'` of the current
/// `X`, every admissible `Y` for `X'` is also admissible for `X`, because
/// `N(X') ⊆ N(X)`. So
///
/// ```text
///   |X'| + |Y| <= |X| + |avail| + maxSF(N(X))
/// ```
///
/// where `avail` is what can still be added to `X`. `maxSF(N(X))` collapses
/// quickly as `X` grows — that is the cross-intersecting condition doing the
/// work — so the bound bites early.
struct Search {
    trip: Vec<u32>,
    cap: usize, // g(3,n): neither side can exceed it
    best: usize,
    best_pair: (Vec<u32>, Vec<u32>),
    nodes: u64,
    maxsf_calls: u64,
}

impl Search {
    /// `avail` are the triples that may still join `X` (index-ordered, all
    /// sunflower-compatible with `X`).
    fn rec(&mut self, avail: &[u32], x: &mut Vec<u32>) {
        self.nodes += 1;

        // Everything still meeting all of X is a candidate for Y.
        let nx: Vec<u32> = self
            .trip
            .iter()
            .copied()
            .filter(|&u| x.iter().all(|&t| t & u != 0))
            .collect();
        self.maxsf_calls += 1;
        let y_cap = max_sunflower_free(&nx).min(self.cap);

        if x.len() + y_cap > self.best {
            self.best = x.len() + y_cap;
            // recover an actual optimal Y, not just its size
            let y = argmax_sunflower_free(&nx, y_cap);
            self.best_pair = (x.clone(), y);
        }

        // Bound for every extension of X.
        if x.len() + avail.len() + y_cap <= self.best {
            return;
        }

        for i in 0..avail.len() {
            if x.len() + (avail.len() - i) + y_cap <= self.best {
                return;
            }
            if x.len() >= self.cap {
                return;
            }
            let t = avail[i];
            let next: Vec<u32> = avail[i + 1..]
                .iter()
                .copied()
                .filter(|&u| !x.iter().any(|&a| is_sunflower(a, t, u)))
                .collect();
            x.push(t);
            self.rec(&next, x);
            x.pop();
        }
    }
}

/// A sunflower-free subfamily of `cands` of size exactly `want`.
fn argmax_sunflower_free(cands: &[u32], want: usize) -> Vec<u32> {
    fn rec(cands: &[u32], cur: &mut Vec<u32>, want: usize, out: &mut Option<Vec<u32>>) {
        if out.is_some() {
            return;
        }
        if cur.len() == want {
            *out = Some(cur.clone());
            return;
        }
        for i in 0..cands.len() {
            if cur.len() + (cands.len() - i) < want {
                return;
            }
            let x = cands[i];
            let next: Vec<u32> = cands[i + 1..]
                .iter()
                .copied()
                .filter(|&y| !cur.iter().any(|&a| is_sunflower(a, x, y)))
                .collect();
            cur.push(x);
            rec(&next, cur, want, out);
            cur.pop();
            if out.is_some() {
                return;
            }
        }
    }
    let mut out = None;
    rec(cands, &mut Vec::new(), want, &mut out);
    out.unwrap_or_default()
}

fn decode(m: u32, n: u32) -> Vec<u32> {
    (0..n).filter(|&i| m >> i & 1 == 1).collect()
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let nums: Vec<u32> = args.iter().filter_map(|a| a.parse().ok()).collect();
    // "n floor" if exactly two arguments and the second is bigger than any
    // plausible ground set; otherwise a list of ground-set sizes.
    let (ns, floor): (Vec<u32>, usize) = match nums.len() {
        0 => (vec![9], 0),
        2 if nums[1] > 20 => (vec![nums[0]], nums[1] as usize),
        _ => (nums.clone(), 0),
    };

    for n in ns {
        let trip = triples(n);
        let cap = max_sunflower_free(&trip);
        let t0 = std::time::Instant::now();
        let mut s = Search {
            trip: trip.clone(),
            cap,
            best: floor,
            best_pair: (vec![], vec![]),
            nodes: 0,
            maxsf_calls: 0,
        };
        s.rec(&trip.clone(), &mut Vec::new());
        let (x, y) = &s.best_pair;

        // Re-verify the optimum as a pair of families, independently of
        // the search that produced it.
        let sf_free = |f: &[u32]| {
            !(0..f.len()).any(|a| {
                (a + 1..f.len())
                    .any(|b| (b + 1..f.len()).any(|c| is_sunflower(f[a], f[b], f[c])))
            })
        };
        let cross = x.iter().all(|&a| y.iter().all(|&b| a & b != 0));

        println!("n = {n}   g(3,{n}) = {cap}   candidates = {}", trip.len());
        if floor > 0 {
            let beaten = s.best > floor;
            println!(
                "  floor {floor}: {}   nodes = {}   maxSF calls = {}   {:.1}s",
                if beaten {
                    format!("BEATEN, reached {}", s.best)
                } else {
                    format!("not beaten, so max(|X|+|Y|) <= {floor}")
                },
                s.nodes,
                s.maxsf_calls,
                t0.elapsed().as_secs_f64()
            );
            if !beaten {
                println!(
                    "  => tau=2 gives |F| <= {floor} + g(2) = {} < 32   TAU=2 CANNOT HOST 32",
                    floor + 6
                );
                println!();
                continue;
            }
        }
        println!(
            "  max(|X|+|Y|) = {}   ({} + {})   nodes = {}   maxSF calls = {}   {:.1}s",
            s.best,
            x.len(),
            y.len(),
            s.nodes,
            s.maxsf_calls,
            t0.elapsed().as_secs_f64()
        );
        println!(
            "  re-checked: X sunflower-free = {}, Y sunflower-free = {}, cross-intersecting = {}",
            sf_free(x),
            sf_free(y),
            cross
        );
        assert!(sf_free(x) && sf_free(y) && cross, "the optimum is not a valid pair");
        if n == 9 {
            let verdict = if s.best + 6 < 32 { "KILLS 32" } else { "does NOT kill 32" };
            println!(
                "  => tau=2 gives |F| <= max(|X|+|Y|) + g(2) = {} + 6 = {}   {}",
                s.best,
                s.best + 6,
                verdict
            );
        }
        println!(
            "  X = {:?}",
            x.iter().map(|&m| decode(m, n)).collect::<Vec<_>>()
        );
        println!(
            "  Y = {:?}",
            y.iter().map(|&m| decode(m, n)).collect::<Vec<_>>()
        );
        println!();
    }
}
