//! Search over **generator programs** rather than over families.
//!
//! `plateau.rs` searched over families: perturb the members and keep
//! what scores better. §20.6 measured what that costs — five parameter
//! rows, hundreds of thousands of moves, and **four of the five never
//! left their seed**. The 1972 families are not merely maximal, they are
//! *isolated*, and an isolated optimum is exactly where moving the object
//! fails and changing the program that emits it can work.
//!
//! So: a generator is a small parameterised program that emits a **pool**
//! of candidate blocks, and its score is the largest verified
//! intersecting sunflower-free subfamily inside that pool. The pool is
//! the hypothesis ("a record family looks like *this kind* of object");
//! the subfamily search is the evaluation. Two generators are compared on
//! one number, so structurally unrelated constructions — a grid of
//! transversals, a cyclic difference family, a geometry, a complementary
//! selection — sit on the same scale.
//!
//! The evaluation reuses [`orbit::search_orbits`] with singleton orbits,
//! which is a max-clique-shaped branch and bound with the ternary
//! sunflower condition checked incrementally, already differentially
//! tested against `intersecting::iota`. Nothing new is trusted: every
//! family that comes out goes through [`orbit::verify`], which shares no
//! code with the search.
//!
//! # Where to point it
//!
//! Sunflower-freeness caps the degree of a `(b-2)`-set at 6 — the link is
//! a graph with `Δ <= 2` (from the `(b-1)`-set cap of 2) and `ν <= 2`
//! (`LinkCharacterisation`), so it is at most two disjoint triangles.
//! Counting members against the `(b-2)`-sets they contain gives
//!
//! ```text
//!     |F| <= (6 / C(b,2)) * C(n, b-2)
//! ```
//!
//! which at `b = 5` is `0.6 * C(n,3)`: 72 at ten points, 99 at eleven,
//! 132 at twelve. **So `iota(5) >= 101` is impossible below twelve
//! points**, and §9's `b = 5` SAT row — run at ground 10 — was asked at a
//! ground that provably cannot hold a record. [`link_bound`] computes it.

use crate::orbit;

/// The `(b-1)`-set bound: `deg <= 2` for every `(b-1)`-set, and each
/// member contains `b` of them.
pub fn top_link_bound(b: u64, n: u64) -> u64 {
    2 * binom(n, b - 1) / b
}

/// The `(b-2)`-set bound: `deg <= 6`, and each member contains `C(b,2)`
/// of them. Sharper than [`top_link_bound`] at every `n` that matters at
/// `b = 4` and `b = 5`.
pub fn link_bound(b: u64, n: u64) -> u64 {
    if b < 2 {
        return binom(n, b);
    }
    6 * binom(n, b - 2) / binom(b, 2)
}

/// The smaller of the two link bounds — what a family on `n` points can
/// possibly have.
pub fn size_ceiling(b: u64, n: u64) -> u64 {
    top_link_bound(b, n).min(link_bound(b, n)).min(binom(n, b))
}

/// The least ground set that could hold `target` members at uniformity
/// `b`, per [`size_ceiling`].
pub fn least_ground(b: u64, target: u64) -> u64 {
    let mut n = b;
    while size_ceiling(b, n) < target {
        n += 1;
        if n > 64 {
            return u64::MAX;
        }
    }
    n
}

pub fn binom(n: u64, k: u64) -> u64 {
    if k > n {
        return 0;
    }
    let mut r: u64 = 1;
    for i in 0..k {
        r = r * (n - i) / (i + 1);
    }
    r
}

/// One generator program: a name, the ground set it lives on, and the
/// pool of blocks it admits.
#[derive(Debug, Clone)]
pub struct Pool {
    pub name: String,
    pub ground: u32,
    pub b: u32,
    pub blocks: Vec<u64>,
}

/// What evaluating a pool found.
#[derive(Debug, Clone)]
pub struct Score {
    pub name: String,
    pub ground: u32,
    pub b: u32,
    pub pool: usize,
    /// Largest verified intersecting sunflower-free subfamily found.
    pub best: usize,
    pub family: Vec<u64>,
    pub exhaustive: bool,
    pub nodes: u64,
    pub seconds: f64,
}

impl Score {
    pub fn line(&self) -> String {
        format!(
            "{:<34} b={} g={:2} pool={:5} best={:4} {} {:.1}s",
            self.name,
            self.b,
            self.ground,
            self.pool,
            self.best,
            if self.exhaustive { "exhausted" } else { "truncated" },
            self.seconds
        )
    }
}

/// Evaluate a pool: the largest intersecting sunflower-free subfamily it
/// contains, verified from scratch.
///
/// [`orbit::search_orbits`] is a **decision** procedure — its bound is
/// "what is in hand plus everything still to come", so it prunes at the
/// root whenever the pool cannot reach the target and its `best` is then
/// not the maximum but whatever it happened to walk past. Turning it
/// into a maximiser means asking one decidable question at a time:
/// succeed at `t`, ask `t+1`; fail exhaustively at `t`, and the maximum
/// is `t-1` because `t-1` succeeded. The bound stays sharp at every
/// step, which is the whole reason not to just remove it.
pub fn evaluate(pool: &Pool, floor: usize, budget: u64) -> Score {
    let started = std::time::Instant::now();
    let singletons: Vec<Vec<u64>> = pool.blocks.iter().map(|&x| vec![x]).collect();
    let mut t = floor.max(1);
    let mut best = 0usize;
    let mut family: Vec<u64> = Vec::new();
    let mut exhaustive = true;
    let mut nodes = 0u64;
    loop {
        if t > pool.blocks.len() {
            break;
        }
        let res = orbit::search_orbits(&singletons, t, true, budget);
        nodes += res.nodes;
        if res.best >= t {
            best = res.best;
            family = res.best_family;
            t = best + 1;
        } else {
            exhaustive = res.exhaustive;
            break;
        }
    }
    if !family.is_empty() {
        orbit::verify(&family, pool.b, true)
            .expect("a pool produced a family that does not verify");
    }
    Score {
        name: pool.name.clone(),
        ground: pool.ground,
        b: pool.b,
        pool: pool.blocks.len(),
        best,
        family,
        exhaustive,
        nodes,
        seconds: started.elapsed().as_secs_f64(),
    }
}

/* ------------------------------------------------------------------ */
/* The generators.                                                     */
/* ------------------------------------------------------------------ */

fn subsets_of_size(ground: u32, b: u32) -> Vec<u64> {
    let mut out = Vec::new();
    for s in 0u64..(1u64 << ground) {
        if s.count_ones() == b {
            out.push(s);
        }
    }
    out
}

/// Everything. The control: any structured pool that scores below this
/// is a worse hypothesis than "no hypothesis", and this is also what the
/// unrestricted search sees.
pub fn all_blocks(ground: u32, b: u32) -> Pool {
    Pool {
        name: "all b-subsets".into(),
        ground,
        b,
        blocks: subsets_of_size(ground, b),
    }
}

/// **Transversals of an `a x m` grid**: the graphs of the functions
/// `[a] -> [m]`, as `a`-subsets of the `a*m` points. Two of them meet
/// exactly where the functions agree, so the family is a *code* and the
/// sunflower condition is a condition on agreement patterns.
///
/// This is the shape every product construction in the catalogue has,
/// written so the pool can be searched directly rather than assembled.
pub fn transversals(a: u32, m: u32) -> Pool {
    let mut blocks = Vec::new();
    let total = (m as u64).pow(a);
    for code in 0..total {
        let mut x = code;
        let mut set = 0u64;
        for i in 0..a {
            let v = (x % m as u64) as u32;
            x /= m as u64;
            set |= 1u64 << (i * m + v);
        }
        blocks.push(set);
    }
    Pool {
        name: format!("transversals {a}x{m}"),
        ground: a * m,
        b: a,
        blocks,
    }
}

/// **Twisted transversals**: the graphs of functions whose values sum to
/// a fixed residue modulo `q`. A cocycle condition on the product — the
/// algebraic move behind the modern cap-set constructions, and the one
/// thing §5 says is *not* in this repository's catalogue of `cone`,
/// `double` and `substitute`.
pub fn twisted_transversals(a: u32, m: u32, q: u32, c: u32) -> Pool {
    let mut blocks = Vec::new();
    let total = (m as u64).pow(a);
    for code in 0..total {
        let mut x = code;
        let mut set = 0u64;
        let mut sum = 0u32;
        for i in 0..a {
            let v = (x % m as u64) as u32;
            x /= m as u64;
            sum += v * (i + 1); // weighted, so the twist is not a translation
            set |= 1u64 << (i * m + v);
        }
        if sum % q == c {
            blocks.push(set);
        }
    }
    Pool {
        name: format!("twisted {a}x{m} sum*i = {c} mod {q}"),
        ground: a * m,
        b: a,
        blocks,
    }
}

/// **Complementary selection**: on `2b` points, one block from each
/// complementary pair, chosen by a parity rule. Automatically
/// intersecting, and it is the shape of `iota(3) = 10` — the 2-(6,3,2)
/// design is exactly "one triple from each complementary pair of [6]".
pub fn complementary_half(b: u32, weight_mod: u32, residue: u32) -> Pool {
    let ground = 2 * b;
    let mut blocks = Vec::new();
    for s in subsets_of_size(ground, b) {
        let comp = ((1u64 << ground) - 1) ^ s;
        if comp < s {
            continue; // visit each complementary pair once, at its smaller half
        }
        let w: u32 = (0..ground).filter(|i| s >> i & 1 == 1).map(|i| i + 1).sum();
        blocks.push(if w % weight_mod == residue { s } else { comp });
    }
    Pool {
        name: format!("complementary half b={b} w={residue} mod {weight_mod}"),
        ground,
        b,
        blocks,
    }
}

/// **Cyclic difference pool**: every translate under `Z_n` of every base
/// block whose difference multiset avoids a forbidden set. Cheap way to
/// get a structured, highly regular pool without prescribing that the
/// *family* be invariant — §13.3's finding was that invariant families
/// die because orbits veto, and this keeps the structure while letting
/// the search take part of an orbit.
pub fn cyclic_pool(n: u32, b: u32, keep_every: u32) -> Pool {
    let mut blocks = Vec::new();
    for s in subsets_of_size(n, b) {
        // canonical representative of the translation class
        let mut rep = u64::MAX;
        for t in 0..n {
            let mut r = 0u64;
            for i in 0..n {
                if s >> i & 1 == 1 {
                    r |= 1u64 << ((i + t) % n);
                }
            }
            rep = rep.min(r);
        }
        if rep == s || keep_every == 1 {
            blocks.push(s);
        }
    }
    if keep_every > 1 {
        blocks.retain(|&x| (x as u32) % keep_every == 0);
    }
    Pool {
        name: format!("cyclic reps n={n}"),
        ground: n,
        b,
        blocks,
    }
}

/// **Star**: every block through a fixed point. Intersecting by
/// construction, and the pool whose optimum is exactly `cone` of the
/// general row — `iota(b) >= g(b-1)`. The baseline every other pool has
/// to beat.
pub fn star(ground: u32, b: u32) -> Pool {
    Pool {
        name: "star at 0 (= cone)".into(),
        ground,
        b,
        blocks: subsets_of_size(ground, b)
            .into_iter()
            .filter(|s| s & 1 == 1)
            .collect(),
    }
}

/// **Bounded-defect pool**: blocks meeting a fixed `t`-set in at least
/// `lo` points. Interpolates between the star (`t = 1, lo = 1`) and
/// everything, and is where an intersecting family with covering number
/// `t` has to live — §21.5 measured `tau = b` for the whole 1972 tower,
/// so the extremal objects are *not* stars and this is the pool that
/// contains them.
pub fn cover_pool(ground: u32, b: u32, t: u32, lo: u32) -> Pool {
    let mask: u64 = (1u64 << t) - 1;
    Pool {
        name: format!("meets [0,{t}) in >= {lo}"),
        ground,
        b,
        blocks: subsets_of_size(ground, b)
            .into_iter()
            .filter(|s| (s & mask).count_ones() >= lo)
            .collect(),
    }
}
