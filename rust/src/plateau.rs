//! Plateau search for large intersecting sunflower-free families.
//!
//! The branch-and-bound in `intersecting` and the SAT encoding in `sat`
//! are both *exact*: they decide, and `docs/roadmap.md` §9 records what
//! that costs — every UNSAT-side question at `b >= 4` was undecided after
//! an hour. This module gives up on deciding and only tries to *find*,
//! which is the side the record needs: `iota(6) >= 317` and
//! `iota(4) >= 32` are each witnessed by a single family, and a witness
//! needs no exhaustiveness argument at all. `intersecting::verify` checks
//! whatever comes out and shares no code with anything here.
//!
//! ## The move set
//!
//! The state is an intersecting sunflower-free family `F` of `b`-subsets
//! of `[g]`. Two moves, and the second is the one that matters:
//!
//! * **Fill.** Add addable candidates, at random, until none is addable.
//!   This reaches a *maximal* family — which is exactly where `extend.rs`
//!   proved the 1972 constructions already sit, so a fill alone can never
//!   beat them.
//! * **Force.** Pick a candidate `x` that is *not* addable, put it in
//!   anyway, and evict every member that blocks it: the members disjoint
//!   from `x`, and for each sunflower `(A, B, x)` both `A` and `B`. This
//!   is the escape from a maximal-family plateau, and it pays a bounded
//!   loss for a state no fill can reach.
//!
//! Evicted sets go on a short tabu list, so the fill that follows a force
//! does not simply undo it.
//!
//! ## Why the candidate test is cheap
//!
//! `A, B, x` is a 3-sunflower iff `A ∩ B = A ∩ x = B ∩ x`. Since
//! `A ∩ x = B ∩ x = Y` already forces `Y ⊆ A ∩ B`, the condition is
//!
//! ```text
//!     A ∩ x = B ∩ x        and        A ∩ B ⊆ x.
//! ```
//!
//! So bucket the members of `F` by `A ∩ x`, which takes `2^b` values, and
//! only pairs *inside a bucket* can be dangerous. That turns a scan over
//! `|F|^2 / 2` pairs — 45000 of them at `|F| = 300` — into `|F|` masking
//! steps plus a few pairs per bucket. It is the observation `orbit.rs`
//! uses for its incremental check, indexed the other way round.
//!
//! The same identity keeps the *incremental* filter cheap. After `x` is
//! added, a surviving candidate `y` is newly dead iff some `A ∈ F` makes
//! `(A, x, y)` a sunflower, which needs `A ∩ x = x ∩ y` — a single
//! bucket, not the whole family. That is a factor `2^b` on the inner
//! loop and it is what makes `b = 6` on eighteen points searchable at
//! all.

/// Do `a`, `b`, `c` form a 3-sunflower?
#[inline]
pub fn is_sunflower(a: u32, b: u32, c: u32) -> bool {
    let ab = a & b;
    ab == (a & c) && ab == (b & c)
}

/// The `b`-subsets of `[ground]` other than `anchor`; when `intersecting`,
/// only those meeting it.
pub fn candidates(ground: u32, b: u32, anchor: u32, intersecting: bool) -> Vec<u32> {
    assert!(ground <= 28, "ground {ground} too large to enumerate");
    (0u32..(1u32 << ground))
        .filter(|x| {
            x.count_ones() == b && *x != anchor && (!intersecting || x & anchor != 0)
        })
        .collect()
}

/// splitmix64, so a run is reproducible from its seed.
pub struct Rng(u64);

impl Rng {
    pub fn new(seed: u64) -> Self {
        Rng(seed.wrapping_mul(0x2545F4914F6CDD1D) | 1)
    }
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E3779B97F4A7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
        z ^ (z >> 31)
    }
    /// A draw in `[0, n)`. Public so tests can share the stream.
    pub fn below(&mut self, n: usize) -> usize {
        if n == 0 {
            0
        } else {
            (self.next() % n as u64) as usize
        }
    }
}

/// Compress `hit` (a subset of `x`) to an index in `[0, 2^b)`.
#[inline]
fn compress(hit: u32, bits: &[u32]) -> usize {
    let mut idx = 0usize;
    for (p, &bit) in bits.iter().enumerate() {
        if hit & bit != 0 {
            idx |= 1 << p;
        }
    }
    idx
}

/// The set bits of `x`, low to high.
#[inline]
fn bits_of(x: u32) -> Vec<u32> {
    let mut v = Vec::with_capacity(x.count_ones() as usize);
    let mut r = x;
    while r != 0 {
        let low = r & r.wrapping_neg();
        v.push(low);
        r ^= low;
    }
    v
}

/// Reference test: is `x` addable to `fam` as an intersecting family?
/// Quadratic in `|fam|`, and it is what the fast paths are checked
/// against.
pub fn addable(fam: &[u32], x: u32) -> bool {
    if fam.iter().any(|&a| a & x == 0) {
        return false;
    }
    for i in 0..fam.len() {
        for j in (i + 1)..fam.len() {
            if is_sunflower(fam[i], fam[j], x) {
                return false;
            }
        }
    }
    true
}

/// Scratch space reused across calls, so a long run does no allocation.
struct Scratch {
    buckets: Vec<Vec<u32>>,
}

impl Scratch {
    fn new(b: u32) -> Self {
        Scratch {
            buckets: vec![Vec::new(); 1usize << b],
        }
    }

    /// Members of `fam` that block `x`, or `None` when `x` is addable.
    ///
    /// When `intersecting` is false the disjoint members are not blockers
    /// — but they are still bucketed at index 0, because a sunflower with
    /// empty core is exactly three pairwise disjoint members and the
    /// bucket test finds it there.
    fn blockers(&mut self, fam: &[u32], x: u32, intersecting: bool) -> Option<Vec<usize>> {
        let bits = bits_of(x);
        let mut out: Vec<usize> = Vec::new();
        for bucket in self.buckets.iter_mut() {
            bucket.clear();
        }
        for (i, &a) in fam.iter().enumerate() {
            let hit = a & x;
            if hit == 0 && intersecting {
                out.push(i);
                continue;
            }
            self.buckets[compress(hit, &bits)].push(i as u32);
        }
        for bucket in self.buckets.iter() {
            for i in 0..bucket.len() {
                for j in (i + 1)..bucket.len() {
                    let (u, v) = (bucket[i] as usize, bucket[j] as usize);
                    if fam[u] & fam[v] & !x == 0 {
                        out.push(u);
                        out.push(v);
                    }
                }
            }
        }
        if out.is_empty() {
            None
        } else {
            out.sort_unstable();
            out.dedup();
            Some(out)
        }
    }
}

/// How many candidates a force move looks at before committing.
const SAMPLE: usize = 400;
/// The largest eviction a single force move will pay for.
const MAX_EVICT: usize = 3;
/// How long an evicted set stays out.
const TABU: u64 = 6;

/// What a run found.
pub struct Found {
    pub best: usize,
    pub family: Vec<u32>,
    pub steps: u64,
}

/// Plateau search on `ground` points at uniformity `b`.
///
/// `seed_family`, when non-empty, is the starting state and must be a
/// valid intersecting sunflower-free family on `[ground]`; it is checked
/// by assertion. `steps` bounds the number of force moves. `report` is
/// called whenever the incumbent improves, so a long run can flush to a
/// file rather than buffer.
///
/// The anchor `{0, ..., b-1}` is held fixed, sound for the same reason
/// `intersecting::max_intersecting` gives: an intersecting family may be
/// relabelled so that a chosen member is the anchor, and relabelling
/// preserves uniformity, distinctness, intersecting-ness and
/// sunflower-freeness.
pub fn search<F: FnMut(usize, &[u32])>(
    ground: u32,
    b: u32,
    steps: u64,
    rng_seed: u64,
    seed_family: &[u32],
    intersecting: bool,
    mut report: F,
) -> Found {
    let anchor: u32 = (1u32 << b) - 1;
    let cands = candidates(ground, b, anchor, intersecting);
    let mut rng = Rng::new(rng_seed);
    let mut scratch = Scratch::new(b);

    let mut fam: Vec<u32> = if seed_family.is_empty() {
        vec![anchor]
    } else {
        anchored(seed_family, ground)
    };
    assert!(
        crate::intersecting::verify(&fam, b, intersecting).is_ok(),
        "seed family is not a valid sunflower-free family"
    );
    assert!(fam.contains(&anchor), "seed family lost its anchor");

    let mut best = fam.len();
    let mut best_family = fam.clone();
    report(best, &best_family);

    // Candidates still addable to `fam`. Recomputed after evictions,
    // narrowed incrementally after additions.
    let mut alive: Vec<u32> = Vec::new();
    let mut tabu: std::collections::HashMap<u32, u64> = std::collections::HashMap::new();
    let mut step: u64 = 0;
    let mut dirty = true;

    loop {
        if dirty {
            alive = cands
                .iter()
                .copied()
                .filter(|&x| !fam.contains(&x) && scratch.blockers(&fam, x, intersecting).is_none())
                .collect();
            dirty = false;
        }

        // ---- fill to maximality ----
        loop {
            let pool: Vec<u32> = alive
                .iter()
                .copied()
                .filter(|x| tabu.get(x).is_none_or(|&t| t <= step))
                .collect();
            if pool.is_empty() {
                break;
            }
            let x = pool[rng.below(pool.len())];
            fam.push(x);
            narrow(&mut alive, &fam, x, &mut scratch, intersecting);
        }
        if fam.len() > best {
            best = fam.len();
            best_family = fam.clone();
            report(best, &best_family);
        }
        step += 1;
        if step >= steps {
            break;
        }

        // ---- force a non-member in, evicting as little as possible ----
        //
        // A forced move with exactly one blocker is size-neutral: it
        // swaps one member for another and the fill that follows may then
        // find room. Those are the moves that walk the plateau of maximal
        // families, and taking the *cheapest* available one rather than a
        // random one is the difference between reaching `iota(4,9) = 27`
        // and stalling in the low twenties. Sampling keeps the scan off
        // the critical path when the candidate set is large.
        let sample = SAMPLE.min(cands.len());
        let mut chosen: Option<(usize, u32, Vec<usize>)> = None;
        for _ in 0..sample {
            let x = cands[rng.below(cands.len())];
            if x == anchor || fam.contains(&x) || tabu.get(&x).is_some_and(|&t| t > step) {
                continue;
            }
            let Some(blockers) = scratch.blockers(&fam, x, intersecting) else {
                chosen = Some((0, x, Vec::new()));
                break;
            };
            if blockers.iter().any(|&i| fam[i] == anchor) || blockers.len() > MAX_EVICT {
                continue;
            }
            let cost = blockers.len();
            if chosen.as_ref().is_none_or(|(c, _, _)| cost < *c) {
                chosen = Some((cost, x, blockers));
            }
            if cost <= 1 {
                break;
            }
        }
        if let Some((cost, x, blockers)) = chosen {
            if cost == 0 {
                fam.push(x);
                narrow(&mut alive, &fam, x, &mut scratch, intersecting);
            } else {
                for &i in blockers.iter().rev() {
                    let gone = fam.swap_remove(i);
                    tabu.insert(gone, step + TABU);
                }
                fam.push(x);
                dirty = true;
            }
        }

        // A harder kick now and then, so the walk is not confined to
        // one basin.
        if step % 4096 == 0 && fam.len() > 4 {
            for _ in 0..3 {
                let i = rng.below(fam.len());
                if fam[i] != anchor {
                    let gone = fam.swap_remove(i);
                    tabu.insert(gone, step + TABU);
                }
            }
            dirty = true;
        }
        if step % 65536 == 0 {
            tabu.retain(|_, t| *t > step);
        }
    }

    Found {
        best,
        family: best_family,
        steps: step,
    }
}

/// Drop from `alive` everything the newly added `x` kills.
///
/// A candidate `y` dies iff it misses `x`, equals `x`, or some `A ∈ fam`
/// makes `(A, x, y)` a sunflower. The last needs `A ∩ x = x ∩ y`, so only
/// one bucket of `fam` is consulted rather than all of it.
fn narrow(
    alive: &mut Vec<u32>,
    fam: &[u32],
    x: u32,
    scratch: &mut Scratch,
    intersecting: bool,
) {
    let bits = bits_of(x);
    for bucket in scratch.buckets.iter_mut() {
        bucket.clear();
    }
    for &a in fam.iter() {
        if a == x {
            continue;
        }
        scratch.buckets[compress(a & x, &bits)].push(a);
    }
    let buckets = &scratch.buckets;
    alive.retain(|&y| {
        if y == x || (intersecting && y & x == 0) {
            return false;
        }
        let core = x & y;
        !buckets[compress(core, &bits)]
            .iter()
            .any(|&a| a & y & !x == 0)
    });
}

/// Relabel `f` so its first member becomes `{0, ..., b-1}`.
pub fn anchored(f: &[u32], ground: u32) -> Vec<u32> {
    let anchor: u32 = (1u32 << f[0].count_ones()) - 1;
    if f.contains(&anchor) {
        return f.to_vec();
    }
    let first = f[0];
    let inside = (0..ground).filter(|p| first >> p & 1 == 1);
    let outside = (0..ground).filter(|p| first >> p & 1 == 0);
    let mut perm = vec![0u32; ground as usize];
    for (i, p) in inside.chain(outside).enumerate() {
        perm[p as usize] = i as u32;
    }
    f.iter()
        .map(|&s| {
            let mut t = 0u32;
            for p in 0..ground {
                if s >> p & 1 == 1 {
                    t |= 1 << perm[p as usize];
                }
            }
            t
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The bucketed blocker test and the quadratic one must agree. This is
    /// the only thing standing between a bucket-index bug and a "family"
    /// that is silently not sunflower-free.
    #[test]
    fn bucket_test_agrees_with_the_quadratic_one() {
        let b = 4u32;
        let ground = 9u32;
        let anchor = (1u32 << b) - 1;
        let cands = candidates(ground, b, anchor, true);
        let mut rng = Rng::new(7);
        let mut scratch = Scratch::new(b);
        let mut checked = 0;
        for _ in 0..200 {
            let mut fam = vec![anchor];
            for _ in 0..15 {
                let x = cands[rng.below(cands.len())];
                if !fam.contains(&x) && addable(&fam, x) {
                    fam.push(x);
                }
            }
            for &x in cands.iter() {
                if fam.contains(&x) {
                    continue;
                }
                assert_eq!(
                    scratch.blockers(&fam, x, true).is_none(),
                    addable(&fam, x),
                    "disagreement at fam {fam:?}, x {x:#b}"
                );
                checked += 1;
            }
        }
        assert!(checked > 20_000, "only {checked} comparisons");
    }

    /// `narrow` must leave exactly the addable candidates behind.
    #[test]
    fn narrow_agrees_with_a_full_rescan() {
        let b = 4u32;
        let ground = 10u32;
        let anchor = (1u32 << b) - 1;
        let cands = candidates(ground, b, anchor, true);
        let mut rng = Rng::new(31);
        let mut scratch = Scratch::new(b);
        for _ in 0..40 {
            let mut fam = vec![anchor];
            let mut alive: Vec<u32> = cands.iter().copied().filter(|&x| addable(&fam, x)).collect();
            for _ in 0..20 {
                if alive.is_empty() {
                    break;
                }
                let x = alive[rng.below(alive.len())];
                fam.push(x);
                narrow(&mut alive, &fam, x, &mut scratch, true);
                let mut want: Vec<u32> = cands
                    .iter()
                    .copied()
                    .filter(|&y| !fam.contains(&y) && addable(&fam, y))
                    .collect();
                let mut got = alive.clone();
                want.sort_unstable();
                got.sort_unstable();
                assert_eq!(got, want, "narrow diverged at |fam| = {}", fam.len());
            }
        }
    }

    /// At parameters the exact search decides, the plateau search must not
    /// claim more than the exhaustive maximum — and should reach it from
    /// nothing. `(4, 9) = 27` is the sharp one: it is the 1972 family, it
    /// is rigid, and a search that cannot rediscover it has no business
    /// being pointed at `b = 6`.
    #[test]
    fn plateau_reaches_the_known_maxima() {
        for (b, g, known) in [(2u32, 6u32, 3usize), (3, 6, 10), (3, 9, 10), (4, 9, 27)] {
            let f = search(g, b, 20_000, 12345, &[], true, |_, _| {});
            assert!(
                f.best <= known,
                "plateau claims {} at b={b} g={g}, above the exhaustive {known}",
                f.best
            );
            crate::intersecting::verify(&f.family, b, true).expect("witness invalid");
            assert_eq!(f.best, known, "plateau missed the maximum at b={b} g={g}");
        }
    }

    /// A seeded run never loses ground: it reports at least the seed.
    #[test]
    fn seeding_never_loses() {
        let (_, seed, _) = crate::intersecting::iota(9, 4, 200_000_000, 0);
        assert_eq!(seed.len(), 27);
        let f = search(9, 4, 60, 999, &seed, true, |_, _| {});
        assert!(f.best >= 27, "seeded run dropped to {}", f.best);
        crate::intersecting::verify(&f.family, 4, true).expect("witness invalid");
    }
}
