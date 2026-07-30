//! What the extremal families *are*, not just how big they are.
//!
//! The development has measured `iota(b,g)` and `N(m,g)` for a while and
//! written down only the sizes. That is the cheapest thing to record and
//! the least informative: `docs/roadmap.md` §10 names "identify the
//! object" as a standing item, and every invariant it asks for is
//! computable from the witness in milliseconds.
//!
//! So this module takes a family of bitmasks and reports:
//!
//! * the **automorphism group** — order, generators, point orbits and
//!   member orbits — by a backtracking search over point permutations
//!   whose prune is *complete*, so the final check is free (see
//!   [`automorphisms`]);
//! * the **degree sequence** and the **diversity** `|F| - maxdeg`, which
//!   `docs/roadmap.md` §7 uses to say the extremal families are maximally
//!   non-star;
//! * the **pair degrees** `lambda(x,y)`, so "is this a 2-design?" is a
//!   question the data answers rather than a guess;
//! * the **per-core link matching numbers** — the clauses of
//!   `LinkCharacterisation.sunflower_iff_link_matching`, one per core, and
//!   in particular how many of them are *tight* (`nu = 2`). That number is
//!   the only measurement here of how much slack sunflower-freeness has;
//! * the **shadow sizes** `|partial_j F|`;
//! * the **VC dimension** of the family read as a set system on its
//!   ground set;
//! * the **anchor decomposition**: fix a member `A0` and split `F` by the
//!   trace `A ∩ A0`. Each class is bounded by `g(b - |S|)`, and the sum of
//!   those bounds is the Erdős–Rado-quality estimate `~b*g(b-1)`. How far
//!   below it the extremal family sits is exactly how much the *cross*
//!   constraints between classes buy — which is the whole conjecture.
//!
//! Sets are `u32` bitmasks, so `ground <= 32`; the subset enumerations
//! below are `2^ground`, so keep `ground <= 20` in practice.

/// Do `a`, `b`, `c` form a 3-sunflower? (Distinctness is the caller's.)
#[inline]
pub fn is_sunflower(a: u32, b: u32, c: u32) -> bool {
    let ab = a & b;
    ab == (a & c) && ab == (b & c)
}

/// The support: every point used by some member.
pub fn support(f: &[u32]) -> u32 {
    f.iter().fold(0, |acc, &a| acc | a)
}

/// The points of the support, in increasing order.
pub fn support_points(f: &[u32]) -> Vec<u32> {
    let s = support(f);
    (0..32).filter(|x| s >> x & 1 == 1).collect()
}

/// `deg(S)` = how many members contain `S`.
#[inline]
pub fn deg(f: &[u32], s: u32) -> usize {
    f.iter().filter(|&&a| a & s == s).count()
}

/// Degrees of the support points, in point order.
pub fn degree_sequence(f: &[u32]) -> Vec<(u32, usize)> {
    support_points(f)
        .into_iter()
        .map(|x| (x, deg(f, 1 << x)))
        .collect()
}

/// `|F| - maxdeg(F)`: how far the family is from being a star.
pub fn diversity(f: &[u32]) -> usize {
    let m = degree_sequence(f).into_iter().map(|(_, d)| d).max().unwrap_or(0);
    f.len() - m
}

/// The pair degrees `lambda(x,y)` over the support, as a sorted multiset.
pub fn pair_degrees(f: &[u32]) -> Vec<usize> {
    let pts = support_points(f);
    let mut out = Vec::new();
    for i in 0..pts.len() {
        for j in (i + 1)..pts.len() {
            out.push(deg(f, (1 << pts[i]) | (1 << pts[j])));
        }
    }
    out.sort_unstable();
    out
}

/// Is the family a 2-design on its support: every point in `r` members
/// and every pair in `lambda` of them?
pub fn design_parameters(f: &[u32]) -> Option<(usize, usize, usize, usize)> {
    let pts = support_points(f);
    if pts.is_empty() {
        return None;
    }
    let degs: Vec<usize> = pts.iter().map(|&x| deg(f, 1 << x)).collect();
    let r = degs[0];
    if degs.iter().any(|&d| d != r) {
        return None;
    }
    let lams = pair_degrees(f);
    let lam = *lams.first()?;
    if lams.iter().any(|&l| l != lam) {
        return None;
    }
    let k = f.first().map(|a| a.count_ones() as usize)?;
    if f.iter().any(|a| a.count_ones() as usize != k) {
        return None;
    }
    Some((pts.len(), k, lam, r))
}

/// The matching number of a family: the largest number of pairwise
/// disjoint members. Capped at `cap` so the search stays cheap.
pub fn matching_number(f: &[u32], cap: usize) -> usize {
    fn go(f: &[u32], used: u32, start: usize, depth: usize, best: &mut usize, cap: usize) {
        if depth > *best {
            *best = depth;
        }
        if *best >= cap || start == f.len() {
            return;
        }
        for i in start..f.len() {
            if f[i] & used == 0 {
                go(f, used | f[i], i + 1, depth + 1, best, cap);
                if *best >= cap {
                    return;
                }
            }
        }
    }
    let mut best = 0;
    go(f, 0, 0, 0, &mut best, cap);
    best
}

/// `Spread.link Y F`, on bitmasks.
pub fn link(y: u32, f: &[u32]) -> Vec<u32> {
    f.iter().filter(|&&a| a & y == y).map(|&a| a & !y).collect()
}

/// The clauses of the link characterisation, one per core, tabulated by
/// core size.
///
/// `by_size[j]` is `(cores with a nonempty link, cores whose link has
/// matching number exactly 2, the maximum matching number seen)` over
/// cores of size `j`. A family is 3-sunflower-free exactly when the
/// maximum is `<= 2` everywhere, so the third component is the check and
/// the second is the measurement: how many of the `2^g` clauses are
/// *tight*.
///
/// Only cores inside the support are enumerated: a core with a point
/// outside it has an empty link.
pub struct LinkProfile {
    pub by_size: Vec<(usize, usize, usize)>,
    pub max_nu: usize,
    pub tight_cores: Vec<u32>,
}

pub fn link_profile(f: &[u32]) -> LinkProfile {
    let pts = support_points(f);
    let n = pts.len();
    let b = f.first().map(|a| a.count_ones() as usize).unwrap_or(0);
    let mut by_size = vec![(0usize, 0usize, 0usize); n + 1];
    let mut max_nu = 0;
    let mut tight = Vec::new();
    for sub in 0u32..(1u32 << n) {
        let mut y = 0u32;
        for (i, &p) in pts.iter().enumerate() {
            if sub >> i & 1 == 1 {
                y |= 1 << p;
            }
        }
        let sz = y.count_ones() as usize;
        if sz > b {
            continue;
        }
        let l = link(y, f);
        if l.is_empty() {
            continue;
        }
        let nu = matching_number(&l, 4);
        let e = &mut by_size[sz];
        e.0 += 1;
        if nu == 2 {
            e.1 += 1;
            tight.push(y);
        }
        if nu > e.2 {
            e.2 = nu;
        }
        if nu > max_nu {
            max_nu = nu;
        }
    }
    LinkProfile { by_size, max_nu, tight_cores: tight }
}

/// `|partial_j F|`: how many distinct `j`-subsets lie inside some member.
pub fn shadow_sizes(f: &[u32]) -> Vec<usize> {
    let b = f.first().map(|a| a.count_ones() as usize).unwrap_or(0);
    let mut out = vec![0usize; b + 1];
    for j in 0..=b {
        let mut seen: Vec<u32> = Vec::new();
        for &a in f {
            let bits: Vec<u32> = (0..32).filter(|x| a >> x & 1 == 1).collect();
            // every j-subset of `a`
            for sub in 0u32..(1u32 << bits.len()) {
                if sub.count_ones() as usize != j {
                    continue;
                }
                let mut s = 0u32;
                for (i, &p) in bits.iter().enumerate() {
                    if sub >> i & 1 == 1 {
                        s |= 1 << p;
                    }
                }
                if !seen.contains(&s) {
                    seen.push(s);
                }
            }
        }
        out[j] = seen.len();
    }
    out
}

/// The VC dimension of `F` read as a set system on its support: the
/// largest `d` such that some `d`-point set `D` has all `2^d` traces
/// `A ∩ D` realised by members.
pub fn vc_dimension(f: &[u32]) -> usize {
    let pts = support_points(f);
    let n = pts.len();
    // A shattered `D` needs a member containing it, so `d <= b`.
    let b = f.first().map(|a| a.count_ones() as usize).unwrap_or(0);
    let mut best = 0;
    for sub in 0u32..(1u32 << n) {
        let d = sub.count_ones() as usize;
        if d <= best || d > b {
            continue;
        }
        let mut dmask = 0u32;
        for (i, &p) in pts.iter().enumerate() {
            if sub >> i & 1 == 1 {
                dmask |= 1 << p;
            }
        }
        // A shattered `D` needs a member containing it, so `d <= b`; the
        // trace table is `2^d` entries and stays small.
        let mut seen = vec![false; 1usize << d];
        for &a in f {
            // compress `a & dmask` down to the `d` chosen positions
            let mut t = 0usize;
            let mut k = 0;
            for (i, &p) in pts.iter().enumerate() {
                if sub >> i & 1 == 1 {
                    if a >> p & 1 == 1 {
                        t |= 1 << k;
                    }
                    k += 1;
                }
                let _ = i;
            }
            seen[t] = true;
        }
        let _ = dmask;
        if seen.iter().all(|&x| x) {
            best = d;
        }
    }
    best
}

/// Automorphisms of `F`: permutations of the support with `pi(F) = F`.
///
/// Returns `(order, generators)` where a generator is the image list
/// indexed by position in `support_points(f)`.
///
/// The prune is the whole method and it is *complete*: assign images
/// point by point, and after fixing the image of the `i`-th point check
/// `deg(S) = deg(pi(S))` for every subset `S` of the assigned points that
/// contains it. Since `deg(A) = 1` exactly for members `A` in a distinct
/// uniform family and `0` for every other set of that size, the family of
/// all those equalities *is* `pi(F) = F` — so a permutation surviving the
/// prune needs no final check, and one failing it can be cut at the
/// earliest possible depth.
pub fn automorphisms(f: &[u32]) -> (u64, Vec<Vec<u32>>) {
    let pts = support_points(f);
    let n = pts.len();
    // deg of every subset of the support, indexed by the compressed mask.
    let mut degs = vec![0usize; 1usize << n];
    for (sub, d) in degs.iter_mut().enumerate() {
        let mut s = 0u32;
        for (i, &p) in pts.iter().enumerate() {
            if sub >> i & 1 == 1 {
                s |= 1 << p;
            }
        }
        *d = deg(f, s);
    }

    let mut image = vec![usize::MAX; n];
    let mut used = vec![false; n];
    let mut found: Vec<Vec<u32>> = Vec::new();
    let mut count: u64 = 0;

    fn go(
        i: usize,
        n: usize,
        degs: &[usize],
        image: &mut Vec<usize>,
        used: &mut Vec<bool>,
        count: &mut u64,
        found: &mut Vec<Vec<u32>>,
        pts: &[u32],
    ) {
        if i == n {
            *count += 1;
            let g: Vec<u32> = image.iter().map(|&j| pts[j]).collect();
            let identity: Vec<u32> = pts.to_vec();
            if g != identity {
                found.push(g);
            }
            return;
        }
        for cand in 0..n {
            if used[cand] {
                continue;
            }
            image[i] = cand;
            // Every subset of {0..i} containing i.
            let mut ok = true;
            let rest = (1usize << i) - 1; // subsets of {0..i-1}
            let mut sub = 0usize;
            loop {
                let s = sub | (1usize << i);
                let mut t = 0usize;
                for k in 0..=i {
                    if s >> k & 1 == 1 {
                        t |= 1usize << image[k];
                    }
                }
                if degs[s] != degs[t] {
                    ok = false;
                    break;
                }
                if sub == rest {
                    break;
                }
                sub += 1;
            }
            if ok {
                used[cand] = true;
                go(i + 1, n, degs, image, used, count, found, pts);
                used[cand] = false;
            }
            image[i] = usize::MAX;
        }
    }

    go(0, n, &degs, &mut image, &mut used, &mut count, &mut found, &pts);
    (count, found)
}

/// Orbits of the automorphism group on the support points, as sorted
/// orbit sizes.
pub fn point_orbit_sizes(f: &[u32]) -> Vec<usize> {
    let pts = support_points(f);
    let n = pts.len();
    let (_, gens) = automorphisms(f);
    // union-find over positions
    let mut parent: Vec<usize> = (0..n).collect();
    fn find(p: &mut Vec<usize>, x: usize) -> usize {
        let mut x = x;
        while p[x] != x {
            p[x] = p[p[x]];
            x = p[x];
        }
        x
    }
    let index = |v: u32| pts.iter().position(|&q| q == v).unwrap();
    for g in &gens {
        for (i, &img) in g.iter().enumerate() {
            let a = find(&mut parent, i);
            let b = find(&mut parent, index(img));
            if a != b {
                parent[a] = b;
            }
        }
    }
    let mut sizes = std::collections::HashMap::new();
    for i in 0..n {
        let r = find(&mut parent, i);
        *sizes.entry(r).or_insert(0usize) += 1;
    }
    let mut out: Vec<usize> = sizes.into_values().collect();
    out.sort_unstable();
    out
}

/// The anchor decomposition: fix `a0` in `F` and bucket the other
/// members by `|A ∩ a0|`.
///
/// `classes[j]` is the total number of members `A != a0` with
/// `|A ∩ a0| = j`. Every such member's petal `A \ a0` lies outside `a0`
/// (that is what `A ∩ a0 = S` means), and the members sharing one trace
/// `S` are sunflower-free exactly when their petals are — so each trace
/// class is bounded by `g(b - |S|)` and the whole family by
/// `1 + sum_j C(b,j) g(b-j)`. The gap between that and `|F|` is what the
/// cross-class constraints buy.
pub fn anchor_classes(f: &[u32], a0: u32) -> Vec<usize> {
    let b = a0.count_ones() as usize;
    let mut out = vec![0usize; b + 1];
    for &a in f {
        if a == a0 {
            continue;
        }
        out[(a & a0).count_ones() as usize] += 1;
    }
    out
}

/// The per-trace class sizes: for each nonempty `S ⊆ a0`, how many
/// members have `A ∩ a0 = S` exactly. Returned as a sorted multiset per
/// `|S|`.
pub fn trace_class_sizes(f: &[u32], a0: u32) -> Vec<Vec<usize>> {
    let b = a0.count_ones() as usize;
    let apts: Vec<u32> = (0..32).filter(|x| a0 >> x & 1 == 1).collect();
    let mut out = vec![Vec::new(); b + 1];
    for sub in 1u32..(1u32 << b) {
        let mut s = 0u32;
        for (i, &p) in apts.iter().enumerate() {
            if sub >> i & 1 == 1 {
                s |= 1 << p;
            }
        }
        let c = f.iter().filter(|&&a| a != a0 && a & a0 == s).count();
        out[s.count_ones() as usize].push(c);
    }
    for v in out.iter_mut() {
        v.sort_unstable();
    }
    out
}

/// The cone: add a fresh point to every member.
///
/// `F` sunflower-free `m`-uniform on `[g]` becomes `(m+1)`-uniform,
/// **intersecting**, still sunflower-free, on `[g+1]`, with the same
/// number of members — because three members `A_i ∪ {*}` have pairwise
/// intersections `(A_i ∩ A_j) ∪ {*}`, which are all equal exactly when
/// the `A_i ∩ A_j` are. So `iota(m+1) >= g(m)`.
pub fn cone(f: &[u32], apex: u32) -> Vec<u32> {
    f.iter().map(|&a| a | (1 << apex)).collect()
}

/// The direct sum on disjoint grounds: `{A | (B << shift)}`.
///
/// Intersecting on both sides gives intersecting, and
/// `DirectSum.sum_family_no_sunflower` gives sunflower-free, so
/// `iota(a+b) >= iota(a) * iota(b)`.
pub fn direct_sum(f: &[u32], g: &[u32], shift: u32) -> Vec<u32> {
    let mut out = Vec::with_capacity(f.len() * g.len());
    for &a in f {
        for &b in g {
            out.push(a | (b << shift));
        }
    }
    out
}

/// Root-to-leaf paths of a complete binary tree of depth `d`, as edge
/// sets. `2^d` members, `d`-uniform, on `2^(d+1) - 2` points, and
/// 3-sunflower-free — the [FPPTZ24] construction, which
/// `rust/tests/ground_set.rs` already checks. Reproduced here because the
/// cone of it is the intersecting witness.
///
/// Edge numbering: the edge from node `v` to child `c` is numbered
/// `c - 1` in the standard heap indexing (`root = 0`, children of `v` are
/// `2v+1` and `2v+2`).
pub fn tree_paths(d: u32) -> Vec<u32> {
    let mut out = Vec::new();
    let first_leaf = (1u32 << d) - 1;
    for leaf in first_leaf..(1u32 << (d + 1)) - 1 {
        let mut m = 0u32;
        let mut v = leaf;
        while v != 0 {
            m |= 1 << (v - 1);
            v = (v - 1) / 2;
        }
        out.push(m);
    }
    out
}

/// Is `f` intersecting?
pub fn is_intersecting(f: &[u32]) -> bool {
    for i in 0..f.len() {
        for j in (i + 1)..f.len() {
            if f[i] & f[j] == 0 {
                return false;
            }
        }
    }
    true
}

/// Full report on one family, as text.
pub fn report(name: &str, f: &[u32], b: u32) -> String {
    use std::fmt::Write as _;
    let mut s = String::new();
    let pts = support_points(f);
    let _ = writeln!(s, "--- {name}");
    let _ = writeln!(
        s,
        "  size {}   uniformity {}   support {} points {:?}",
        f.len(),
        b,
        pts.len(),
        pts
    );
    let _ = writeln!(s, "  members: {}", fmt_family(f));
    let verdict = crate::intersecting::verify(f, b, true);
    let _ = writeln!(
        s,
        "  verify(uniform, distinct, intersecting, sunflower-free): {}",
        match &verdict {
            Ok(()) => "OK".to_string(),
            Err(e) => format!("FAILED: {e}"),
        }
    );
    let degs: Vec<usize> = degree_sequence(f).into_iter().map(|(_, d)| d).collect();
    let _ = writeln!(s, "  degrees {degs:?}   diversity {}", diversity(f));
    let lams = pair_degrees(f);
    let lmin = lams.iter().min().copied().unwrap_or(0);
    let lmax = lams.iter().max().copied().unwrap_or(0);
    let _ = writeln!(s, "  pair degrees in [{lmin}, {lmax}]");
    match design_parameters(f) {
        Some((v, k, lam, r)) => {
            let _ = writeln!(s, "  *** 2-design: 2-({v},{k},{lam}) with r = {r}");
        }
        None => {
            let _ = writeln!(s, "  not a 2-design (degrees or pair degrees not constant)");
        }
    }
    let (order, gens) = automorphisms(f);
    let _ = writeln!(
        s,
        "  |Aut| = {order}   generators {}   point orbits {:?}",
        gens.len(),
        point_orbit_sizes(f)
    );
    let lp = link_profile(f);
    let _ = writeln!(s, "  max link matching number nu = {} (must be <= 2)", lp.max_nu);
    let _ = writeln!(s, "  link clauses by core size |Y|: (cores with nonempty link, of which nu=2, max nu)");
    for (j, e) in lp.by_size.iter().enumerate() {
        if e.0 > 0 {
            let _ = writeln!(s, "    |Y| = {j}: {} cores, {} tight, max nu {}", e.0, e.1, e.2);
        }
    }
    let _ = writeln!(s, "  shadow sizes |partial_j F| = {:?}", shadow_sizes(f));
    let _ = writeln!(s, "  VC dimension {}", vc_dimension(f));
    if let Some(&a0) = f.first() {
        let _ = writeln!(
            s,
            "  anchor {a0:#b}: classes by |A cap A0| = {:?}",
            anchor_classes(f, a0)
        );
        let _ = writeln!(
            s,
            "  per-trace class sizes by |S| = {:?}",
            trace_class_sizes(f, a0)
        );
    }
    s
}

/// Render a family as sorted point lists.
pub fn fmt_family(f: &[u32]) -> String {
    let mut parts: Vec<String> = f
        .iter()
        .map(|&a| {
            let pts: Vec<u32> = (0..32).filter(|x| a >> x & 1 == 1).collect();
            format!(
                "{{{}}}",
                pts.iter().map(|p| p.to_string()).collect::<Vec<_>>().join(",")
            )
        })
        .collect();
    parts.sort();
    parts.join(" ")
}

/// The same, as a Coq literal `[[0; 1; 2]; ...]`.
pub fn fmt_coq(f: &[u32]) -> String {
    let parts: Vec<String> = f
        .iter()
        .map(|&a| {
            let pts: Vec<u32> = (0..32).filter(|x| a >> x & 1 == 1).collect();
            format!(
                "[{}]",
                pts.iter().map(|p| p.to_string()).collect::<Vec<_>>().join("; ")
            )
        })
        .collect();
    format!("[{}]", parts.join("; "))
}

/// A dreadnaut (nauty) input for the bipartite incidence graph of `F`,
/// so `|Aut|` can be checked against an independent implementation.
///
/// Points are vertices `0..n`, members are vertices `n..n+|F|`, and the
/// two sides are put in different colours so no automorphism mixes them.
/// nauty reports the order of the automorphism group of that coloured
/// graph, which for a distinct family is exactly the group [`automorphisms`]
/// counts.
pub fn dreadnaut_input(f: &[u32]) -> String {
    use std::fmt::Write as _;
    let pts = support_points(f);
    let n = pts.len();
    let total = n + f.len();
    let mut s = String::new();
    let _ = writeln!(s, "n={total} g");
    for (i, &p) in pts.iter().enumerate() {
        let nbrs: Vec<String> = f
            .iter()
            .enumerate()
            .filter(|(_, &a)| a >> p & 1 == 1)
            .map(|(j, _)| (n + j).to_string())
            .collect();
        let _ = writeln!(s, "{i}: {};", nbrs.join(" "));
    }
    let _ = writeln!(s, ".");
    // Colour the two sides apart.
    let _ = writeln!(
        s,
        "f=[{}|{}]",
        (0..n).map(|i| i.to_string()).collect::<Vec<_>>().join(","),
        (n..total).map(|i| i.to_string()).collect::<Vec<_>>().join(",")
    );
    let _ = writeln!(s, "x");
    let _ = writeln!(s, "q");
    s
}

// ---------------------------------------------------------------------
// The 128-bit path.
//
// `u32` runs out at 32 ground points, which is exactly where the
// interesting constructions start: the cone of the depth-5 tree paths
// needs 63, and `substitute(two_triangles, iota3)` needs 36. Before this
// existed the tree-path table silently reported nonsense from `b = 6` on
// (32 members on a 32-point support, against the 63 the construction
// actually uses) -- a truncation that read as data.
// ---------------------------------------------------------------------

/// Do `a`, `b`, `c` form a 3-sunflower? 128-bit version.
#[inline]
pub fn is_sunflower_128(a: u128, b: u128, c: u128) -> bool {
    let ab = a & b;
    ab == (a & c) && ab == (b & c)
}

/// Root-to-leaf paths of a complete binary tree of depth `d`, as edge
/// sets: `2^d` members, `d`-uniform, on `2^(d+1) - 2` points, and
/// 3-sunflower-free ([FPPTZ24]).
pub fn tree_paths_128(d: u32) -> Vec<u128> {
    assert!(d <= 6, "2^(d+1)-2 must fit in 128 bits");
    let mut out = Vec::new();
    let first_leaf = (1u32 << d) - 1;
    for leaf in first_leaf..(1u32 << (d + 1)) - 1 {
        let mut m = 0u128;
        let mut v = leaf;
        while v != 0 {
            m |= 1u128 << (v - 1);
            v = (v - 1) / 2;
        }
        out.push(m);
    }
    out
}

/// Add a fresh point to every member: `iota(m+1) >= g(m)`.
pub fn cone_128(f: &[u128], apex: u32) -> Vec<u128> {
    f.iter().map(|&a| a | (1u128 << apex)).collect()
}

/// How many ground points the family actually uses.
pub fn support_count_128(f: &[u128]) -> u32 {
    f.iter().fold(0u128, |acc, &a| acc | a).count_ones()
}

/// Verify uniformity, distinctness, sunflower-freeness and (optionally)
/// intersecting-ness, on 128-bit masks. Independent of every search.
pub fn verify_128(f: &[u128], b: u32, intersecting: bool) -> Result<(), String> {
    for (i, a) in f.iter().enumerate() {
        if a.count_ones() != b {
            return Err(format!("member {i} has size {}", a.count_ones()));
        }
        for (j, y) in f.iter().enumerate().skip(i + 1) {
            if a == y {
                return Err(format!("members {i} and {j} are equal"));
            }
            if intersecting && a & y == 0 {
                return Err(format!("members {i} and {j} are disjoint"));
            }
        }
    }
    match find_sunflower_128_local(f) {
        Some((i, j, l)) => Err(format!("members {i},{j},{l} are a 3-sunflower")),
        None => Ok(()),
    }
}

fn find_sunflower_128_local(f: &[u128]) -> Option<(usize, usize, usize)> {
    for i in 0..f.len() {
        for j in (i + 1)..f.len() {
            let ab = f[i] & f[j];
            for l in (j + 1)..f.len() {
                if ab == (f[i] & f[l]) && ab == (f[j] & f[l]) {
                    return Some((i, j, l));
                }
            }
        }
    }
    None
}

/// Widen a `u32` family.
pub fn widen(f: &[u32]) -> Vec<u128> {
    f.iter().map(|&a| u128::from(a)).collect()
}
