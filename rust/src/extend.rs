//! Is the 1972 construction *maximal*? — the extension question.
//!
//! `docs/roadmap.md` §12 says the record moves the moment some `b` has
//! `iota(b)^2 > 10^(b-1)`, and §11.6 says the best families the
//! repository can build come from the Abbott–Hanson–Sauer substitution.
//! Nobody had asked the cheapest question about them: **can a single
//! further `b`-set be added?** At `b = 9` the substitution builds 10,000
//! members and the threshold is 10,001, so one addable set would beat
//! 1972 outright.
//!
//! ## The reduction that makes this finite
//!
//! The question looks like it has to be asked once per ground set. It
//! does not. A candidate `C` interacts with the family only through
//! `C ∩ support(F)`: a point in no member contributes to no
//! intersection. So write `S = C ∩ support(F)` and note
//!
//! * `C` meets `A` iff `S` meets `A`;
//! * `A ∩ C = A ∩ S` for every member `A`.
//!
//! Hence `C` may be added iff its **trace** `S` may be, and the trace
//! ranges over subsets of the support of size at most `b`. Enumerating
//! traces answers the question for *every* ground set at once, which is
//! what makes a negative result here worth stating.
//!
//! ## The two conditions, as conditions on the trace
//!
//! **Meeting.** `S` must meet every member — i.e. `S` is a *hitting set*
//! (transversal) of `F`. So a maximal intersecting family is one whose
//! only hitting sets of size `<= b` are its own members, and the
//! covering number `tau(F)` is what decides it: if `tau(F) = b` and the
//! minimum hitting sets are exactly the members, nothing can be added on
//! any ground set.
//!
//! **Sunflower-freeness.** `A`, `B`, `C` is a 3-sunflower iff
//! `A ∩ B = A ∩ C = B ∩ C`, and substituting `A ∩ C = A ∩ S` turns that
//! into a condition with no `C` in it:
//!
//! ```text
//!     (A, B) is dangerous for S   iff   A ∩ B ⊆ S   and   S ∩ (A △ B) = ∅.
//! ```
//!
//! One clause per *pair* of members, not per triple. That is the whole
//! reason this is a small SAT instance rather than a large one.
//!
//! ## What is asked of what
//!
//! For the pure substitutions the meeting condition alone settles it, so
//! the sunflower clauses are switched off — a stronger negative, and it
//! keeps the `b = 9` instance at ten thousand clauses instead of the
//! fifty million the pairs would cost. For the *cones* the apex meets
//! everything for free, so there the meeting condition is vacuous and
//! the sunflower clauses are the whole question.
//!
//! Everything here is cross-checked two ways: a brute-force enumeration
//! of every trace, and a SAT encoding, must agree wherever both run; and
//! every model is decoded to an actual `b`-set and handed to
//! `structure::verify_128`, which shares no code with any of this.

use crate::sat::{Cnf, RawVerdict, Solver};
use crate::structure;

/// The points of the support, in increasing order.
pub fn support_points_128(f: &[u128]) -> Vec<u32> {
    let s = f.iter().fold(0u128, |a, &x| a | x);
    (0..128).filter(|x| s >> x & 1 == 1).collect()
}

/// Is `s` a hitting set of `f` — does it meet every member?
#[inline]
pub fn hits_all(f: &[u128], s: u128) -> bool {
    f.iter().all(|&a| a & s != 0)
}

/// Is the pair `(a, b)` dangerous for the trace `s`: would a `b`-set
/// with that trace complete a 3-sunflower with them?
#[inline]
pub fn dangerous(a: u128, b: u128, s: u128) -> bool {
    let i = a & b;
    i & s == i && (a ^ b) & s == 0
}

/// Can a `b`-set with trace `s` be added to `f`?
///
/// `require_meeting` asks for intersecting-ness, `require_sunflower_free`
/// for the ternary condition. A trace equal to a member is rejected:
/// that would re-add a set already there.
pub fn trace_is_addable(
    f: &[u128],
    b: usize,
    s: u128,
    require_meeting: bool,
    require_sunflower_free: bool,
) -> bool {
    if s.count_ones() as usize > b {
        return false;
    }
    if s.count_ones() as usize == b && f.contains(&s) {
        return false;
    }
    if require_meeting && !hits_all(f, s) {
        return false;
    }
    if require_sunflower_free {
        for i in 0..f.len() {
            for j in (i + 1)..f.len() {
                if dangerous(f[i], f[j], s) {
                    return false;
                }
            }
        }
    }
    true
}

/// Every addable trace, by brute force over the subsets of the support.
///
/// `Sum_{j <= b} C(|support|, j)` candidates, so this is the oracle for
/// the small rows and the differential check on the SAT encoding — not
/// the method for `b = 9`, where it is 1.4e8 traces against ten thousand
/// members.
pub fn addable_traces_brute(
    f: &[u128],
    b: usize,
    require_meeting: bool,
    require_sunflower_free: bool,
) -> Vec<u128> {
    let pts = support_points_128(f);
    let mut out = Vec::new();
    let mut cur = 0u128;
    fn go(
        f: &[u128],
        b: usize,
        pts: &[u32],
        i: usize,
        cur: &mut u128,
        depth: usize,
        require_meeting: bool,
        require_sunflower_free: bool,
        out: &mut Vec<u128>,
    ) {
        if trace_is_addable(f, b, *cur, require_meeting, require_sunflower_free) {
            out.push(*cur);
        }
        if depth == b {
            return;
        }
        for k in i..pts.len() {
            *cur |= 1u128 << pts[k];
            go(
                f,
                b,
                pts,
                k + 1,
                cur,
                depth + 1,
                require_meeting,
                require_sunflower_free,
                out,
            );
            *cur &= !(1u128 << pts[k]);
        }
    }
    go(
        f,
        b,
        &pts,
        0,
        &mut cur,
        0,
        require_meeting,
        require_sunflower_free,
        &mut out,
    );
    out
}

/// The CNF for "is there an addable trace?", one boolean per support
/// point. Returns the formula and the point list, in variable order.
pub fn addable_cnf(
    f: &[u128],
    b: usize,
    require_meeting: bool,
    require_sunflower_free: bool,
) -> (Cnf, Vec<u32>) {
    let pts = support_points_128(f);
    let mut cnf = Cnf::new();
    let vars: Vec<i32> = pts.iter().map(|_| cnf.new_var()).collect();
    let var_of = |p: u32| -> i32 {
        let i = pts.iter().position(|&q| q == p).expect("point outside support");
        vars[i]
    };

    // |S| <= b.
    cnf.at_most(&vars, b);

    // S meets every member.
    if require_meeting {
        for &a in f {
            let cl: Vec<i32> = pts
                .iter()
                .filter(|&&p| a >> p & 1 == 1)
                .map(|&p| var_of(p))
                .collect();
            cnf.add(cl);
        }
    }

    // No pair is dangerous: NOT( A cap B subseteq S  AND  S cap (A xor B) = empty ).
    if require_sunflower_free {
        for i in 0..f.len() {
            for j in (i + 1)..f.len() {
                let inter = f[i] & f[j];
                let sym = f[i] ^ f[j];
                let mut cl: Vec<i32> = Vec::new();
                for &p in &pts {
                    if inter >> p & 1 == 1 {
                        cl.push(-var_of(p));
                    } else if sym >> p & 1 == 1 {
                        cl.push(var_of(p));
                    }
                }
                cnf.add(cl);
            }
        }
    }

    // S must not be a member outright -- that would re-add a set already
    // present. Only a trace of full size can be one, and this clause is
    // satisfied by any proper subset of `a`.
    for &a in f {
        let cl: Vec<i32> = pts
            .iter()
            .map(|&p| if a >> p & 1 == 1 { -var_of(p) } else { var_of(p) })
            .collect();
        cnf.add(cl);
    }

    (cnf, pts)
}

/// What the extension question answered to.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Extension {
    /// A trace, and the `b`-set built from it (fresh points appended).
    Found(u128, u128),
    /// No `b`-set can be added, on **any** ground set.
    Maximal,
    /// The solvers did not decide, or disagreed with each other.
    Undecided,
}

/// Ask the extension question with a SAT solver, and verify whatever
/// comes back.
///
/// A model is decoded to a trace, padded to a full `b`-set with points
/// nobody uses, appended to the family, and the *whole* family is handed
/// to `structure::verify_128` — so a wrong encoding produces a failed
/// verification rather than a false discovery. UNSAT needs two solvers
/// to agree, which is the discipline `docs/roadmap.md` §9 already
/// applies: it is the verdict no witness can confirm.
pub fn addable_sat(
    f: &[u128],
    b: usize,
    require_meeting: bool,
    require_sunflower_free: bool,
    seconds: u64,
    tag: &str,
) -> std::io::Result<Extension> {
    let (cnf, pts) = addable_cnf(f, b, require_meeting, require_sunflower_free);
    let second = if Solver::CryptoMiniSat.available() {
        Solver::CryptoMiniSat
    } else {
        Solver::Minisat
    };
    let verdict = crate::sat::solve_cnf_agreed(&cnf, Solver::Cadical, second, seconds, tag)?;
    Ok(match verdict {
        RawVerdict::Unsat => Extension::Maximal,
        RawVerdict::Unknown => Extension::Undecided,
        RawVerdict::Sat(assign) => {
            let mut trace = 0u128;
            for (i, &p) in pts.iter().enumerate() {
                if assign[i] {
                    trace |= 1u128 << p;
                }
            }
            let member = pad_with_fresh(f, b, trace);
            let mut widened = f.to_vec();
            widened.push(member);
            structure::verify_128(&widened, b as u32, require_meeting).unwrap_or_else(|e| {
                panic!("the solver returned a trace that does not extend the family: {e}")
            });
            Extension::Found(trace, member)
        }
    })
}

/// Pad a trace up to `b` points using points outside the support.
pub fn pad_with_fresh(f: &[u128], b: usize, trace: u128) -> u128 {
    let used = f.iter().fold(0u128, |a, &x| a | x) | trace;
    let mut m = trace;
    let mut p = 0u32;
    while (m.count_ones() as usize) < b {
        while used >> p & 1 == 1 {
            p += 1;
            assert!(p < 128, "no fresh point left inside 128 bits");
        }
        m |= 1u128 << p;
        p += 1;
    }
    m
}

/// Every *minimal* hitting set of `f` of size at most `cap`.
///
/// Branch on an unhit member: any hitting set contains one of its
/// points. Forbidding a point once its branch is finished stops the same
/// set being found twice. The result may contain non-minimal sets; the
/// caller filters if it cares. Returns `(sets, exhaustive)`.
pub fn minimal_hitting_sets(f: &[u128], cap: usize, budget: u64) -> (Vec<u128>, bool) {
    fn rec(
        f: &[u128],
        unhit: &[usize],
        cur: u128,
        forbidden: u128,
        cap: usize,
        out: &mut Vec<u128>,
        nodes: &mut u64,
        budget: u64,
    ) {
        *nodes += 1;
        if *nodes > budget {
            return;
        }
        if unhit.is_empty() {
            out.push(cur);
            return;
        }
        if cur.count_ones() as usize >= cap {
            return;
        }
        // The unhit member with fewest points still allowed.
        let mut best = u32::MAX;
        let mut pick = 0u128;
        for &i in unhit {
            let m = f[i] & !forbidden;
            let c = m.count_ones();
            if c < best {
                best = c;
                pick = m;
                if c == 0 {
                    break;
                }
            }
        }
        if best == 0 {
            return;
        }
        let mut forb = forbidden;
        let mut m = pick;
        while m != 0 {
            let p = m & m.wrapping_neg();
            m ^= p;
            let next: Vec<usize> = unhit.iter().copied().filter(|&i| f[i] & p == 0).collect();
            rec(f, &next, cur | p, forb, cap, out, nodes, budget);
            forb |= p;
            if *nodes > budget {
                return;
            }
        }
    }
    let all: Vec<usize> = (0..f.len()).collect();
    let mut out = Vec::new();
    let mut nodes = 0u64;
    rec(f, &all, 0, 0, cap, &mut out, &mut nodes, budget);
    out.sort_unstable();
    out.dedup();
    (out, nodes <= budget)
}

/// The covering number `tau(f)`: the size of the smallest hitting set,
/// or `None` if it exceeds `cap`.
pub fn covering_number(f: &[u128], cap: usize, budget: u64) -> Option<usize> {
    let (sets, exhaustive) = minimal_hitting_sets(f, cap, budget);
    if !exhaustive {
        return None;
    }
    sets.iter().map(|s| s.count_ones() as usize).min()
}
