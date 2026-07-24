//! Cross-checks between the Coq theorems and brute-force computation.
//!
//! Each test pins down a concrete instance of a theorem from the Coq
//! formalization. A failing assertion here would indicate either a
//! bug in this crate's brute-force code, or — assuming the Coq
//! kernel is sound — a contradiction in our axioms, which would be a
//! catastrophic failure of the underlying logic.

use sunflower_formal::{
    bounds::f_nk_exact,
    construction::{disjoint_blocks, product_family},
    sunflower::find_k_sunflower,
};

// --- Coq: SmallCases.f_n_2_eq_2 ---
//
// f(n, 2) = 2 for every n >= 1.

#[test]
fn f_1_2_eq_2() {
    let (m, _) = f_nk_exact(1, 2, 3);
    assert_eq!(m, 2);
}

#[test]
fn f_2_2_eq_2() {
    let (m, _) = f_nk_exact(2, 2, 4);
    assert_eq!(m, 2);
}

#[test]
fn f_3_2_eq_2() {
    let (m, _) = f_nk_exact(3, 2, 5);
    assert_eq!(m, 2);
}

// --- Coq: SmallCases.f_1_k_eq_k ---
//
// f(1, k) = k for every k >= 2.

#[test]
fn f_1_3_eq_3() {
    let (m, _) = f_nk_exact(1, 3, 4);
    assert_eq!(m, 3);
}

#[test]
fn f_1_4_eq_4() {
    let (m, _) = f_nk_exact(1, 4, 5);
    assert_eq!(m, 4);
}

// --- Coq: LowerBound.lower_bound_trivial ---
//
// disjoint_blocks(k-1, n) is a family of k-1 sets with no k-sunflower.

#[test]
fn disjoint_blocks_2_3_no_3_sunflower() {
    // k = 3, n = 3 ⇒ family of 2 sets, can't contain a 3-sunflower.
    let f = disjoint_blocks(2, 3);
    assert!(find_k_sunflower(&f, 3).is_none());
}

#[test]
fn disjoint_blocks_3_2_no_4_sunflower() {
    let f = disjoint_blocks(3, 2);
    assert!(find_k_sunflower(&f, 4).is_none());
}

// --- Standard exponential lower bound (formalized in Coq as
// `ProductLowerBound.lower_bound_exponential`; these brute-force checks
// remain as an independent computational cross-check): product_family(k-1, n)
// has size (k-1)^n and no k-sunflower.

#[test]
fn product_family_2_2_no_3_sunflower() {
    // k=3, n=2: (k-1)^n = 4 sets, no 3-sunflower.
    let f = product_family(2, 2);
    assert_eq!(f.len(), 4);
    assert!(find_k_sunflower(&f, 3).is_none());
}

#[test]
fn product_family_2_3_no_3_sunflower() {
    // k=3, n=3: (k-1)^n = 8 sets, no 3-sunflower.
    let f = product_family(2, 3);
    assert_eq!(f.len(), 8);
    assert!(find_k_sunflower(&f, 3).is_none());
}

#[test]
fn product_family_3_2_no_4_sunflower() {
    // k=4, n=2: (k-1)^n = 9 sets, no 4-sunflower.
    let f = product_family(3, 2);
    assert_eq!(f.len(), 9);
    assert!(find_k_sunflower(&f, 4).is_none());
}

// --- Cross-checking exact f(n,k) against ER upper bound ---
//
// The Coq theorem says f(n,k) <= (k-1)^n n! + 1. So our exact value
// should be at most that. (For all tested small cases.)

#[test]
fn f_2_3_within_ER_bound() {
    let (m, _) = f_nk_exact(2, 3, 5);
    let er = sunflower_formal::bounds::erdos_rado_bound(2, 3);
    // Theorem: f(n,k) <= ER_bound(n,k). Strict for small cases.
    assert!(m <= er, "exact f(2,3) = {} should be <= ER bound {}", m, er);
    // Lower bound from this development: f(n,k) >= k. So f(2,3) >= 3.
    assert!(m >= 3, "lower bound: f(2,3) >= 3, got {}", m);
}

#[test]
fn f_2_3_actual_value() {
    // f(2, 3) = ? Let's see what brute force finds (with sufficient universe).
    let (m, _) = f_nk_exact(2, 3, 5);
    // The product_family(2, 2) gives 4 distinct 2-sets with no 3-sunflower:
    // those are {0,2}, {0,3}, {1,2}, {1,3}. So f(2, 3) >= 5.
    // Erdős-Rado: f(2, 3) <= (k-1)^n n! + 1 = 4*2+1 = 9.
    // (The actual value is between 5 and 9.)
    assert!(m >= 5);
    assert!(m <= 9);
    eprintln!("f(2, 3) = {} (brute-force exact value over universe size 5)", m);
}
