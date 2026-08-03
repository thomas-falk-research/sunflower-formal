//! Sunflower-formal: computational companion.
//!
//! This crate provides a brute-force search for k-sunflowers in a
//! finite family of finite sets, and a tabulator that computes the
//! exact value of f(n, k) for small inputs by enumerating all
//! candidate families up to the Erdős-Rado upper bound.
//!
//! The crate exists to cross-check the Coq formalization on concrete
//! parameters. A failing assertion in `tests/small_cases.rs` would
//! indicate either:
//!   1. A bug in the brute-force search here, or
//!   2. A genuine refutation of the Coq theorem (whose proofs are
//!      machine-checked and known to terminate without admits).
//!
//! Tests in `tests/small_cases.rs` exercise the bounds proved in the
//! Coq layer: every distinct n-uniform family of size > (k-1)^n n!
//! contains a k-sunflower (upper bound), and the family of k-1
//! disjoint blocks has no k-sunflower (lower bound).

pub mod sunflower;
pub mod bounds;
pub mod chvatal_hanson;
pub mod construction;
pub mod extend;
pub mod ground;
pub mod intersecting;
pub mod link;
pub mod orbit;
pub mod plateau;
pub mod ratio;
pub mod rstar;
pub mod sat;
pub mod shift;
pub mod spread;
pub mod structure;
pub mod testbed;
pub mod wide;

pub use sunflower::{find_k_sunflower, is_k_sunflower, Sunflower};
pub use bounds::{erdos_rado_bound, f_nk_exact};
pub use construction::{disjoint_blocks, product_family};
pub use spread::{has_k_disjoint, is_rao_spread, matching_number};
pub use testbed::{find_counterexample, search, verify_counterexample};
