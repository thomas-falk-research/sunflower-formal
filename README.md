# Sunflower-Formal

A self-contained Coq formalization of the **Erdős–Rado sunflower
problem** — machine-checked proofs of the classical upper bound, the
matching exponential lower bound, the first nontrivial exact value
`f(2,3) = 7`, constructive Hall and Kőnig theorems for the supporting
matching theory, and a precise formal statement of the open
conjecture — together with a Rust computational companion that
cross-checks the small cases by brute force.

Everything compiles with stock **Coq 8.18** and the standard library
only (no Mathematical Components, no Flocq, no plugins beyond `lia`).
Every closed theorem reports **`Closed under the global context`**
under `Print Assumptions`: zero admits, and a single named axiom in
the whole development — the published Alweiss–Lovett–Wu–Zhang 2020
bound, cited and quarantined in `coq/Spread.v`, used by nothing.

## The problem

Let $f(n, k)$ be the smallest integer such that every family
$\mathcal{F}$ of distinct $n$-element sets with
$|\mathcal{F}| \ge f(n, k)$ contains a $k$-sunflower (a
$k$-Δ-system): $k$ distinct sets whose pairwise intersections all
equal a common *core*.

**The open conjecture (Erdős–Rado 1960; Erdős's \$1000 prize for
$k = 3$):** $f(n,k) \le c_k^{\,n}$ for a constant $c_k$ depending
only on $k$.

## Honest status

The Sunflower Conjecture is **open**. This repository does **not**
claim progress on it. What is machine-checked here is the complete
*provable frontier* around it:

| Result | Statement | File |
|---|---|---|
| Erdős–Rado upper bound (1960) | $f(n,k) \le (k-1)^n\, n! + 1$ | `coq/ErdosRado.v` |
| Exponential lower bound (1960) | $f(n,k) \ge (k-1)^n + 1$ | `coq/ProductLowerBound.v` |
| Boundary exact values | $f(n,2) = 2$, $\; f(1,k) = k$ | `coq/SmallCases.v` |
| **Exact value at $k=3$** | $f(2,3) = 7$ | `coq/F23.v` |
| Hall's marriage theorem (1935) | constructive, Halmos–Vaughan induction | `coq/HallCore.v`, `coq/KoenigHall.v` |
| Kőnig's minimax theorem (1931) | max matching = min vertex cover (bipartite) | `coq/KoenigHall.v` |
| Pigeonhole counting lemma | used by the Erdős–Rado induction | `coq/Pigeonhole.v` |
| ALWZ 2020 bound | $f(n,k) \le (Ck\log n)^n$ — **named axiom**, cited, unused | `coq/Spread.v` |
| The conjecture itself | formal statement, **open** | `coq/Conjecture.v` |

So the function is bracketed
$(k-1)^n + 1 \le f(n,k) \le (k-1)^n\, n! + 1$, with exact values at
the boundary cases and at $(n,k) = (2,3)$ — $k = 3$ being the case
Erdős singled out as containing "the whole difficulty."

Highlights of the less-routine parts:

- **`f(2,3) = 7`** (`f_2_3_eq_7 : UpperBound 2 3 7 /\ ~ UpperBound 2 3 6`).
  The upper bound is a constructive counting argument: a 2-uniform
  family without a 3-sunflower has maximum degree ≤ 2 and no three
  pairwise-disjoint members, and an incidence double-count over a
  maximal disjoint pair forces at most 6 members. The lower bound is
  the two-disjoint-triangles family, certified by a reflective
  boolean sunflower detector (proved *complete* for
  `ContainsKSunflower 3`) evaluating to `false` under `vm_compute`.
  The value itself is classical.
- **Hall and Kőnig without a graph library.** Hall's theorem is
  proved over a bare adjacency function and vertex lists by the
  Halmos–Vaughan induction, with criticality decided by brute-force
  enumeration of subsequences; Kőnig's theorem follows via the
  deficiency form (fresh dummy vertices restore Hall's condition, and
  the easy direction `matching_le_cover` upgrades the resulting
  matching/cover pair to optimal).
- **Canonical-representation techniques.** The exponential lower
  bound's product family has strictly-descending members, so
  set-equality collapses to literal equality — which turns the
  no-sunflower argument into pigeonhole on top-block values plus a
  head-stripping induction.

## Verifying

```bash
make verify        # builds all 15 Coq files, then runs the axiom audit
```

Expected: every audited theorem (16 of them, including `f_2_3_eq_7`,
`hall_marriage_theorem`, `koenig_theorem`,
`lower_bound_exponential`) reports

```
Closed under the global context
```

Requirements: Coq 8.18 (`apt-get install coq` on Ubuntu 24.04).
The Rust cross-checks (22 brute-force assertions tying the formal
bounds to concrete instances):

```bash
cd rust && cargo test --release
```

Per-theorem status, including exactly what is and is not proved, is
tracked in [`STATUS.md`](STATUS.md).

## Design notes

Finite sets are `NoDup` lists of `nat`; families are lists of sets;
set-equality (`SetEq`) is mutual inclusion, and family distinctness
(`SetNoDup`) is "no two members set-equal" — the right notion for
non-canonical list representations. This keeps the whole development
elementary and stdlib-only at the cost of some bookkeeping; the
`witness` canonicalization in `coq/LowerBound.v` bridges abstract
(up-to-`SetEq`) sunflowers to literal subfamilies where counting
arguments live.

## Relation to prior formalizations

These are classical theorems, and most have been machine-checked
before. A targeted (though not exhaustive) check of the usual venues,
done before publishing this repository:

- **Erdős–Rado sunflower lemma**: formalized in Isabelle/HOL by René
  Thiemann — [AFP entry *Sunflowers*](https://www.isa-afp.org/entries/Sunflowers.html)
  (2021). That entry proves the classical upper bound; it does not
  cover the exponential lower bound, exact values, or the ALWZ 2020
  improvement. Lean's mathlib has no sunflower development as of
  mid-2026 (the conjecture is listed as an open formalization target
  in the [formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
  tracker).
- **Hall's marriage theorem**: Isabelle —
  [AFP entry *Marriage*](https://www.isa-afp.org/entries/Marriage.html)
  (Jiang–Nipkow 2010, containing the same Halmos–Vaughan proof used
  here, plus Rado's); Lean —
  [`Mathlib.Combinatorics.Hall.Basic`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/Hall/Basic.html)
  (which even drops the finite-index restriction via a compactness
  argument); and Coq — together with **Kőnig's theorem**, as
  corollaries of Menger's theorem in the MathComp-based
  [coq-community/graph-theory](https://github.com/coq-community/graph-theory)
  library.
- We did **not** find a machine-checked proof of an exact nontrivial
  sunflower number (such as `f(2,3) = 7`) or of the exponential lower
  bound in any system, nor a sunflower development in Coq. This was a
  targeted search, not a systematic one; corrections are welcome and
  will be credited.

This repository's distinct contribution is therefore modest and
specific: a single self-contained, stdlib-only Coq account of the
sunflower problem's provable frontier — both bounds, the exact
values, the supporting matching theory built without any graph
library — with a machine-auditable trust story (one cited axiom, used
by nothing).

## References

See [`docs/references.md`](docs/references.md) for the full list. Key
sources: Erdős–Rado, *Intersection theorems for systems of sets*,
J. London Math. Soc. 35 (1960); P. Hall, *On representatives of
subsets*, J. London Math. Soc. 10 (1935); D. Kőnig, *Gráfok és
mátrixok*, Mat. Fiz. Lapok 38 (1931); Halmos–Vaughan, *The marriage
problem*, Amer. J. Math. 72 (1950); Abbott–Hanson on finite
Δ-systems, Discrete Math. (1974); Alweiss–Lovett–Wu–Zhang, *Improved
bounds for the sunflower lemma*, STOC 2020, with the
Rao / Frankston–Kahn–Narayanan–Park / Bell–Chueluecha–Warnke
refinements.

## Methods note

The proofs in this repository were developed with substantial AI
assistance (Anthropic's Claude), directed and reviewed by the
maintainer. Correctness does not rest on how the proofs were
written: every theorem is independently checked by the Coq kernel,
and the `make verify` audit prints the assumption set of each
headline theorem. The one axiom in the development is a *published*
theorem (ALWZ 2020) recorded as such, not a gap being papered over.

## License

MIT — see [`LICENSE`](LICENSE).
