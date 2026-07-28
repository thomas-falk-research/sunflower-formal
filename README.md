# Sunflower-Formal

A self-contained Coq formalization of the **Erdős–Rado sunflower
problem** — machine-checked proofs of the classical upper bound, the
matching exponential lower bound, the first nontrivial exact value
`f(2,3) = 7`, the **deterministic half of the 2020 (ALWZ / Rao) spread
proof**, constructive Hall and Kőnig theorems for the supporting
matching theory, and a precise formal statement of the open
conjecture — together with a Rust computational companion that
cross-checks the small cases by brute force, and a testing layer
aimed at the errors the kernel cannot catch.

Everything compiles with stock **Coq 8.18** and the standard library
only (no Mathematical Components, no Flocq, no plugins beyond `lia`).
Every closed theorem reports **`Closed under the global context`**
under `Print Assumptions`: zero admits, and a single named axiom in
the whole development — the published 2020 **spread lemma**, cited and
quarantined in `coq/ALWZ.v`, used by nothing except the one theorem
that is explicitly derived from it.

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
| **Spread reduction** (ALWZ §4 / Rao) | "$r$-spread $\Rightarrow k$ disjoint members" $\Rightarrow f(n,k) \le r^n + 1$ | `coq/SpreadReduction.v` |
| **Bound via the spread framework** | $f(n,k) \le (n(k-1)+1)^n + 1$, **axiom-free** | `coq/SpreadReduction.v` |
| Hall's marriage theorem (1935) | constructive, Halmos–Vaughan induction | `coq/HallCore.v`, `coq/KoenigHall.v` |
| Kőnig's minimax theorem (1931) | max matching = min vertex cover (bipartite) | `coq/KoenigHall.v` |
| Pigeonhole counting lemma | used by the Erdős–Rado induction | `coq/Pigeonhole.v` |
| 2020 spread lemma | $r$-spread $\Rightarrow k$ disjoint members for $r \ge Ck\log(nk)$ — **the one named axiom**, cited | `coq/ALWZ.v` |
| ALWZ/Rao 2020 bound | $f(n,k) \le (Ck\log(nk))^n + 1$ — **derived** from that axiom alone | `coq/ALWZ.v` |
| The conjecture itself | formal statement, **open** | `coq/Conjecture.v` |
| Definition audit | complementarity of the bounds, encoding-invariance, non-vacuity of the axiom's shape | `coq/Audit.v` |
| Differential spread checker | a second decision procedure, proved to agree with the first | `coq/Reflect.v` |

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

- **The deterministic half of the 2020 proof.** The modern argument
  splits into a *reduction* and a *spread lemma*. The reduction —
  "every $r$-spread family of small sets contains $k$ pairwise
  disjoint members" implies $f(n,k) \le r^n + 1$ — is proved here in
  full (`spread_reduction`), by the spread/link dichotomy: either the
  family is spread, or some set $T$ is over-represented and one
  recurses into the link $\{A \setminus T : T \subseteq A\}$, lifting
  any sunflower back by merging $T$ into the core. The dichotomy is
  decided constructively (no excluded middle) by searching the
  sublists of members, and the lift needed a set-indexed
  generalisation of the single-element `sunflower_lift`. This replaces
  what used to be an axiom asserting the *whole 2020 bound*: the axiom
  is now the spread lemma alone.

  The reduction is not left hanging off an assumption. An elementary
  spread lemma is proved outright (`elementary_spread_disjoint`: the
  parameter $r = n(k-1)+1$ works, by maximal disjoint cover plus
  pigeonhole), and feeding it through the reduction gives an
  **unconditional** $f(n,k) \le (n(k-1)+1)^n + 1$ — Erdős–Rado
  quality, slightly weaker than the 1960 bound by a factor $e^n$, but
  proved along the modern route rather than the classical one.

  The axiom is stated as **Rao's Lemma 2 verbatim**, in his absolute
  form of spreadness ("every nonempty $Z$ lies in at most $r^{n-|Z|}$
  members") together with his size hypothesis — checked against the
  paper, not reconstructed from memory. That form is *stronger* than
  the fractional condition (`RaoSpread_Spread` proves the implication),
  so assuming the conclusion under it is the weaker assumption.

  Along the way the previous file's definition of spreadness turned
  out to be *degenerate* — it quantified over lists with repeated
  entries, which forces every member of the family to be empty. That
  is now recorded as a theorem (`w_spread_legacy_degenerate`) rather
  than silently corrected, and a concrete family satisfying every
  hypothesis of the axiom (with the conclusion) is certified by
  `vm_compute` as a standing non-vacuity guard.

- **Testing what the kernel cannot check.** Both errors this
  development has produced were errors of *statement*, not of proof: a
  spread definition that quantified over lists with repeats and so
  forced every member to be empty, and an axiom stated with the
  fractional spread condition where the source uses the absolute one.
  Neither could fail a build. Four mechanisms now target that class of
  error — coherence theorems that would derive `False` if two of the
  development's own bounds contradicted each other (`coq/Audit.v`); a
  second, independently-implemented spread decision procedure proved
  to agree with the first (`coq/Reflect.v`); an exhaustive search for
  counterexamples to the axiom's shape over small ground sets
  (`make testbed`); and mutation testing of the definitions
  (`make mutants`), which weakens one hypothesis at a time and checks
  that something breaks. Of 23 mutations, 22 are killed outright and
  one is killed only at the level of tactics — a distinction the
  harness verifies by applying declared repairs, rather than asserting.
  See [`docs/testing.md`](docs/testing.md).

  The search found the five-cycle, which is now a theorem: together
  with the disjoint-blocks family it shows the axiom's conclusion is
  *false* below `r = k-1`, while `spread_disjoint_above_elementary`
  shows it is *true* above `r = n(k-1)`. The axiom asserts something
  about the gap in between — neither vacuous nor already proved.

- **The conjecture, restated without sunflowers.** Because the
  reduction is lossless — it gives exactly $r^n$ — a spread lemma whose
  threshold does not grow with $n$ would settle the conjecture.
  `spread_conjecture_suffices` proves that implication, turning the
  \$1000 problem into: *is there, for each $k$, a constant $c_k$ such
  that every $c_k$-spread family of more than $c_k^{\,n}$ sets of size
  $n$ has $k$ pairwise disjoint members?*

## Verifying

```bash
make verify        # builds all 19 Coq files, then runs the axiom audit
```

Expected: every audited theorem (51 of them, including `f_2_3_eq_7`,
`hall_marriage_theorem`, `koenig_theorem`,
`lower_bound_exponential`, `spread_reduction`, `spread_erdos_rado`)
reports

```
Closed under the global context
```

followed by an `axiom-audit` section printing the *full statement* of
the one axiom the modern bound rests on, so what is being trusted is
visible in the build log rather than buried in a source file:

```
  [axiom-dep] Axioms:
  [axiom-dep] Rao20_lemma2
  [axiom-dep]   : exists alpha : nat,
  [axiom-dep]       1 <= alpha /\
  [axiom-dep]       (forall n k r : nat, ... -> SpreadYieldsDisjoint n k r)
```

CI gates on the count, on no closed theorem listing `Axioms:`, and on
exactly one axiom name appearing under the modern bound.

Requirements: Coq 8.18 (`apt-get install coq` on Ubuntu 24.04).
The Rust cross-checks (brute-force assertions tying the formal bounds
to concrete instances, plus the falsification testbed below):

```bash
cd rust && cargo test --release
```

Two further checks target what `Print Assumptions` cannot see — whether
the *definitions* say what their names claim:

```bash
make mutants       # weaken each definition in turn; see what breaks
make testbed       # exhaustive falsification of the spread hypothesis
```

Both are CI jobs. The methodology, and what it does and does not
cover, is in [`docs/testing.md`](docs/testing.md).

Per-theorem status, including exactly what is and is not proved, is
tracked in [`STATUS.md`](STATUS.md); what is worth doing next, and
what to avoid, is in [`docs/roadmap.md`](docs/roadmap.md).

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
  sunflower number (such as `f(2,3) = 7`), of the exponential lower
  bound, or of any part of the post-2020 spread argument in any
  system, nor a sunflower development in Coq. This was a targeted
  search, not a systematic one; corrections are welcome and will be
  credited.

This repository's distinct contribution is therefore modest and
specific: a single self-contained, stdlib-only Coq account of the
sunflower problem's provable frontier — both bounds, the exact
values, the deterministic half of the modern (2020) argument, the
supporting matching theory built without any graph library — with a
machine-auditable trust story (one cited axiom, and a printed
derivation of exactly what depends on it).

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
headline theorem, with `make mutants` and `make testbed` attacking the
definitions themselves. The one axiom in the development is a *published*
theorem (ALWZ 2020) recorded as such, not a gap being papered over.

## License

MIT — see [`LICENSE`](LICENSE).
