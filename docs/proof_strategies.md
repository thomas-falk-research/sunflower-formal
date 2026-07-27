# Proof strategies in the sunflower literature

This document surveys the four main approaches to the sunflower
problem, indicates which is formalized in this development, and
which remains open.

## 1. Erdős–Rado induction (1960) — **formalized**

The original argument; see `docs/problem.md` for the full text and
`coq/ErdosRado.v` for the Coq proof.

The argument has two pieces:

1. **Cover lemma**: every family of nonempty sets has a sub-family
   that is pairwise-disjoint *and* every set in the original family
   meets some member of the sub-family. (Greedy construction.) See
   `coq/ErdosRado.v` lemma `max_disjoint_cover`.

2. **Pigeonhole step**: if the cover has fewer than $k$ members, the
   union has at most $(k-1)n$ elements, so by pigeonhole some
   element is in many sets, and induction on $n$ closes. See
   `coq/Pigeonhole.v` lemma `pigeonhole_family`.

Resulting bound: $f(n, k) \leq (k-1)^n n! + 1$.

In Coq this is `theorem erdos_rado_upper_bound` in
`coq/ErdosRado.v`. The `Print Assumptions` audit returns "Closed
under the global context" — zero axioms, zero admits.

## 2. Kostochka refinement (1997) — *not formalized*

Kostochka [Ko97] proved the Erdős–Rado bound can be improved to

$$f(n, k) \leq c_k \cdot \frac{n!}{(\log n / \log \log n)^n}$$

— a sub-$n!$ refinement. This won him the consolation prize of $100
from Erdős. The argument tracks the constant in the Erdős–Rado
recursion more carefully and uses extremal-graph machinery.

This refinement is mentioned in `STATUS.md`'s open table but is not
formalised here. The proof is roughly the same shape as
Erdős–Rado's but with tighter quantitative accounting.

## 3. Alweiss–Lovett–Wu–Zhang spread lemma (2020) — **stated, not proved**

The 2020 breakthrough replaced the $(k-1)^n n!$ bound with
$(C k \log n)^n$.

The strategy:

1. Reformulate: a "spread distribution" on the family lets us argue
   probabilistically.

2. Show: a $w$-spread $n$-uniform family of size $> w^n$ can be
   "shattered" by a uniformly-random subset of size $O(n \log w / w)$.

3. By contradiction, show: a $w$-spread family with $|\mathcal{F}| >
   (C k \log n)^n$ and $w$ moderately large must contain a
   $k$-sunflower (else apply the shattering argument and contradict
   $\sum_i |A_i|$).

The argument splits into a *reduction* (step 3, deterministic) and a
*spread lemma* (steps 1–2, the analytic content). **The reduction is
formalised** in `coq/SpreadReduction.v` as `spread_reduction`, and it
gives exactly $f(n,k) \le r^n + 1$ for the spread threshold $r$. Only
the spread lemma is assumed, as the named axiom
`Rao20_spread_lemma` in `coq/ALWZ.v`; the modern bound is then
*derived* from it. No other theorem depends on the axiom, and the
same reduction — instantiated with an elementary spread lemma proved
in full — yields an unconditional bound $f(n,k) \le (n(k-1)+1)^n + 1$.
See `docs/spread_framework.md`.

The original ALWZ proof of the spread lemma is probabilistic, but
Rao's is not: "Coding for sunflowers" gives an encoding/counting
proof using only injections between finite sets and binomial
estimates, which is why discharging the remaining axiom is a
realistic target for this stdlib-only development.

Refinements:
- Rao 2020 [Ra20]: alternative streamlined proof, same constant up
  to logarithmic factors.
- Frankston–Kahn–Narayanan–Park 2019 [FKNP19]: a related expansion
  argument resolving "Talagrand's expectation threshold conjecture"
  (which implies the sunflower bound).
- Bell–Chueluecha–Warnke 2021 [BCW21]: further refinement, achieves
  current record up to small constants.
- Hu [Hu]: streamlined exposition.
- Stoeckl: constant $C = 64$ in a presented walkthrough.

## 4. Direct combinatorial constructions for lower bounds

### Trivial: $f(n, k) \geq k$ — **formalized**

`coq/LowerBound.v` theorem `lower_bound_trivial`. Construction:
$k - 1$ disjoint blocks of $n$ consecutive integers.

### Standard exponential: $f(n, k) \geq (k-1)^n + 1$ — *not formalized*

Product-family construction; described in `docs/problem.md` and
verified computationally for small parameters by
`rust/tests/small_cases.rs`. A full Coq proof would need:

1. Define `product_family kk n offset` (the family of systems of
   representatives across $n$ rows of width $kk$).

2. Show it is $(kk^n)$-many, $n$-uniform, strictly-sorted (hence
   SetNoDup).

3. The "no $k$-sunflower" argument: at each row, $k$-many
   $\phi_j$-values must either all agree or all disagree; the
   "all disagree" case has $k$ distinct values in $[0, kk)$ with
   $kk = k - 1$, contradicting pigeonhole.

Step 3 is the substantive content; steps 1–2 are bookkeeping. We
elected to formalise the weaker (k-1) bound to keep the codebase
focused.

### Kostochka–Rödl–Talysheva large-$k$ asymptotic

[KRT99]: when $k = k(n)$ grows with $n$, the optimum is

$$f(n, k) = (1 + O(k^{-1/2} n)) \cdot k^n.$$

Not relevant to the fixed-$k$ regime of the main conjecture.

## Summary of what is rigorously proved here

| Bound | Direction | File | Status |
|-------|-----------|------|--------|
| $f(n, k) \leq (k-1)^n n! + 1$ | upper | `coq/ErdosRado.v` | **proved, zero admits** |
| $f(n, k) \geq k$ | lower | `coq/LowerBound.v` | **proved, zero admits** |
| $f(n, 2) = 2$ | exact | `coq/SmallCases.v` | **proved, zero admits** |
| $f(1, k) = k$ | exact | `coq/SmallCases.v` | **proved, zero admits** |
| $f(n, k) \geq (k-1)^n + 1$ | lower | `coq/ProductLowerBound.v` | **proved, zero admits** |
| $f(n, k) \leq (n(k-1)+1)^n + 1$ | upper | `coq/SpreadReduction.v` | **proved, zero admits** (via the spread framework) |
| spread $\Rightarrow$ sunflower reduction | — | `coq/SpreadReduction.v` | **proved, zero admits** |
| $f(n, k) \leq (C k \log(nk))^n$ | upper | `coq/ALWZ.v` | derived from the one named axiom (the spread lemma) |
| $f(n, k) \leq c_k^n$ (conjecture) | upper | `coq/Conjecture.v` | open since 1960 |
