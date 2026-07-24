# The spread-family framework (ALWZ–Rao–FKNP–BCW)

This document is an exposition of the 2020 breakthrough on the
Sunflower Conjecture. The full proof of the spread lemma is not
formalised in the Coq layer of this development; it is recorded as
the axiom `ALWZ20_spread_bound` in `coq/Spread.v` with the citation
below. Nothing in `coq/ErdosRado.v`, `coq/LowerBound.v`,
`coq/SmallCases.v`, or `coq/Conjecture.v` depends on this axiom.

## Spread families

For a finite family of sets $\mathcal{F}$ over a universe $[N]$ and a
positive real $w$, $\mathcal{F}$ is **$w$-spread** if for every $T
\subseteq [N]$,

$$|\{A \in \mathcal{F} : T \subseteq A\}| \leq \frac{|\mathcal{F}|}{w^{|T|}}.$$

That is, no point $T$ is "over-represented" — the fraction of
$\mathcal{F}$ containing $T$ decreases like $w^{-|T|}$.

Coq formalisation: `coq/Spread.v` definition `w_spread`.

Intuition. If $w$ is large, $\mathcal{F}$ is "spread out" — no small
set is in too many members. A uniformly-random member of
$\mathcal{F}$ contains a uniformly-random element of $[N]$ with
probability $\approx n / N$, but no specific element with
disproportionate frequency.

## The spread lemma

**Theorem (ALWZ 2020, FKNP 2019, Rao 2020, BCW 2021).** There exists
an absolute constant $C$ such that the following holds. Let
$\mathcal{F}$ be a $w$-spread $n$-uniform family with $w \geq C \log
n$. Let $R \subseteq [N]$ be a uniformly-random subset of size
$\lceil n / 2 \rceil$. Then with probability $\geq 1/2$, $R$ contains
some member of $\mathcal{F}$.

(Different sources state it with slightly different constants and
exact formulations. The version above is the FKNP / BCW form.)

**Consequence for the sunflower problem.** Suppose $\mathcal{F}$ is
an $n$-uniform family with $|\mathcal{F}| > (Ck \log n)^n$ and *no*
$k$-sunflower. By a standard reduction one may pass to a "kernel"
where $\mathcal{F}$ is $w$-spread for $w = Ck \log n$. The spread
lemma then implies a random small subset contains many distinct
members of $\mathcal{F}$, which forces a sunflower structure
contradicting the hypothesis.

## Why this doesn't resolve the conjecture

The conjecture asks for $f(n, k) \leq c_k^n$ with $c_k$ independent
of $n$. The spread lemma gives $(C k \log n)^n$, with a $\log n$
factor inside the base of the exponent.

Where does $\log n$ come from? It is the spread threshold needed for
the probabilistic argument to succeed: a $w$-spread family needs
$w = \Omega(\log n)$ for a random subset of size $O(n)$ to contain a
member with constant probability. This is a combinatorial fact about
"covering" random subsets, established via concentration
inequalities.

Removing the $\log n$ would mean either:
- A spread threshold of $O(1)$ suffices for the covering argument
  (open).
- A different argument entirely bypasses the spread lemma (open).

## Provenance and references

The key papers, in order of refinement:

- **[ALWZ20]** R. Alweiss, S. Lovett, K. Wu, J. Zhang, "Improved
  bounds for the sunflower lemma", *STOC 2020* (also arXiv
  1908.08483). The original 2020 breakthrough.

- **[Ra20]** A. Rao, "Coding for sunflowers", *Discrete Analysis*
  2020 (arXiv 1909.04774). Alternative proof.

- **[FKNP19]** K. Frankston, J. Kahn, B. Narayanan, J. Park,
  "Thresholds versus fractional expectation-thresholds", *Annals of
  Mathematics* 2021 (arXiv 1910.13433). Related expansion result.

- **[BCW21]** T. Bell, S. Chueluecha, L. Warnke, "Note on sunflowers",
  *Discrete Mathematics* 2021. Refinement.

- **[Hu]** L. Hu, blog/note streamlining the proof.

- **[Stoeckl]** S. Stoeckl, presentation reaching $C = 64$ in the
  final constant.

Earlier work on the lower-order regime:

- **[Ko97]** A. V. Kostochka, "An intersection theorem for systems of
  finite sets", *Acta Math. Hungarica* 1997. The Kostochka
  refinement, which won the consolation Erdős prize.

- **[KRT99]** A. V. Kostochka, V. Rödl, L. A. Talysheva, "On systems
  of small sets with no large $\Delta$-subsystem", *Combinatorics,
  Probability and Computing* 1999. Asymptotic in the large-$k$
  regime.

Original sources:

- **[ErRa60]** P. Erdős, R. Rado, "Intersection theorems for systems
  of sets", *J. London Math. Soc.* 35 (1960), 85–90. Defines the
  function and proves the original $(k-1)^n n!$ upper bound.

- **[Er81]** P. Erdős, "On the combinatorial problems which I would
  most like to see solved", *Combinatorica* 1 (1981), 25–42. The
  $1000 prize for $k = 3$ is stated here.

## What a Coq proof of the spread lemma would need

To replace `ALWZ20_spread_bound` with a proof, one would need:

1. A real-analysis layer for finite-probability arguments. Coquelicot
   provides `Hierarchy` and `Series` modules; Mathematical Components
   provides `mathcomp-analysis`. Either could underpin the
   probabilistic step.

2. Lemmas about uniformly-random subsets of a finite universe:
   inclusion probabilities, Bernoulli inequality, etc.

3. The "shatter" argument: given a $w$-spread family, the probability
   that a uniform random subset of size $cn$ contains some member is
   $\geq 1/2$. This is a moment / second-moment / coupling argument.

4. The reduction from sunflower-free to $w$-spread, which involves
   passing to a "kernel" subfamily and iterating.

We estimate this would take several hundred to a thousand lines of
Coq plus an analysis layer; outside the scope of this development.

## Summary

The spread-family framework is the current state of the art on
sunflower bounds, but does not resolve the open conjecture. The Coq
file `coq/Spread.v` records its key consequence as a named axiom
with citation; this serves as a clear interface for a future
mathematician who would replace the axiom with a proof.
