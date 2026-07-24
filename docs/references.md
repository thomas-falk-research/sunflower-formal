# Annotated bibliography

Original sources, refinements, and surveys on the Sunflower
Conjecture. Cross-referenced from `coq/Spread.v`,
`coq/Conjecture.v`, and `docs/proof_strategies.md`.

## Original problem

- **[ErRa60]** P. Erdős and R. Rado, *Intersection theorems for systems
  of sets*. Journal of the London Mathematical Society 35 (1960),
  85–90. Defines $f(n, k)$ and proves $f(n, k) \leq (k-1)^n n! + 1$.

- **[Er65b]** P. Erdős, *Extremal problems in number theory*. AMS
  Proc. Symp. Pure Math. (1965). Mentions the conjecture.

- **[Er69]** P. Erdős, *Problems and results in chromatic graph
  theory*. Proof Techniques in Graph Theory (Academic Press, 1969).

- **[Er71]** P. Erdős, *Some unsolved problems in graph theory and
  combinatorial analysis*. Combinatorial Math. and its Applications
  (Academic Press, 1971), pp. 97–109.

- **[Er73]** P. Erdős, *On the combinatorial problems which I would
  most like to see solved*. Combinatorica 1 (1981), 25–42.

- **[Er78]** P. Erdős, *Some old and new problems in combinatorial
  analysis*. Congressus Numerantium 21 (1978), 35.

- **[Er81]** P. Erdős, with the $1000 prize for the $k = 3$ case.

- **[Er90, Er95, Er97c, Er97d]** Further restatements by Erdős in
  various combinatorics proceedings.

## Pre-2020 partial results

- **[Ko97]** A. V. Kostochka, *An intersection theorem for systems of
  finite sets*. Acta Math. Hungarica 75 (1997), 81–88. Refinement to
  $o(n!)$, won the consolation $100 prize.

- **[KRT99]** A. V. Kostochka, V. Rödl, L. A. Talysheva, *On systems
  of small sets with no large $\Delta$-subsystem*. Combinatorics,
  Probability and Computing 8 (1999), 81–88. The large-$k$
  asymptotic.

## 2020 breakthrough and refinements

- **[ALWZ20]** R. Alweiss, S. Lovett, K. Wu, J. Zhang, *Improved
  bounds for the sunflower lemma*. STOC 2020. arXiv 1908.08483.
  Establishes $f(n, k) \leq (C k \log n)^n$, replacing the $n!$
  factor.

- **[Ra20]** A. Rao, *Coding for sunflowers*. Discrete Analysis 2020.
  arXiv 1909.04774. Alternative proof with similar bound.

- **[FKNP19]** K. Frankston, J. Kahn, B. Narayanan, J. Park,
  *Thresholds versus fractional expectation-thresholds*. Annals of
  Mathematics 2021. arXiv 1910.13433. Resolves Talagrand's
  expectation-threshold conjecture, which implies a sunflower bound.

- **[BCW21]** T. Bell, S. Chueluecha, L. Warnke, *Note on sunflowers*.
  Discrete Mathematics 344 (2021). Refines the constant.

- **[Hu]** L. Hu, exposition/blog streamlining the proof.

- **[Stoeckl]** S. Stoeckl, presentation achieving $C = 64$ in the
  streamlined proof.

## Surveys and textbooks

- **[Va99]** A. Vaintrob, *Algebraic structures and the Sunflower
  Conjecture*. (1999), Section 3.63 in some unpublished or online
  notes, mentioned in the open-problems list as [Va99, 3.63].

- *Open Problem Garden* (openproblemgarden.org), problem on sunflowers.

- *Erdős Problems* (erdosproblems.com), problem #20 on sunflowers
  (the source of the problem statement reproduced in `README.md`).

## Coq / formal-verification context

This is, to the best knowledge of the authors at the time of
writing, the only fully machine-checked formalisation of the
Erdős–Rado 1960 upper bound. We are unaware of any Mathematical
Components or Mathlib formalisation of this theorem.

If a Coq or Lean formalisation of the ALWZ 2020 spread-family bound
becomes available, the axiom `ALWZ20_spread_bound` in
`coq/Spread.v` can be replaced by an import.
