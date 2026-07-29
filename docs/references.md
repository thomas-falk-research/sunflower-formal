# Annotated bibliography

Original sources, refinements, and surveys on the Sunflower
Conjecture. Cross-referenced from `coq/Spread.v`, `coq/ALWZ.v`,
`coq/Conjecture.v`, `coq/TwoUniform.v`, `coq/CliqueLowerBound.v`, and
`docs/proof_strategies.md`.

Two results here are *used* rather than merely cited: [Ra20] Lemma 2,
which is the development's one axiom, and [ChHa76], which is not
formalised at all and which no theorem in the development depends on —
it is the source of the numbers `rust/src/chvatal_hanson.rs` computes
and of the claim that those numbers are the truth rather than an upper
estimate. Both are marked below.

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

## Uniformity 2: the extremal function behind $f(2,k)$

- **[ChHa76]** V. Chvátal and D. Hanson, *Degrees and matchings*.
  Journal of Combinatorial Theory Series B 20 (1976), 128–138.
  Evaluates the largest number of edges in a simple graph with maximum
  degree at most $D$ and matching number at most $\nu$:

  $$\mathrm{CH}(D,\nu) \;=\; \nu D + \left\lfloor \tfrac{D}{2} \right\rfloor
     \left\lfloor \frac{\nu}{\lceil D/2 \rceil} \right\rfloor .$$

  Their proof has a linear-programming flavour and goes through Berge's
  matching formula. The extremal graphs are disjoint unions of
  *odd near-regular* components — a maximum-degree-$D$ graph on
  $2\lceil D/2 \rceil + 1$ vertices — together with stars $K_{1,D}$
  spending the leftover matching budget; at $D = \nu = k-1$ with $k$
  odd this is two disjoint copies of $K_k$.

  **Not formalised, and nothing in the Coq development depends on it.**
  `coq/TwoUniform.v` proves the *identification* — that a distinct
  2-uniform family avoids $k$-sunflowers exactly when these two
  parameters are at most $k-1$, and that `RaoSpread 2 F r` is the
  degree bound — which is what makes $f(2,k)$ this extremal problem.
  Given [ChHa76], that yields $f(2,k) = \mathrm{CH}(k-1,k-1)+1$ and a
  sharp spread threshold $r^*(2,k) = k$; the repository proves the
  lower half outright for odd $k$ (`coq/CliqueLowerBound.v`) and treats
  the rest as cited. The formula is falsified against exhaustive search
  in `rust/tests/chvatal_hanson.rs` rather than taken on trust.

  The problem was posed by Erdős and Rado, which is why it turns up
  here at all.

- **[BaKh09]** N. Balachandran and N. Khare, *Graphs with restricted
  valency and matching number*. Discrete Mathematics 309 (2009),
  4176–4180. A second, **constructive** proof of the [ChHa76] bound,
  five pages, which also characterises the extremal graphs and the
  cases where they are unique.

  Found by a literature check scoped to one question: does the
  [ChHa76] upper bound need Gallai–Edmonds, or would a clever
  induction do? The answer is that it needs the matching-theory
  primitive either way. This paper's own keywords are *Gallai's lemma*
  and *factor-critical graph*, and it contains a new proof of Gallai's
  lemma — so the dependency is not an artefact of Chvátal and Hanson's
  linear-programming presentation, and the two published proofs agree
  on what the bound rests on.

  That is still much less than the full Gallai–Edmonds structure
  theorem: Gallai's lemma is one statement ("a connected graph in which
  every vertex is missed by some maximum matching is factor-critical")
  with a self-contained alternating-path proof. See `docs/roadmap.md`
  §3a for what that means for scoping. The paper is paywalled and no
  preprint was found, so its proof was **not** read — what is recorded
  here is its abstract and keywords, and the description of it in the
  papers that cite it.

- **[AbHa74]** H. L. Abbott and D. Hanson, *On finite $\Delta$-systems*.
  Discrete Mathematics 8 (1974), 1–12. The source usually credited for
  the small exact values, including $f(2,3) = 7$ (`coq/F23.v`).

- **[NaSa17]** E. Naslund, W. Sawin, *Upper bounds for sunflower-free
  sets*. Forum of Mathematics Sigma 5 (2017), e15. The slice-rank
  method — the machinery that settled cap set — applied to the sunflower
  problem: a 3-sunflower-free family of subsets of $[n]$ has at most
  $3(n+1)C^n$ members with $C = 3/2^{2/3} < 1.89$. A $constant^n$ bound
  of exactly the conjectured shape, but in the **ground set** rather
  than the uniformity. `coq/SliceRank.v` carries it as a hypothesis
  (not an axiom) and proves that one further fact — that extremal
  uniform families live on $O(m)$ points — would turn it into the
  conjecture at $k = 3$. Constant confirmed against the abstract and
  against a later paper improving the polynomial factor; the proof was
  not read.

- **[AHS72]** H. L. Abbott, D. Hanson, N. Sauer, *Intersection theorems
  for systems of sets*. Journal of Combinatorial Theory Series A 12
  (1972), 381–389. The best classical lower bound at $k = 3$:
  $f(n,3) \gtrsim 10^{n/2 - c\log n}$, i.e. a rate of
  $10^{1/2} = 3.162\ldots$ per point. The mechanism is a *substitution*
  recursion $g(ab) \ge g(a)\,g(b)^a$, strictly stronger than the direct
  sum $g(a+b) \ge g(a)g(b)$ that `coq/DirectSum.v` proves and that only
  reaches $6^{1/2} = 2.449\ldots$. See `docs/roadmap.md` §5 for what
  formalising it would need.

  **The paper was not read.** What is recorded here is from secondary
  sources; the rate and the recursion were checked against each other
  (the recursion's fixed point at $a = b = 3$ is $g(3)^{3/2}$, which is
  $10^{1/2}$ exactly when $g(3) = 10$), and they agree. The reported
  base case does not corroborate: $g(3,3) \ge 12$ already follows from
  the direct sum here. Read the paper before relying on any constant
  from it.

  **Corroborated since, against [Kup25].** The survey states the bound
  as $\phi(k,3) \ge 10^{k/2 - c\log k}$ and describes the mechanism in
  the same terms this repository reconstructed it: *"They used a
  construction of a 3-uniform family of size 10 and with no
  $\Delta(3)$-system, and then leveraged it to any uniformity using an
  iterated product construction, which gives a recursion
  $\psi(ab) \ge \psi(a)\psi(b)^a$."* So the recursion and the seed
  value 10 are both confirmed from a second source. Two things the
  survey does not say, and which the reconstruction here adds:

  * the **inner** family must be *intersecting* for the recursion to be
    valid — that is what makes the projection to the outer ground set a
    $\Delta$-system. `rust/tests/intersecting.rs` verifies the
    construction and includes a control showing it breaks the moment
    the inner family is not intersecting;
  * $\psi$ in the survey is "the size of their iterated construction",
    a property of *one* construction. Separating it into $g$ and the
    intersecting quantity $\iota$ is what makes
    `coq/IotaRate.v`'s sandwich say something about every construction
    rather than about theirs.

  The primary source is still unread and the $-c\log k$ correction term
  is taken on the survey's word.

- **[Kup25]** A. Kupavskii, *Delta-system method: a survey*.
  arXiv:2508.20132 (2025). A survey of the sunflower / $\Delta$-system
  method from Erdős–Rado 1960 to the present. Used here for two
  literature checks recorded in `docs/roadmap.md` §5:

  1. it corroborates the [AHS72] recursion and seed (above), **with a
     re-indexing that has to be done by hand**. The survey's own
     definition, read off the rendered page (1.1) rather than an
     extracted-text summary, is

     > $\phi(k,s) := \max\{|\mathcal F| : \mathcal F$ consists of sets of
     > size $\le k$ and $\mathcal F$ contains no $\Delta(s+1)$-system$\}$

     — the second argument is **one less than the petal count**, which the
     survey confirms by restating Erdős–Rado as $\phi(k,s) \le k!s^k$.
     Under that definition its [AHS72] sentences read: the lower bound is
     stated as $\phi(k,3) \ge 10^{k/2 - c\log k}$, i.e. about
     $\Delta(4)$-systems and compared against the trivial $3^k$, while the
     construction it cites is "a 3-uniform family of size 10 and with no
     $\Delta(3)$-system", i.e. 3 petals.

     That is **not** an inconsistency — a $\Delta(3)$-free family is
     $\Delta(4)$-free, so the sentence is true as written. It is simply
     not the statement usually attributed to [AHS72], which is the
     3-petal one: in the survey's notation $\phi(k,2) \ge 10^{k/2-c\log k}$,
     exponentially better than $2^k$. So "the 1972 bound is $10^{n/2}$ for
     3-sunflowers" is *derivable* from this survey but is not what the
     survey's sentence says, and anyone reading the constant off it should
     re-index first. The repository's own side is unaffected and is
     verified directly: $\iota(3) = 10$ is exhaustive and
     `rust/tests/intersecting.rs` checks that substituting an intersecting
     3-sunflower-free family preserves 3-sunflower-freeness. The
     $-c\log k$ correction term remains second-hand;

  2. it does **not** name an extremal function for *intersecting*
     sunflower-free families, and contains no reduction of the
     sunflower problem to intersecting families. That is a negative
     result from one survey, not a claim of novelty — see the
     "literature check" note in `docs/roadmap.md` §5 for exactly what
     was searched.

  Only the sections reachable from the arXiv HTML were read.

### Who evaluated $f(2,k)$ first

[Kup25] reports that [AHS72] "showed that $\phi(2,s) = s(s+1)$ for even
$s$ and $s^2 + \frac{s-1}{2}$ for odd $s$". Under [Kup25]'s own
definition (second argument = petals minus one) that is the largest
2-uniform family with no $(s+1)$-sunflower, i.e. $f(2,s+1) - 1$ in this
repository's notation. Checked against this repository's own
Chvátal–Hanson oracle in `rust/examples/ahs_convention.rs`, the quoted
formula equals $CH(s,s)$ **exactly** for every $s$ from 2 to 8 — and
`chvatal_hanson::f_2_k` computes $f(2,k) = CH(k-1,k-1) + 1$, so the two
agree with the offset the definition predicts.

[AHS72]'s own abstract says the paper "evaluates $\phi(2,k)$ for all
$k \ge 3$", with $\phi(n,k)$ counting petals directly — so it evaluates
the 2-uniform sunflower number at every petal count, which is precisely
`chvatal_hanson::f_2_k`.

The consequence for this repository: **the exact values $f(2,k)$ are due
to [AHS72] in 1972, not to [CH76] in 1976.** What [CH76] adds
is the full two-parameter function $CH(D,\nu)$ for $D \ne \nu$; the
sunflower problem only ever needs the diagonal. `docs/roadmap.md` §3a
names "the $CH$ upper bound" as the main remaining target at uniformity
2, and if the diagonal is what is wanted then [AHS72]'s argument may be
the shorter one to formalise. Both papers remain unread; this is an
inference from a survey's quoted formula matching a computed table, and
is recorded as that.

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

## The ground-set framing, which is known

- **[FPPTZ24]** P. Frankl, J. Pach, D. Pálvölgyi, and others, *Odd-sunflowers*.
  Journal of Combinatorial Theory Series A 205 (2024); arXiv:2310.16701.
  Read from the rendered pages. Three things in it bear directly on
  `docs/roadmap.md` §7, and the first two were **not** known to this
  repository.

  1. **The ground-set framing is known and is an equivalence.** Its
     Conjecture 14 — "the maximum number of base elements, each of which
     is contained in at least one set of a sunflower-free $k$-uniform
     family, is at most $c^k$" — is reported, crediting **Zach Hunter**
     (MathOverflow), to be *equivalent* to the Erdős–Rado conjecture. So
     `SliceRank.GroundBounded` is not a new angle; it is a *linear*
     strengthening of a known equivalent formulation.

  2. **The ground set can be exponentially large:** $g_v(k) \ge 2^k - 1$,
     via the root-to-leaf paths of a depth-$k$ binary tree taken as edge
     sets. So the *universal* reading of `GroundBounded` — "every
     sunflower-free $m$-uniform family lives on $O(m)$ points" — is false
     for every $c$, and only the existence reading the definition actually
     has survives. `IotaGround.the_universal_ground_reading_is_false` is
     the $k=3$ instance and `rust/tests/ground_set.rs` checks the
     construction to $k = 6$. This does not conflict with the $N(m,g)$
     measurements, which are about the largest family *on* $g$ points —
     exactly the quantity the existence reading needs.

  3. **"We could not find any papers studying the quantity $g_v(k)$"** —
     their words. A 2024 paper with Frankl as a coauthor says the
     ground-set quantity is unstudied, which is mild support for the
     framing being unusual even though the equivalence is known.

  Also in that paper, and worth not mis-citing: its Proposition 12 ("direct
  sum constructions never reach the optimal value") is about the
  **Erdős–Szemerédi** problem — non-uniform families on a bounded ground
  set — not the uniform problem this repository works on. So is
  [DEGKM97] (Deuber, Erdős, Gunderson, Kostochka, Meyer, *Intersection
  statements for systems of sets*, JCTA 79 (1997) 118–132), whose
  $F(n,3) \ge 1.551^{n-2}$ is a bound for that other problem and does
  **not** displace [AHS72] as the uniform record.

### What this corrects in §7

Chasing Hunter's equivalence exposed a gap in this development's own
reasoning. `SliceRank.bounded_ground_set_settles_k3` derives the
conjecture from `GroundBounded c` **plus** `NaslundSawinBound`. The
polynomial method is not needed: a family of distinct subsets of a
$g$-point set has at most $2^g$ members by counting, so a ground set of
size $c \cdot m$ gives $(2^c)^m$ directly.
`IotaGround.ground_bounded_settles_k3_by_counting` and
`iota_ground_bounded_settles_k3_without_the_axiom` are the axiom-free
versions, and $(2^c)^m$ beats the $(27^{c+1})^m$ the Naslund–Sawin route
gives, for every $c$. What [NaSa17] contributes is the constant
($1.89^g$ against $2^g$) — a real theorem, and not the load-bearing part.

## What the literature does not contain

Three sources were searched for the two structural claims this
repository makes — the sandwich $2\iota(b) \le g(b) \le 2b\,\iota(b)$ and
the equivalence "the conjecture at $k=3$ iff $\iota(b) \le C^b$" — and
for any use of shifting against sunflower-freeness. All three are
negative, and negatives from sources of this weight are worth recording
even though they are not proof of novelty.

- **[Kup25]**, the survey of the Δ-system method: no extremal function
  for intersecting sunflower-free families, no reduction of the sunflower
  problem to the intersecting case, and **no discussion of shifting at
  all** — in the survey of the method the problem belongs to.
- **Lovett, *From sunflowers to thresholds*** (PCMI lecture series, IAS).
  The word "intersecting" does **not occur in the notes** (1358 lines of
  extracted text, zero matches). The only occurrence of "compress" is the
  ALWZ sense of compressing a *set*, not Frankl's shift.
- **[Mis26]** does apply shifting, and does not observe that it fails to
  preserve sunflower-freeness.

What *is* textbook is the first step of the star bound: a maximal
disjoint subfamily, maximality, pigeonhole to a heavy point. That is
Erdős–Rado's own argument. What this repository adds is reading the
resulting star as an *intersecting sunflower-free family* and closing the
loop with the doubling, which is what turns a step of a proof into an
equivalence. Treat "new" as unverified; treat "not in the standard
sources" as checked.

## Shifting, and the shifted case

- **[Mis26]** Tapas Kumar Mishra, *Erdős Rado Sunflower Theorem for
  Shifted Families*. arXiv:2606.02667, v1 1 June 2026, v2 8 June 2026,
  math.CO. Proves the Erdős–Rado conjecture **for shifted families**:
  writing $f'(k,s)$ for the least $m$ such that every *shifted* family of
  more than $m$ $k$-sets contains an $s$-sunflower, Theorem 1 gives
  $f'(k,s) \le s^{2k}$ for $k \le s-1$ and $f'(k,s) \le 2f'(k-1,s)$
  otherwise, hence Corollary 1: $f'(k,s) \le s^{2s-2}2^k$. Uniform
  families; "shifted" is the standard fixed-point-of-all-$(i,j)$-shifts
  condition, the same as `Compression.LeftCompressed`. **The paper gives
  no lower bound and no extremal family**, and does not discuss whether
  shifting preserves sunflower-freeness.

  `coq/Compression.v` determines the same quantity exactly:
  $f'(k,s) = \binom{k+s-2}{k}$, attained by all $k$-subsets of a
  $(k+s-2)$-set. ([Mis26] defines $f'$ by "cardinality **more than** $m$",
  so $f'$ *is* the extremal number and there is no $+1$; the definition
  was read off the rendered page rather than an extracted-text summary,
  which had it as "at least".) That is **polynomial in $k$ of degree $s-2$**, against
  the exponential $s^{2s-2}2^k$, and it is sharp rather than an estimate.
  `compressed_lives_on_m_plus_k_minus_two_points` is the machine-checked
  half (a shifted $s$-sunflower-free $k$-uniform family lives on $k+s-2$
  points); the count and the attainment are exhaustively verified in
  `rust/tests/shifting.rs` over 62 parameter points and proved in prose
  there. See `docs/roadmap.md` §8.

  This is also the answer to "has anyone pointed shifting at this
  problem?": yes, two months before this was written, and the question is
  live. [Kup25], the survey of the Δ-system method, contains no
  discussion of shifting at all.

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

The same holds for [ChHa76]: a formalisation of its upper bound would
turn `CliqueLowerBound.two_cliques_lower_bound` from a lower bound into
an exact value for every odd $k$, and would settle the sharp spread
threshold at uniformity 2. That is the campaign described in
`docs/roadmap.md` §3a — and, per [BaKh09], its prerequisite is Gallai's
lemma on factor-critical graphs, which no part of this development's
bipartite Hall/Kőnig layer supplies.

If a Coq or Lean formalisation of the 2020 spread lemma becomes
available, the axiom `Rao20_lemma2` in `coq/ALWZ.v` can be
replaced by an import — and nothing downstream of it needs to change,
since the passage from the spread lemma to the sunflower bound is
already proved in `coq/SpreadReduction.v`. The interface to meet is
`SpreadReduction.SpreadYieldsDisjoint n k r` for
$r = \Theta(k \log (nk))$; [Ra20] is the elementary route to it.
