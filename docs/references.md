# Annotated bibliography

Original sources, refinements, and surveys on the Sunflower
Conjecture. Cross-referenced from `coq/Spread.v`, `coq/ALWZ.v`,
`coq/Conjecture.v`, `coq/TwoUniform.v`, `coq/CliqueLowerBound.v`, and
`docs/proof_strategies.md`.

**Evidence class is stated for every entry**, following the July 2026
reading session (`docs/reading.md`):

```
  read in full        every page rendered and read
  read pp. N-M        that range only
  abstract only       the abstract page, nothing else
  unreachable         attempted, blocked; attempts recorded in docs/reading.md
  not attempted       named but not chased
  inferred            from a citing paper or survey; never treated as read
```

Withdrawals are written as withdrawals, in the text, not edited away.

Two results here are *used* rather than merely cited: [Ra20] Lemma 2,
which is the development's one axiom, and [ChHa76], which is not
formalised at all and which no theorem in the development depends on —
it is the source of the numbers `rust/src/chvatal_hanson.rs` computes
and of the claim that those numbers are the truth rather than an upper
estimate. Both are marked below.

## Original problem

- **[ErRa60]** P. Erdős and R. Rado, *Intersection theorems for systems
  of sets*. Journal of the London Mathematical Society 35 (1960),
  85–90. **Read in full (6 pages), July 2026**, from the Erdős archive
  at `users.renyi.hu/~p_erdos/1960-04.pdf` — open access.

  **Withdrawn:** this entry previously said the paper *"proves
  $f(n,k) \le (k-1)^n n! + 1$"*. That is the modern rounding, not the
  paper. Three corrections, all from rendered pages:

  * the paper's objects are *systems*, i.e. **multisets** — p. 85,
    *"a $(a,b)$-system if it consists of $a$ (not necessarily distinct)
    sets of cardinal $b$"*. Remark 3 on p. 86 gives the $a=b=2$ witness
    `01, 01, 23, 23, 04, 04, 14, 14, 25, 25, 35, 35`, every pair
    doubled, and hence $c = 12$ rather than 6;
  * **Theorem III**'s constant (p. 86) is
    $c = b!\,a^{b+1}\left(1 - \frac{1}{2!a} - \frac{2}{3!a^2} - \cdots -
    \frac{b-1}{b!\,a^{b-1}}\right)$;
  * for *distinct* families the paper derives, on p. 90,
    $\phi(a,b) \le b!\,a^{b}\left(1 - \frac{1}{2!a} - \cdots\right)$ —
    **strictly sharper** than $b!a^b$. `coq/ErdosRado.v` proves the
    rounded $(k-1)^n n! + 1$, which is correct and weaker than the 1960
    paper's own bound.

  The conjecture in the authors' words, p. 86: *"It is not improbable
  that in (1) the factor $b!$ can be replaced by $c_1^{\,b}$, for some
  absolute positive constant $c_1$. Such a sharpened version of III
  would have some applications in the theory of numbers, and in fact
  these applications originally gave rise to the present
  investigations."*

  **Theorem II** (p. 86, constructed p. 89) is the lower bound: all maps
  $B \to A$, giving an $(a^{b+1}, b)$-system with no $\Delta(>a)$-system.
  This transversal family is the tightness example every 2020–2021 paper
  reuses.

  And the modern textbook proof **is** Erdős and Rado's own, on p. 90:
  *"Let $N_0$ be a maximal subset of $N$ such that $X_\mu X_\nu = \emptyset$
  ... Then $|N_0| \le a$, since $X_\nu\ (\nu \in N_0)$ is a
  $\Delta$-system"*, followed by pigeonhole on $\bigcup N_0$. Both branches
  of `StarDefect.the_two_branches_of_the_dichotomy` are on that page.
  (Theorem I's proof, pp. 87–89, is a transfinite *Ramification Lemma*,
  which is not what anyone formalises.)

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
  sets*. Forum of Mathematics Sigma 5 (2017), e15; arXiv:1606.09575.
  **Read p. 1 of 5 (rendered).** The slice-rank method — the machinery
  that settled cap set — applied to the sunflower problem.

  **Corrected.** This entry previously stated the bound as
  *"$3(n+1)C^n$ members with $C = 3/2^{2/3}$"*. The abstract, on the
  rendered page, says

  $$|\mathcal F| \;\le\; 3n \sum_{k \le n/3}\binom{n}{k}
    \;\le\; \left(\tfrac{3}{2^{2/3}}\right)^{n(1+o(1))}.$$

  The polynomial factor is $3n$, not $3(n+1)$, and the exponential
  factor is a **binomial sum** bounded by $C^{n(1+o(1))}$ — not $C^n$ on
  the nose. The base $C = 3/2^{2/3} < 1.89$ is right. It is a
  $constant^n$ bound of the conjectured shape, but in the **ground set**
  rather than the uniformity.

  `coq/SliceRank.v` carries it as a hypothesis (not an axiom) and proves
  that one further fact — that extremal uniform families live on $O(m)$
  points — would turn it into the conjecture at $k = 3$. Nothing there
  depends on the polynomial factor, so the misquote was cosmetic; it is
  fixed anyway.

  **The "later paper improving the polynomial factor" is now identified
  and read (p. 1 of 12):** O. Ahmadi and H. Norouzi, *A Polynomial
  Improvement of Naslund–Sawin Bound for Sunflower-Free Families Using
  Triangular Tensors*, arXiv:2606.30593 (30 June 2026), which proves
  $|\mathcal F| = O\!\left(n^{1/6}(3/2^{2/3})^n\right)$ against
  Naslund–Sawin's $O\!\left(n^{1/2}(3/2^{2/3})^n\right)$. **The base is
  unchanged**, so `NaslundSawinBound` is unaffected in substance.

- **[AHS72]** H. L. Abbott, D. Hanson, N. Sauer, *Intersection theorems
  for systems of sets*. Journal of Combinatorial Theory Series A 12
  (1972), 381–389. The best classical lower bound at $k = 3$:
  $f(n,3) \gtrsim 10^{n/2 - c\log n}$, i.e. a rate of
  $10^{1/2} = 3.162\ldots$ per point. The mechanism is a *substitution*
  recursion $g(ab) \ge g(a)\,g(b)^a$, strictly stronger than the direct
  sum $g(a+b) \ge g(a)g(b)$ that `coq/DirectSum.v` proves and that only
  reaches $6^{1/2} = 2.449\ldots$. See `docs/roadmap.md` §5 for what
  formalising it would need.

  **UNREACHABLE — Elsevier paywall.** Four routes were tried in July 2026
  and all failed: ScienceDirect PDF (HTTP 403), the DOI
  `10.1016/0097-3165(72)90103-4` (HTTP 404), CORE search (HTTP 403), and
  the Erdős archive (Erdős is not an author; the index has no entry —
  confirmed by grepping it for "Intersection theorem", which returns only
  ErRa60, EKR61, ErRa69-II and EMR74-III). Per `docs/roadmap.md` §15.2's
  own instruction, **nothing further is built on it.**

  What is recorded here is from secondary
  sources; the rate and the recursion were checked against each other
  (the recursion's fixed point at $a = b = 3$ is $g(3)^{3/2}$, which is
  $10^{1/2}$ exactly when $g(3) = 10$), and they agree. The reported
  base case does not corroborate: $g(3,3) \ge 12$ already follows from
  the direct sum here. Read the paper before relying on any constant
  from it.

  **Corroborated against [Kup25], now from rendered pages** (previously
  only its arXiv HTML had been read; the quotations below survive
  rendering unchanged). The survey states the bound
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

  **New, from [Kup25] p. 5 rendered:** *"Abbot, Hanson and Sauer [1] in
  1972, and then Spencer [116] in 1977 improved upper bounds on
  $\phi(k,s)$. The result of Spencer states that for any fixed $s$ and
  $\epsilon > 0$ there exists $C$ such that
  $\phi(k,s) \le Ck!(1+\epsilon)^k$."* So [AHS72] also improved the
  **upper** bound, which this repository did not know, and **Spencer
  1977** is a reference this bibliography lacks entirely. Neither has
  been read.

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

  **Read pp. 5–6 of 66 rendered pages, July 2026** (previously only the
  arXiv HTML). Definition (1.1) on p. 5 confirms the re-indexing note
  verbatim, and the two [AHS72] sentences on p. 6 survive rendering
  unchanged. Also on p. 6, **Observation 2**: *"We have
  $\phi(a+b,s) \ge \phi(a,s)\phi(b,s)$"*, with proof — that is
  `coq/DirectSum.v`'s supermultiplicativity, and it is published. No
  novelty was claimed for it; now it has a citation. The other 60 pages
  were not read.

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
  $o(n!)$, won the consolation $100 prize. **Not read.** Two surveys
  render the bound differently and neither was checked against the
  paper: [Kup25] p. 5 gives
  $\phi(k,s) \le C(s,\alpha)k!\left((\log\log k)^2/(\alpha\log\log k)\right)^k$,
  [Rao25] p. 2 gives $O(k!\,(\log\log\log k/\log\log k)^k)$. **Inferred,
  and inconsistently.** Do not quote either without the paper.

- **[KRT99]** A. V. Kostochka, V. Rödl, L. A. Talysheva, *On systems
  of small sets with no large $\Delta$-subsystem*. Combinatorics,
  Probability and Computing 8 (1999), 81–88. **Not read.** [Kup25] p. 5
  states it as: *"For fixed $k$ and large $s$ Kostochka, Rödl and
  Talysheva [93] showed that $\phi(k,s) = (1+o(1))k^s$"* — in this
  repository's notation, the many-petals asymptotic. **Inferred.**

## 2020 breakthrough and refinements

- **[ALWZ20]** R. Alweiss, S. Lovett, K. Wu, J. Zhang, *Improved
  bounds for the sunflower lemma*. STOC 2020; Annals of Mathematics
  194(3):795–815, 2021. arXiv:1908.08483v3. **Read in full (19 pages),
  July 2026.**

  **Corrected.** This entry previously said ALWZ *"establishes
  $f(n,k) \le (Ck\log n)^n$"*. **That is [BCW21]'s bound.** ALWZ's own
  Theorem 1.4, rendered page 1, is

  > For some constant $C$, any $w$-set system $\mathcal F$ of size
  > $|\mathcal F| \ge (Cr^3 \log w \log\log w)^w$ contains an
  > $r$-sunflower.

  Their §4, page 12, records the chain themselves: *"Rao then used their
  refinements to further improve ... the bound in Theorem 1.4 to
  $(Cr\log(wr))^w$. Bell, Chueluecha, and Warnke [4] observed that a
  small modification of the argument improves the bound in Theorem 1.4
  further to $(Cr\log(w))^w$."*

  **Definition 1.1, rendered page 1**: *"a $w$-set system if each set in
  $\mathcal F$ has size **at most** $w$"*. The "at most" convention is
  ALWZ's; `coq/ALWZ.v` had attributed it to [Ra20], which says "of size
  $k$". That mis-citation is withdrawn there.

  **§3, Lemma 3.1, rendered pages 11–12**, is the tightness example, and
  reading it settles `docs/roadmap.md` §5's open question in the
  direction that keeps it open: the family is a thinned subfamily of
  $X_1 \times \cdots \times X_w$, and Claims 3.2/3.3 show it contains no
  *robust* sunflower. A transversal family with parts of size $\ge p$
  **does** contain $p$ pairwise disjoint members, so the example says
  nothing about the disjointness form. See `docs/reading.md` row A2.

  **§4.2 *Intersecting set systems*, rendered page 13, Theorem 4.2:**

  > If $\mathcal F$ is an intersecting $w$-uniform set system, and for all
  > $T$, $|\mathcal F_T| \le \kappa^{-|T|}|\mathcal F|$, then
  > $\kappa = O(\log w)$.

  with, on the same page, *"An example from [16] shows that for
  $\kappa = \Omega(\log w/\log\log w)$, there are intersecting
  $\kappa$-spread $w$-uniform set systems, so the bound in Theorem 4.2
  is close to tight."* **This refutes `coq/IotaRate.v`'s claim that the
  extremal-set-theory toolbox "has never been pointed" at the
  intersecting side.** It does not touch the sandwich or the
  equivalence — ALWZ's hypothesis is *spread*, the repository's is
  *sunflower-free*, and neither implies the other — but the claim as
  written was false and is withdrawn there.
  `IotaRate.intersecting_not_spread_above_uniformity` is the elementary
  version of Theorem 4.2, machine-checked.

  **Definition 1.10, read from the rendered page 4**: *"We say that a
  $w$-set system $\mathcal F$ is $\kappa$-spread if
  $|\mathcal F| \ge \kappa^w$ and
  $|\mathcal F_T| \le \kappa^{-|T|}|\mathcal F|$ for all non-empty
  $T$"*, followed by *"The paper [16] calls these 'regular set systems',
  but we use the more descriptive term 'spread'."* So the notion predates
  the paper. The same page states the dichotomy in the form this
  repository re-derived: *"either $\mathcal F$ is $\kappa$-spread, or
  there is a link $\mathcal F_T$ of size
  $|\mathcal F_T| \ge \kappa^{w-|T|}$. In the latter 'structured' case,
  we can simply pass to the link and apply induction, much like in the
  original proof of Erdős and Rado."* See `docs/roadmap.md` §14.5.

- **[Ra20]** A. Rao, *Coding for sunflowers*. Discrete Analysis 2020:2.
  arXiv:1909.04774. **Read in full (8 pages), July 2026.** The source of
  this development's only axiom, and the reason `docs/reading.md`
  exists. Lemma 2 and the spread definition are quoted verbatim there
  and checked symbol-by-symbol against `ALWZ.Rao20_lemma2`.

  Two things in it that change what this repository does:

  1. **p. 2, and it closes an open item:** *"As far as we know, it is
     possible that Lemma 2 holds even when $r(p,k) = O(p)$. Such a
     strengthening of Lemma 2 would imply the sunflower conjecture of
     Erdős and Rado."* `docs/roadmap.md` §5 recorded "whether the log is
     necessary in the disjointness form was looked for and not found".
     It is found: **the question is open, and the source says so.**
  2. **The proof is not elementary.** Its Lemma 5 (p. 4) is Shannon's
     noiseless coding theorem, applied through Kraft's inequality and
     the concavity of $\log$, over a random partition of the ground set.
     `coq/ALWZ.v` said *"elementary — injections between finite sets and
     binomial estimates, no measure theory"*. **Withdrawn** there. Of
     the four published proofs it is the worst fit for a `nat`-only
     development, not the best.

- **[Rao25]** A. Rao, *The Story of Sunflowers*. arXiv:2509.14790
  (18 Sep 2025). **Read pp. 1–3 of 12.** A 2025 survey by the author of
  [Ra20], and a third independent confirmation of the item above, p. 3:
  *"The only difference between this bound and the conjecture of Erdős
  and Rado is the presence of the $\log k$ term. **This dependence is
  necessary for robust sunflowers**, as shown by [3] ... **Nevertheless,
  it is quite possible that the sunflower conjecture of Erdős and Rado
  holds in its original form.**"* Its §3 gives *"a short elementary
  proof of the best known bounds for the robust sunflower lemma"* and
  was **not read**; it may be a better formalisation target than
  Lovett §3.

- **[Rao23]** A. Rao, *Sunflowers: from soil to oil*. Bulletin of the
  AMS 60(1):29–38, 2023. **Not attempted.** Discovered via [Mis26]'s
  reference list; recorded so it is not re-discovered.

- **[FKNP19]** K. Frankston, J. Kahn, B. Narayanan, J. Park,
  *Thresholds versus fractional expectation-thresholds*. Annals of
  Mathematics 2021. arXiv 1910.13433. Resolves Talagrand's
  expectation-threshold conjecture, which implies a sunflower bound.

- **[BCW21]** T. Bell, S. Chueluecha, L. Warnke, *Note on sunflowers*.
  Discrete Mathematics 344(7):112367, 2021; arXiv:2009.09327. **Read in
  full (3 pages), July 2026.** **This is the current peer-reviewed
  record.** Theorem 1, p. 1: *"There is a constant $C \ge 4$ such that
  $\mathrm{Sun}(p,k) \le (Cp\log k)^k$ for all integers $p, k \ge 2$."*
  Its Lemma 2, p. 1, is the disjointness form at threshold
  $r(p,k) = Cp\log k$ — the log is of the **set size alone**, which is
  exactly the improvement `coq/ALWZ.v`'s "what an improved spread lemma
  would buy" note describes. Lemma 4, p. 3, is the tightness example for
  the $r$-spread assumption; like ALWZ's it is the transversal family
  and does **not** touch the disjointness form.

- **[Fuk25]** J. Fukuyama, *Sunflower Bound with a Sub-Logarithmic
  Base*. arXiv:2510.19037v2 (1 Dec 2025). **Read in full (8 pages).**
  Theorem 1.1 claims a family of $m$-sets with
  $|\mathcal F| \ge (ck^2\ln m/\ln\ln m)^m$ contains a $k$-sunflower —
  which would beat [BCW21]. **Unrefereed preprint; no journal
  publication is recorded, and the author's own project page describes
  the proof as not yet stable.** The same author's arXiv:1809.10318
  (cited by [ALWZ20] as [11]) made a comparable claim in 2018 and is
  likewise unpublished. **Recorded, not adopted**: `docs/roadmap.md` §12's
  threshold table continues to use [BCW21].

- **[MNSZ22]** E. Mossel, J. Niles-Weed, N. Sun, I. Zadik, *A second
  moment proof of the spread lemma*. arXiv:2209.11347, 8 pages. **Read
  in full, July 2026.** Two things the earlier page-1-only read missed:
  the proof runs on Radon–Nikodym derivatives, couplings and Hölder's
  inequality (pp. 2–5), making it the *second* worst fit for a
  `nat`-only development; and **footnote 2 on p. 6** says *"It was
  recently pointed out that the proof of [Tao20] has a gap, which has
  been corrected in [Hu21, Sto22]."* — so one of the four proofs has a
  published gap. Also: the streamlining below is by **M.** Stoeckl
  (`mstoeckl.com/notes/research/sunflower_notes.html`, 2022), not S.

  The earlier note, which stands: Recorded here
  because its abstract enumerates what this repository needed to know
  before scoping `docs/roadmap.md` §1: the spread lemma has **four**
  independent proofs — *"delicate counting arguments"* ([ALWZ20],
  refined by [FKNP21]), *"Shannon's noiseless coding theorem"*
  ([Ra20]), *"manipulations of Shannon entropy bounds"* (Tao 2020), and
  their own *"truncated second moment calculation"* via the planting
  trick. §1 plans its campaign against [Ra20], whose prerequisite is the
  worst fit of the four for a `nat`-only development; see
  `docs/roadmap.md` §15.1.

- **[Lovett]** S. Lovett, *From sunflowers to thresholds*. PCMI lecture
  series, IAS, July 2025;
  `www.ias.edu/sites/default/files/Shachar%20Lovett%20Lecture%20Notes%201.pdf`.
  **Read in full (28 pages), July 2026.** (`docs/roadmap.md` §15.1 said
  29pp; the version reachable in July 2026 is 28.) Everything below was
  re-checked on the rendered page it is attributed to, and all three
  quotations survive verbatim.

  Two further things, both found only by reading past page 7:

  * **Lemma 2.6, p. 8**, is `SpreadReduction.spread_reduction`, *with*
    the relativisation: *"Assume that for all `n' ≤ n`, every family of
    `n'`-sets which is `k`-spread contains an `r`-sunflower. Then
    `SF(n,r) < k^n`."* So the axiom's "relativised to all `m ≤ n`" is
    textbook, not an extension of the literature.
  * **Lemma 2.9, p. 8**, is the *fractional* disjointness statement:
    *"Let `F` be a family of `n`-sets which is `k`-spread for
    `k = cr log n` ... Then `F` contains `r` pairwise disjoint sets."*
    No size hypothesis, because `k`-spread already forces `|F| ≥ k^n`.
    This is the form the axiom should have been stated against;
    `ALWZ.fractional_form_gives_the_axiom_shape` bridges the two and
    thereby discharges the axiom's quantification over `r`.
  * **§3, pp. 11–15**, is the counting proof of the spread lemma
    (Park–Pham's minimal-fragment streamlining), and it is the
    formalisation target this repository should pick. Claim 3.4's
    "probability" is literally `|B| / (|F|·C(N,qN))`, a ratio of two
    explicit cardinalities. See `docs/reading.md` row C17.

  Two things in it bear directly on `coq/StarDefect.v`, and both
  correct a claim this repository made.

  1. **Definition 2.5 (Spread family)**: *"Let `F` be a family of sets,
     and let `k > 1`. We say that `F` is `k`-spread if for every set
     `T`, `|F_T| <= |F|/k^{|T|}`."* At `|T| = 1` that is
     `maxdeg(F) <= |F|/k`, i.e. exactly the ratio `rho(F) = |F|/maxdeg(F)`
     being at least `k`. So `rho` is the singleton clause of spreadness,
     which is `Spread.Spread` in this development and has been since the
     spread layer went in. `docs/roadmap.md` §14.5 withdraws the claim
     that it was an unnamed quantity;
     `StarDefect.star_defect_is_the_singleton_spread_clause` is the
     identification as a theorem.

  2. **Lemma 2.2 (Sunflower lemma, again)** proves Erdős–Rado by the
     dichotomy this repository re-derived: with `k = (r-1)n`, either some
     element lies in a `1/k`-fraction of the sets — recurse into its link
     — or every element lies in strictly fewer, and then a maximal
     pairwise-disjoint subfamily must have `r` members. At `r = 3` the
     constant `(r-1)n` is exactly the `2b` of
     `StarDefect.star_defect_bound` and one below the `2b+1` of
     `SpreadReduction.elementary_spread_disjoint`, which is the other
     branch and was already here.

  And the sentence that says why the singleton parameter cannot be a
  constant, immediately before Definition 2.5: *"Note that in the proof
  we only used the 'structured' case where a single element belongs to
  many sets in `F`. But we also could have used two elements, or three
  elements, or any number of elements. This motivates the following
  definitions."* Generalising from one element to sets is the whole 2020
  programme. The earlier note recorded here — that the word
  "intersecting" does not occur in these notes — stands and is
  unaffected.

- **[Hu21]** L. Hu, exposition streamlining the proof; cited by
  [MNSZ22] as one of the two corrections to the gap in [Tao20]. **Not
  attempted.** *Name discrepancy, unresolved:* [MNSZ22] cites this as
  **[Hu21]**, [Kup25] p. 7 writes **"Lu [75]"** for what is evidently the
  same correction. Do not cite either spelling as settled.

- **[Tao20]** T. Tao, *The sunflower lemma via Shannon entropy*,
  `terrytao.wordpress.com/2020/07/20/the-sunflower-lemma-via-shannon-entropy/`,
  20 July 2020. **Not read.** Recorded here because **two independent
  sources say it has a gap**: [MNSZ22] fn. 2, p. 6, *"It was recently
  pointed out that the proof of [Tao20] has a gap, which has been
  corrected in [Hu21, Sto22]"*; and [Kup25] p. 7, *"Tao [118] gave a
  proof based on entropy, which, however, contained a mistake."* Use
  [Hu21] or [Sto22] instead. `docs/roadmap.md` §15.1 listed this as one
  of four candidate routes without knowing.

- **[Sto22]** M. Stoeckl, *Lecture notes on recent improvements for the
  sunflower lemma*, `mstoeckl.com/notes/research/sunflower_notes.html`,
  2022. **Not attempted.** [Kup25] p. 7 states the bound it reaches:
  *"Lu [75] and then Stoeckl [117] gave another entropy proof, which gave
  the bound $\phi(s,k) \le (64s\log k)^k$."* That is where this file's
  "$C = 64$" comes from, now with a source. (Earlier revisions gave the
  initial as "S.")

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

- **[ES78]** P. Erdős and E. Szemerédi, *Combinatorial properties of
  systems of sets*. Journal of Combinatorial Theory Series A
  24(3):308–313, 1978. **Not attempted.** Added because it is the
  primary source of the *other* problem — bounded ground set — that
  [DEGKM97] and [FPPTZ24, Prop. 12] belong to, and because this
  bibliography had been warning against mis-citing it without ever
  naming it. Lovett's notes p. 5 give the statement: $ES(N,r)$ counts
  $r$-sunflower-free families of *arbitrary-size* subsets of $[N]$, and
  the conjecture is $ES(N,r) \le (2-\epsilon_r)^N$.

- **[Hun24]** Zach Hunter, MathOverflow answer 463150, 30 January 2024,
  accepted, to Dömötör Pálvölgyi's question 462924 *"How many base
  elements can a sunflower-free system have?"*. The source of the
  ground-set equivalence credited in [FPPTZ24]. **READ IN FULL.**
  `WebFetch` is blocked for mathoverflow.net in this environment; the
  **StackExchange API is not** —
  `api.stackexchange.com/2.3/answers/463150?site=mathoverflow&filter=withbody`
  returns the body verbatim. Quoted in full in `docs/reading.md`.

  The equivalence, in his words: *"one can start with a maximal
  `t`-sunflower-free collection in uniformity `k-1`, and then add a
  unique 'dummy element' to each edge in this construction. Thus, your
  problem has a bound of `exp(O_t(k))` if and only if the original
  Erdos-Rado problem has a bound of `exp(O_t(k))`."*

  Two things in it that were not known here:

  * his closing **"EDIT: my question is also silly. If no element is
    contained by a `(1/tk)`-fraction of the edges from `H`, then we can
    greedily find `t` disjoint sets"** is
    `StarDefect.star_defect_bound` — a second, independent, informal
    statement of the branch §14.5 already withdrew the novelty claim for,
    at the slightly weaker constant `3b` against this repository's `2b`;
  * the question he proposes and withdraws — *"Is there some vertex that
    is contained in at least `c_t^k|H|` of the edges?"* — is the
    **exponentially weak** form of `StarDefect.StarBounded`, and it is
    trivially true. `StarBounded c` asks for a *constant* factor, which
    settles the conjecture and which this repository shows is false. The
    two must not be conflated.

## The extremal objects, identified

Not references so much as a place to record what the extremal families
*are*, since the identification is what would let the literature be
searched properly. Both come from `rust/examples/iota_structure.rs`, whose
automorphism-group search is cross-checked against `nauty`.

- **$\iota(3) = 10$ is the unique simple 2-(6,3,2) design.** Ten triples
  on six points, 5-regular, every pair in exactly two blocks,
  $|\mathrm{Aut}| = 60$ and point-transitive. (60 is the order of
  $A_5 \cong \mathrm{PSL}(2,5)$ acting on the six points of the projective
  line over $\mathbb F_5$, which is what one would expect; the *order* is
  what was computed, not the isomorphism type.) A 2-(6,3,2) design is the smallest nontrivial *biplane*
  complement / twofold triple system, and the simple one is unique up to
  isomorphism; that uniqueness is standard design theory and is **taken
  on the literature's word here**, not verified. What is verified is the
  parameters, the regularity and the group order.

- **$\iota(4,9) = 27$ is the Abbott–Hanson–Sauer substitution of the
  triangle into itself.** Split the nine points into three triples; take
  every union of a pair from one triple with a pair from a different one.
  $3 \cdot 3 \cdot 3 = \iota(2)\,\iota(2)^2$. Its automorphism group has
  order $1296 = 6\cdot 6^3$, which is $\mathrm{Sym}(3)$ on the triples
  times $\mathrm{Sym}(3)$ inside each — exactly the symmetry the
  substitution predicts, and the reason to believe the identification
  rather than merely the count. So at $b = 4$ the 1972 construction is
  *optimal on nine points*, not one construction among many.

**Searched under the design names in July 2026; not resolved.** The
parameter arithmetic checks out — for a 2-$(6,3,2)$ design,
$r = \lambda(v-1)/(k-1) = 5$ and $b = vr/k = 10$, matching the computed
10 blocks and 5-regularity — and $|\mathrm{Aut}| = 60$ is exactly
$|\mathrm{PSL}(2,5)| = |A_5|$ acting on the six points of
$\mathrm{PG}(1,5)$, whose two orbits on triples are the two
complementary 2-$(6,3,2)$ designs, swapped by $\mathrm{PGL}(2,5)$. That
is a mechanism, and it agrees with the computation. **But the
*uniqueness* claim was not read from any primary source**: the Handbook
of Combinatorial Designs is not open access and no free rendered page was
obtained. It stays cited-not-verified, and this paragraph is the search
that failed rather than a claim that it succeeded. The note below about
the design name also stands: a 2-$(6,3,2)$ design is *not* symmetric
($b = 10 \ne 6 = v$), so calling it a biplane complement is loose; it is
a twofold triple system $TS(6,2)$. The `iota` sequence
$1, 3, 10, 27$ is **not** in OEIS in any relevant form — ten hits, all
coincidental (non-sum-free subsets, $\lfloor\sinh n\rfloor$, …) — and
$1,3,10,27,54$, $3,10,24$ and the ground-set rows return nothing at all.
Searched with the OEIS JSON API over six queries; not exhaustive over
reformulations.

## The cone, and whether it is known

`Product.iota_at_least_g_pred` — adding a fresh point to every member of a
sunflower-free $m$-uniform family gives an intersecting $(m+1)$-uniform
one of the same size, so $g(m) \le \iota(m+1)$ — is elementary enough that
it is almost certainly folklore. **No novelty is claimed for it.**

**Updated July 2026: the *technique* is published, in this exact
context.** [Hun24], reading it properly for the first time: *"one can
start with a maximal $t$-sunflower-free collection in uniformity $k-1$,
and then add a unique 'dummy element' to each edge in this
construction."* His dummies are **distinct per edge**, which grows the
ground set and gives the ground-set equivalence; the repository adds
**one shared** fresh point to every member, which makes the family
intersecting and gives the cone. Different constructions with the same
first move, reaching different conclusions. The exact statement
$g(m) \le \iota(m+1)$ is still not found anywhere, but "nobody has used
this move" was never the claim and is now definitely false. A two-line
observation is exactly what a literature search is worst at finding, and
the search was not exhaustive.

What the repository does claim is what follows from it, which is not
folklore because $\iota$ is not a named quantity elsewhere (see [Kup25]
above): the second sandwich $g(b-1) \le \iota(b) \le b\,g(b-1)$, the
transfer of an $\iota$ upper bound into an $f(3,3)$ bound, the collapse of
the two ground-set hypotheses into one, and the refutation of the
universal reading of `IotaGroundBounded`. See `docs/roadmap.md` §11.

## What the literature does not contain

Three sources were searched for the two structural claims this
repository makes — the sandwich $2\iota(b) \le g(b) \le 2b\,\iota(b)$ and
the equivalence "the conjecture at $k=3$ iff $\iota(b) \le C^b$" — and
for any use of shifting against sunflower-freeness. All three are
negative, and negatives from sources of this weight are worth recording
even though they are not proof of novelty.

**One adjacent negative is now positive, and is withdrawn.** The claim
that the intersecting side of this problem is untouched is false:
[ALWZ20] §4.2 is titled *Intersecting set systems* and Theorem 4.2
(rendered p. 13) bounds the spread parameter of an intersecting
$w$-uniform system by $O(\log w)$, with a near-matching example. The
sandwich and the equivalence are about intersecting **sunflower-free**
families and are untouched by it, but "nobody has looked at intersecting
families here" was never true. See `coq/IotaRate.v`, whose header now
says so, and `IotaRate.intersecting_not_spread_above_uniformity`.

The corpus actually read for these searches, July 2026:
[Ra20] (8pp, full), [ALWZ20] (19pp, full), [BCW21] (3pp, full),
[Lovett] (28pp, full), [MNSZ22] (8pp, full), [ErRa60] (6pp, full),
[Mis26] (12pp, full), [Kup25] (pp. 5–6 of 66), [Rao25] (pp. 1–3 of 12).
Plus an arXiv sweep, 2024-06 to 2026-07, over
`all:sunflower AND cat:math.CO`, `all:"sunflower-free"` and
`abs:sunflower AND cat:cs.CC`, tabulated in `docs/reading.md`. **Empty is
not absence.**

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

  **Re-read in full (12 pages), July 2026.** Version history checked:
  v1 1 June 2026, v2 8 June 2026, **no v3, not withdrawn**. Theorem 1
  (p. 3) and Corollary 1 (p. 7) are as recorded above, verbatim.

  `coq/Compression.v` determines the same quantity exactly:
  $f'(k,s) = \binom{k+s-2}{k}$, attained by all $k$-subsets of a
  $(k+s-2)$-set. [Mis26] defines $f'$ on p. 3 by "cardinality **more
  than** $m$", so $f'$ *is* the extremal number and there is no $+1$ —
  that reading is confirmed.

  **The reason given here for the discrepancy was wrong, and is
  withdrawn.** This entry said the "at least" version came from *"an
  extracted-text summary"*. It did not: the paper's own **abstract**
  says *"cardinality at least $m$"* while its **introduction** says
  *"cardinality more than $m$"*, for the same $f(k,s)$. The paper is
  internally inconsistent. (It also labels two different statements
  "Theorem 1", on pp. 5 and 6.) The convention `coq/Compression.v` uses
  is still the right one, for the right reason now. That is **polynomial in $k$ of degree $s-2$**, against
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

**WITHDRAWN.** This section previously read: *"This is, to the best
knowledge of the authors at the time of writing, the only fully
machine-checked formalisation of the Erdős–Rado 1960 upper bound. We are
unaware of any Mathematical Components or Mathlib formalisation of this
theorem."* The first sentence is **false**, and was false for five years
before this repository started.

- **[Thi21]** R. Thiemann, *The Sunflower Lemma of Erdős and Rado*.
  Archive of Formal Proofs, submitted **25 February 2021**;
  `isa-afp.org/entries/Sunflowers.html`. Isabelle/HOL. **Read pp. 1–4
  and 13–14 of the 14-page proof document** (pp. 5–12 are the Isabelle
  proof script of the induction and were not read). Its abstract, p. 1:

  > We formally define sunflowers and provide a formalization of the
  > sunflower lemma of Erdős and Rado: whenever a set of size-$k$-sets
  > has a larger cardinality than $(r-1)^k \cdot k!$, then it contains a
  > sunflower of cardinality $r$.

  That is `coq/ErdosRado.erdos_rado_upper_bound` — same bound, same
  strict-inequality convention — in a different prover, five years
  earlier. The entry also proves two results this development does not
  (p. 14): `Erdos-Rado-sunflower-card-core` (a core of prescribed
  cardinality) and `Erdos-Rado-sunflower-nonempty-core`.

The narrower claim survives, with its evidence class stated. Mathlib has
no `sunflower` definition, and `google-deepmind/formal-conjectures` issue
#2284 tracks the Erdős–Rado sunflower conjecture as an open formalisation
target. **That is a web-search result, not a rendered page**, and is
recorded as such rather than as verified.

What this development still appears to be alone in having is the *spread
layer* — `SpreadReduction.spread_reduction` as a machine-checked
reduction, with the 2020 spread lemma isolated as a single axiom. No
formalisation of the spread lemma itself was found in any prover.

A formalisation of [ChHa76]'s upper bound would
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
`ALWZ.FractionalSpreadDisjoint n k t` for $t = \Theta(k\log n)$ —
`ALWZ.fractional_form_gives_the_axiom_shape` carries that the rest of
the way to `SpreadReduction.SpreadYieldsDisjoint n k r` for every
$r \ge t$.

**Corrected:** this paragraph used to end *"[Ra20] is the elementary
route to it"*. [Ra20] was read in full in July 2026 and is **not** the
elementary route — its engine is Shannon's noiseless coding theorem. The
elementary route is the counting proof of [ALWZ20] §2 as streamlined by
Park–Pham, written out in [Lovett] §3. See `docs/roadmap.md` §1, rewritten
against it.
