# Sunflower-Formal

A self-contained Coq formalization of the **Erdős–Rado sunflower
problem** — machine-checked proofs of the classical upper bound, the
matching exponential lower bound, the first nontrivial exact value
`f(2,3) = 7` and an infinite family of exact lower bounds at
uniformity 2, a **supermultiplicativity theorem that lifts those into
the first lower bound here beating the product construction**, the
**deterministic half of the 2020 (ALWZ / Rao) spread proof**, constructive Hall and Kőnig theorems for the supporting
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
| **Uniformity 2 is degrees and matchings** | no $k$-sunflower $\iff$ matching number and maximum degree both $\le k-1$ — so $f(2,k)$ is the Chvátal–Hanson problem, which is *cited, not formalised* | `coq/TwoUniform.v` |
| **A sunflower is a matching in a link** | $k$-sunflower $\iff$ some link has $k$ pairwise disjoint members, at every uniformity and with no hypotheses; the row above is its $\lvert Y\rvert \le 1$ case | `coq/LinkCharacterisation.v` |
| **Lower bound at every odd $k$** | $f(2,k) \ge k(k-1) + 1$, two disjoint copies of $K_k$ | `coq/CliqueLowerBound.v` |
| **The extremal function is supermultiplicative** | $g(a{+}b,k) \ge g(a,k)\,g(b,k)$ for $g = f-1$ — the direct sum of two sunflower-free families on disjoint ground sets | `coq/DirectSum.v` |
| **First lower bound beating the product** | $f(n,3) \ge 6^{n/2} + 1 = 2.449\ldots^n$, and $f(n,k) \ge (k(k-1))^{n/2} + 1$ at odd $k$ — strictly above $(k-1)^n + 1$, by a factor growing geometrically | `coq/DirectSum.v` |
| **`g(b) ≥ 2·ι(b)`** | two disjoint copies of an *intersecting* sunflower-free family are sunflower-free; `ι(3) = 10` by exhaustive search gives $f(3,3) \ge 21$ and $f(n,3) \ge 20^{n/3}+1 = 2.714\ldots^n$ | `coq/Intersecting.v` |
| **`g(b) ≤ 2b·ι(b)`** | the converse: the star at the most popular point of a maximal disjoint cover is an *intersecting* sunflower-free family of at least $\lvert F\rvert/(2b)$ members | `coq/Intersecting.v` |
| **The conjecture at $k=3$ is about intersecting families** | $2\iota(b) \le g(b) \le 2b\,\iota(b)$, so the two have the same exponential rate — and **`sunflower_conjecture_k_3` $\iff$ $\exists C\,\forall b,\ \iota(b) \le C^b$**, an equivalence, not a sufficient condition | `coq/IotaRate.v` |
| **3-sunflowers are decidable** | `sunflower3b` is proved sound *and* complete, so any bound on sunflower-free families becomes an `UpperBound` — the step the equivalence above needs | `coq/F23.v` |
| **The link restriction is vacuous** | every uniform family is a link, so a spread lemma restricted to the families the sunflower recursion produces implies the unrestricted one | `coq/SpreadRestrictions.v` |
| **The reduction needs strictly less** | it only ever applies the spread lemma to *sunflower-free* families, so a weaker hypothesis suffices — the narrower interface for a future proof of Rao's Lemma 2 | `coq/SpreadRestrictions.v` |
| **What the polynomial method is missing** | Naslund–Sawin's $constant^n$ bound is in the *ground set*; one further fact — that extremal uniform families live on $O(m)$ points — would turn it into the conjecture at $k=3$ | `coq/SliceRank.v` |
| **The same hypothesis, where the data supports it** | that fact is unsupported for general families ($N(3,g)$ still climbing at $3m$) and *measured* for intersecting ones ($\iota(3,g)$ flat at 10 from six points to fourteen) — and by the equivalence above the intersecting version suffices | `coq/IotaGround.v` |
| **A ground-set-aware link bound** | $b\lvert F\rvert \le \lvert U\rvert\, N(b{-}1,\lvert U\rvert{-}1)$ by double counting, met with equality at four measured rows — which forces the extremal families to be regular. Unconditionally $N(3,g) \le 2g$ | `coq/IotaGround.v` |
| **The pure link is intersecting** | the members meeting a maximal-matching cover exactly once, with that point removed, pairwise intersect — so one of the Erdős–Rado degrees is bounded by $\iota(b{-}1)$ rather than $g(b{-}1)$, giving $2\lvert F\rvert \le \lvert T\rvert(g(b{-}1) + \iota(b{-}1))$. Reproduces $g(2)=6$ and $\iota(2)=3$ exactly; gives **$f(3,3) \le 28$**, and **$\le 27$** once the matching members are charged the $b$ points of the cover they actually occupy, where Erdős–Rado gives 49 | `coq/PureLink.v` |
| **`ι(b)` is decided by one finite search** | an $n$-member intersecting $b$-uniform family has support $\le b + (b{-}1)(n{-}1)$, so a statement quantified over every ground set becomes a search on $b + (b{-}1)N$ points. At $b=3$ that is 23 points, the search is exhaustively empty at eleven members, and **$\iota(3) = 10$** exactly | `coq/PureLink.v`, `rust/src/wide.rs` |
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

The lower end of that bracket is no longer the best thing proved here.
Sunflower-freeness survives the direct sum of two families on disjoint
ground sets (`coq/DirectSum.v`), so $g = f - 1$ is supermultiplicative,
and feeding it this repository's own exact value $f(2,3) = 7$ gives
$f(n,3) \ge 6^{\lfloor n/2\rfloor} + 1 = 2.449\ldots^{\,n}$ against the
product construction's $2^n$. Seeding it instead with $f(3,3) \ge 21$ —
which `coq/Intersecting.v` gets by doubling the largest *intersecting*
sunflower-free 3-uniform family, $\iota(3) = 10$ — gives

$$f(n,3) \;\ge\; 20^{\lfloor n/3\rfloor} + 1 \;=\; 2.714\ldots^{\,n}.$$ At every odd $k$ the same
theorem applied to the two-cliques family gives
$f(n,k) \ge (k(k-1))^{\lfloor n/2\rfloor} + 1$, beating $(k-1)^n + 1$ by
$(k/(k-1))^{n/2}$. The targeted search recorded under [Relation to
prior formalizations](#relation-to-prior-formalizations) found no
machine-checked sunflower lower bound at all, in any system, so this is
very likely the first one above the trivial product construction — but
that is a claim about a search, not a proved fact. It is
still a long way from the literature: Abbott–Hanson–Sauer (1972) reach
$3.162\ldots^n$ at $k = 3$, by a *substitution* recursion
$g(ab) \ge g(a)\,\iota(b)^a$ that the direct sum does not reach — see
[`docs/roadmap.md`](docs/roadmap.md) §5.

**What `ι` turns out to be.** It is not just a convenient seed. The
converse of the doubling holds up to a factor: a sunflower-free family
has no three pairwise disjoint members, so a maximal disjoint subfamily
spans at most $2b$ points and meets everything, and the star at the most
popular of those points is *intersecting*, sunflower-free and has at
least $\lvert F\rvert/(2b)$ members. So

$$2\,\iota(b) \;\le\; g(b) \;\le\; 2b\,\iota(b),$$

and $2b$ is subexponential. `coq/IotaRate.v` draws the consequence:
**the sunflower conjecture at $k = 3$ is equivalent to an exponential
bound on intersecting sunflower-free families**, and every lower-bound
construction at uniformity $b$ — the 1972 substitution included — is
capped at $2b\,\iota(b)$. That is a statement about *where the problem
lives*, not a better constant: the bound it gives at $b = 3$ is
$g(3) \le 108$, well above Erdős–Rado's 48. The measured rates
$\iota(b)^{1/(b-1)}$ are $3.000,\, 3.162,\, 3.000,\, {<}3.142$ — flat
over everything decided, which through the equivalence is mild evidence
for the conjecture at $k=3$ with $c(3)$ near $3.2$.

At uniformity 2 the picture is sharper than that bracket suggests. A
distinct family of pairs is a graph, and it avoids $k$-sunflowers
exactly when its matching number and its maximum degree are both at
most $k-1$ (`coq/TwoUniform.v`) — so $f(2,k)$ *is* the Chvátal–Hanson
extremal problem at $D = \nu = k-1$, and the spread hypothesis at
uniformity 2 is the same problem again. That identification is proved
here; the extremal function itself is not. $f(2,k) \ge k(k-1)+1$ for
every odd $k$ is proved outright, from two disjoint copies of $K_k$
(`coq/CliqueLowerBound.v`). Taking [Chvátal–Hanson 1976](docs/references.md) on citation upgrades that
to equality and pins the sharp spread threshold at $r = k$ against the
$2k-1$ this development proves — both conditional, both falsified
rather than assumed in `rust/tests/chvatal_hanson.rs`.

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

- **The sharp threshold $r^{*}(m,3)$.** Write $r^{*}(n,k)$ for the least
  $r$ making `SpreadYieldsDisjoint n k r` true. Since the reduction
  turns it into $f(m,k) \le r^m + 1$, **whether $r^{*}(m,3)$ is bounded
  in $m$ is the sunflower conjecture at $k = 3$** — the sequence is not
  evidence about the problem, it *is* the problem. `coq/SpreadThreshold.v`
  proves two upper bounds on it, both better than the $2n+1$ above:
  $r^{*}(n,3) \le 2n$ from the two-member cover, and
  $r^{*}(n,3) \le 1 + \sqrt{3n^2 - 4n + 3}$ from a decomposition against
  a matching. The second turns on the fact that for $B$ *any* member of a
  family with no three pairwise disjoint members, $\{C : C \cap B =
  \emptyset\}$ is intersecting; the resulting pieces are covered by
  *pairs*, whose degree is $r^{m-2}$ rather than $r^{m-1}$. At $n = 4$
  that is $r^{*}(4,3) \le 7$, down from 9. `rust/src/rstar.rs` searches
  for the matching lower bounds — two independent searches, a SAT
  encoding with lex-leader symmetry breaking and a depth-first
  enumeration with counting bounds — and pins the counterexample families
  it finds.

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
  Neither could fail a build. Six mechanisms now target that class of
  error — coherence theorems that would derive `False` if two of the
  development's own bounds contradicted each other (`coq/Audit.v`); a
  second, independently-implemented spread decision procedure proved
  to agree with the first (`coq/Reflect.v`); an exhaustive search for
  counterexamples to the axiom's shape over small ground sets
  (`make testbed`); and mutation testing of the definitions
  (`make mutants`), which weakens one hypothesis at a time and checks
  that something breaks. Of 150 mutations, 147 are killed outright, two
  survive — `LowerBound`'s `length F = m` really is documentation, as
  `Audit.LowerBound_ge_equiv` proves, and `Product.IotaAtLeast`'s is too,
  by `Product.IotaAtLeast_antitone` — and one is a positive control
  that must survive. Fifth, statement baselines (`make statements`):
  every audited theorem's statement and every core definition's body is
  recorded in `tools/statements.txt`, and CI fails if one moves without
  the baseline moving in the same commit — which is what turns "did this
  change what we claim?" from a rereading exercise into a one-line diff.
  Sixth, one level up again, `make docnumbers` checks every count this
  prose quotes about itself against the list it is a count of — three
  were already wrong when that gate was written. Seventh, `make ceilings`
  costs every *route*: each reduction declares the best `f(n,3)` bound it
  could ever produce, and `tools/ceiling.py` compares it in exact integer
  arithmetic against Erdős–Rado 1960, against the record, and against the
  target, failing the build when a route's declared verdict disagrees with
  its own arithmetic. That gate exists because five sessions of correct
  work were done inside a reduction whose best case was worse than the
  1960 bound and nobody had multiplied it out. Underneath them, `coqchk`
  re-verifies every module with Coq's separate kernel checker and
  gates on a whole-library assumption census, which is what makes
  "zero admits" a claim about the development rather than about a list
  of theorem names. See [`docs/testing.md`](docs/testing.md).

  The search found the five-cycle, which is now a theorem: together
  with the disjoint-blocks family it shows the axiom's conclusion is
  *false* below `r = k-1`, while `spread_disjoint_above_elementary`
  shows it is *true* above `r = n(k-1)`. The axiom asserts something
  about the gap in between — neither vacuous nor already proved.

- **A sunflower is a matching in a link.** For $Y \subseteq A, B$ the
  identity $A \cap B = Y \iff (A \setminus Y) \cap (B \setminus Y) =
  \emptyset$ turns both halves of the definition of a sunflower into one
  matching condition in one derived family
  (`coq/LinkCharacterisation.v`):

  $$\text{a } k\text{-sunflower} \iff \exists Y,\ \text{the link
  } \{A \setminus Y : Y \subseteq A \in \mathcal{F}\}\ \text{has
  } k \text{ pairwise disjoint members}.$$

  No uniformity, no distinctness, no hypothesis on $k$. This makes the
  uniformity-2 characterisation above the case $|Y| \le 1$ — proved as
  a corollary, by a route sharing no step with the original — and turns
  `link_sunflower_lift` from a one-way reduction into an equivalence.
  Above uniformity 2 the quantifier over $Y$ is doing work:
  $\{0,1,2\}, \{0,1,3\}, \{0,1,4\}$ has a 3-sunflower whose only
  core is $\{0,1\}$, and no core of size $\le 1$ works for it.

  It was falsified before it was proved. The equivalence was enumerated
  against a brute-force sunflower detector over every family on five and
  six points at uniformities 2 and 3, over every family of *arbitrary*
  sets on four points, and over a sample at ground 7
  (`rust/tests/link_characterisation.rs`). The non-uniform enumeration
  earned its keep: it found that a member may equal the core of a
  sunflower it belongs to, contributing the *empty* petal to the link —
  a case no uniform family exhibits, and one that
  `pairwise_disjoint_sunflower`'s nonemptiness hypothesis used to
  exclude. That hypothesis is now gone, and it was decoration in three
  other lemmas too.

  What it does not buy: nothing here bears on the conjecture's bound.

- **The conjecture, restated without sunflowers.** Because the
  reduction is lossless — it gives exactly $r^n$ — a spread lemma whose
  threshold does not grow with $n$ would settle the conjecture.
  `spread_conjecture_suffices` proves that implication, turning the
  \$1000 problem into: *is there, for each $k$, a constant $c_k$ such
  that every $c_k$-spread family of more than $c_k^{\,n}$ sets of size
  $n$ has $k$ pairwise disjoint members?*

## Verifying

```bash
make verify        # builds all 45 Coq files, then runs the axiom audit
```

Expected: every audited theorem (665 of them, including `f_2_3_eq_7`,
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

`coqchk` re-checks every module with Coq's *separate* kernel
implementation and prints a whole-library assumption census — unlike
the audit above, which covers only the theorem names the Makefile
enumerates:

```bash
make coqchk        # independent re-check; exactly one axiom library-wide
```

CI gates on that census listing exactly `Sunflower.ALWZ.Rao20_lemma2`,
and on no reliance on type-in-type, unsafe fixpoints, or assumed
positivity. Two further checks target what no kernel can see — whether
the *definitions* say what their names claim:

```bash
make mutants       # weaken each definition in turn; see what breaks
make testbed       # exhaustive falsification of the spread hypothesis
```

All are CI jobs. The methodology, and what it does and does not
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
  bound, of any lower bound *above* it (`coq/DirectSum.v`), or of any
  part of the post-2020 spread argument in any
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

[`docs/reading.md`](docs/reading.md) records what was actually read —
one entry per source, with an explicit page count, verbatim quotations
with page numbers, and a register of every claim this repository makes
about the literature, resolved to confirmed / refuted / not found /
unreachable. Sources that could not be reached have entries saying so.

See [`docs/references.md`](docs/references.md) for the full list, where
every annotation now states its evidence class (*read in full / read
pp. N–M / abstract only / unreachable / not attempted / inferred*). Key
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
