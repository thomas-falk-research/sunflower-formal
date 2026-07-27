# The spread framework (ALWZ–Rao–FKNP–BCW), and what is formalised

The 2020 breakthrough on the Sunflower Conjecture replaced the 1960
Erdős–Rado bound $f(n,k) \le (k-1)^n n! + 1$ with $f(n,k) \le (Ck\log
n)^n$. This document explains the argument and states precisely which
part of it is machine-checked here.

**Summary of the trust story.** The argument splits cleanly into a
*reduction* and a *spread lemma*. In this development:

| Half | Status |
|---|---|
| Reduction: "spread ⟹ $k$ disjoint members" implies $f(n,k) \le r^n+1$ | **proved** — `SpreadReduction.spread_reduction`, closed under the global context |
| Spread lemma at the elementary parameter $r = n(k-1)+1$ | **proved** — `SpreadReduction.elementary_spread_disjoint` |
| Spread lemma at the 2020 parameter $r = \Theta(k\log(nk))$ | **assumed** — `ALWZ.Rao20_spread_lemma`, the development's only axiom |

Consequently the repository contains an *unconditional* Erdős–Rado-quality
bound proved entirely through the modern framework
(`SpreadReduction.spread_erdos_rado`), and the modern bound itself as a
theorem whose only assumption is the spread lemma
(`ALWZ.sunflower_bound_from_spread_lemma`).

## Spread families

Let $\mathcal{F}$ be a finite family of finite sets and $r \ge 1$.
$\mathcal{F}$ is **$r$-spread** if for every finite set $T$,

$$r^{|T|}\cdot\bigl|\{A \in \mathcal{F} : T \subseteq A\}\bigr| \;\le\; |\mathcal{F}| .$$

No small set is over-represented: the fraction of $\mathcal{F}$
containing $T$ decays like $r^{-|T|}$.

Coq: `Spread.Spread`, with `Spread.deg T F` for the count.

> **A defect that was found and fixed.** Earlier revisions of this
> repository defined spreadness by quantifying over *all lists* $T$,
> including lists with repeated entries. That definition is degenerate:
> taking $T = [x,x,\dots,x]$ forces $r^{t}\cdot\deg(\{x\}) \le
> |\mathcal{F}|$ for every $t$, so for $r \ge 2$ no member of the family
> may contain any element at all. This is now recorded as a theorem —
> `Spread.w_spread_legacy_degenerate` — rather than a comment, and the
> corrected definition quantifies over `NoDup` lists, i.e. over genuine
> finite sets. `ALWZ.spread_singletons` exhibits a concrete spread
> family (three singletons, $3$-spread, certified by `vm_compute`
> through the decision procedure) as a standing guard against the same
> mistake recurring.

## The reduction (proved)

**Theorem** (`SpreadReduction.spread_reduction`)**.** Fix $k \ge 2$ and
$r \ge 1$, and suppose

> $(\ast)$ every $r$-spread distinct family of $m$-element sets, $1 \le
> m \le n$, contains $k$ pairwise disjoint members.

Then $f(m,k) \le r^m + 1$ for every $m \le n$: any distinct
$m$-uniform family with more than $r^m$ members contains a
$k$-sunflower.

*Proof* (strong induction on $m$). For $m = 0$ all members are empty, so
a distinct family has at most one member, while $r^0 + 1 = 2$ are
assumed. For $m \ge 1$, decide whether $\mathcal{F}$ is $r$-spread.

- **Spread.** By $(\ast)$ there are $k$ pairwise disjoint members. They
  are nonempty (uniformity $m \ge 1$) and pairwise disjoint, hence a
  $k$-sunflower with empty core.
- **Not spread.** There is a nonempty $T$ with $r^{|T|}\deg(T) >
  |\mathcal{F}| > r^m$. Since $T$ is contained in some member,
  $1 \le |T| \le m$, and cancelling $r^{|T|}$ gives $\deg(T) >
  r^{\,m-|T|}$. The **link**
  $$\mathcal{F}_T \;=\; \{\,A \setminus T \;:\; T \subseteq A \in \mathcal{F}\,\}$$
  is $(m-|T|)$-uniform, still distinct (two members containing $T$ that
  agree off $T$ are equal), and has exactly $\deg(T) > r^{\,m-|T|}$
  members. The induction hypothesis applies, and a $k$-sunflower in the
  link lifts to one in $\mathcal{F}$ by merging $T$ into the core. ∎

Two points about the formalisation.

*The dichotomy is decidable, not classical.* "Either $\mathcal{F}$ is
$r$-spread or some $T$ violates the condition" is an unbounded
quantifier over sets $T$, and taking the classical negation would import
excluded middle as an axiom — exactly the sort of hidden assumption this
repository exists to avoid. Instead `Spread.spread_witness` searches a
concrete finite list of candidates, the sublists of members
(`Spread.subsets`), and returns a violator or `None`. Soundness is
immediate; completeness (`Spread.spread_witness_none`) is the one real
step: for an arbitrary `NoDup` set $T$ of positive degree contained in a
member $A$, the sublist `filter (fun x => memb x T) A` has exactly the
same elements as $T$ — hence the same cardinality and the same degree —
and *is* among the candidates. The whole reduction is therefore
constructive.

*The lift is set-indexed.* `Sunflower.sunflower_lift` handles removing a
single element. The link removes a whole set, so
`Spread.sunflower_lift_set` generalises it: for $S$ a sunflower with core
$Y$ whose members avoid $T$, the family $\{T \cup B : B \in S\}$ is a
sunflower with core $T \cup Y$. The intersection identity needed is pure
set algebra, $(T \cup A) \cap (T \cup B) = T \cup (A \cap B)$, with no
disjointness hypothesis; disjointness is needed only to see that
distinctness survives.

### The bound is exactly $r^n$

Note what the induction gives: the sunflower bound is precisely the
spread threshold raised to the uniformity. This is why the published
bounds have the shape they do — $r = \Theta(k\log n)$ gives $(Ck\log
n)^n$ — and why an $O(1)$ spread threshold would resolve the conjecture
outright.

## The elementary spread lemma (proved)

**Theorem** (`SpreadReduction.elementary_spread_disjoint`)**.** $(\ast)$
holds with $r = n(k-1)+1$.

*Proof.* Take a maximal pairwise-disjoint subfamily $\mathcal{D}$
(`ErdosRado.max_disjoint_cover`). If $|\mathcal{D}| \ge k$ we are done.
Otherwise $X = \bigcup \mathcal{D}$ has at most $(k-1)m \le (k-1)n < r$
elements, and every member of $\mathcal{F}$ meets $X$ by maximality. By
pigeonhole (`Pigeonhole.pigeonhole_family`) some $x \in X$ satisfies
$|X|\cdot\deg(\{x\}) \ge |\mathcal{F}|$ with $\deg(\{x\}) \ge 1$; since
$r > |X|$ this gives $r\cdot\deg(\{x\}) > |\mathcal{F}|$, contradicting
spreadness at $T = \{x\}$. ∎

Feeding this into the reduction:

**Corollary** (`SpreadReduction.spread_erdos_rado`, axiom-free)**.**
$$f(n,k) \;\le\; \bigl(n(k-1)+1\bigr)^n + 1 .$$

This is *comparable to, and slightly weaker than*, Erdős–Rado: $(nk)^n$
against $(k-1)^n n! \approx (nk/e)^n$, a factor $e^n$ worse. It is not
presented as an improvement. Its value is that it is an unconditional
theorem proved by the modern route, which means the reduction machinery
is exercised end-to-end by the kernel rather than resting on an
assumption — the standard failure mode for "framework" formalisations is
that the framework turns out to prove nothing.

## The spread lemma (assumed)

**Theorem** (ALWZ 2020; Rao 2020; BCW 2021)**.** There is an absolute
constant $C$ such that $(\ast)$ holds whenever $r \ge Ck\log(nk)$ (Rao);
BCW sharpen this to $r \ge Ck\log n$.

Coq: `ALWZ.Rao20_spread_lemma`, the single axiom of the development.
From it, `ALWZ.sunflower_bound_from_spread_lemma` derives
$$f(n,k) \;\le\; \bigl(C k \log_2(nk+1)\bigr)^n + 1 .$$

The probabilistic content is the passage from spreadness to a random
subset containing a member: for $\mathcal{F}$ an $r$-spread family with
$r = \Theta(\log n)$, a uniformly random subset $W$ of the ground set of
the appropriate density contains a member of $\mathcal{F}$ with
probability $\ge 1/2$. Splitting the ground set into $k$ random parts and
applying this to each — which costs the extra factor $k$ in the
threshold — yields $k$ members lying in disjoint parts, hence pairwise
disjoint. That is exactly $(\ast)$.

### What discharging the axiom would take

The original ALWZ argument is probabilistic and would need a
finite-probability layer. **Rao's proof does not.** "Coding for
sunflowers" replaces the probabilistic step with an encoding/counting
argument: assuming too many sets $W$ fail to contain a member of
$\mathcal{F}$, one builds an injection from the failing $W$'s into a
strictly smaller collection of encodings, contradicting a binomial
count. Everything in it is finite: injections between finite sets and
binomial estimates, no measure theory. That makes it a realistic target
for the stdlib-only, list-based style used here, and it is the reason
the axiom in this repository has been restated as the spread lemma
rather than as the final bound: the interface a future proof must meet
is now exactly Rao's theorem, and nothing downstream of it will need to
change.

Concretely, a formalisation would need:

1. counting infrastructure for finite subsets of a ground set — the
   `subsets` enumeration in `Spread.v` is a start, plus binomial
   coefficients and the standard $\binom{N}{m}$ estimates;
2. the encoding map and the proof that it is injective on failing sets;
3. the arithmetic that the encoded range is smaller than
   $\binom{N}{m}$, which is where the explicit constant lives.

Steps 1 and 3 are bookkeeping-heavy but routine; step 2 is the
mathematical content.

## Why none of this resolves the conjecture

The conjecture asks for $f(n,k) \le c_k^n$ with $c_k$ independent of
$n$. By the reduction, that is *equivalent* to a spread lemma with an
$n$-independent threshold $r = c_k$: an $O_k(1)$-spread family of
$n$-sets would have to contain $k$ pairwise disjoint members. The $\log
n$ in the current threshold is not an artefact of the reduction — the
reduction is lossless, giving exactly $r^n$ — it is a genuine feature of
every known proof of the covering step. Removing it is the open problem,
and this repository claims no progress on it.

## Provenance and references

- **[ALWZ20]** R. Alweiss, S. Lovett, K. Wu, J. Zhang, "Improved bounds
  for the sunflower lemma", *STOC 2020* (arXiv 1908.08483). The
  breakthrough; original spread lemma, probabilistic proof.
- **[Ra20]** A. Rao, "Coding for sunflowers", *Discrete Analysis*
  2020:2 (arXiv 1909.04774). Elementary encoding proof; the threshold
  $\Theta(k\log(nk))$ used in the axiom here.
- **[FKNP19]** K. Frankston, J. Kahn, B. Narayanan, J. Park, "Thresholds
  versus fractional expectation-thresholds", *Ann. of Math.* 194 (2021)
  (arXiv 1910.13433).
- **[BCW21]** T. Bell, S. Chueluecha, L. Warnke, "Note on sunflowers",
  *Discrete Math.* 344 (2021). Sharpens the threshold to
  $\Theta(k\log n)$, giving the frequently quoted $(Ck\log n)^n$.
- **[Stoeckl]** M. Stoeckl, presentation of the streamlined proof
  reaching $C = 64$.
- **[Ko97]** A. V. Kostochka, "An intersection theorem for systems of
  finite sets", *Acta Math. Hungarica* 1997.
- **[KRT99]** A. V. Kostochka, V. Rödl, L. A. Talysheva, "On systems of
  small sets with no large $\Delta$-subsystem", *CPC* 1999.
- **[ErRa60]** P. Erdős, R. Rado, "Intersection theorems for systems of
  sets", *J. London Math. Soc.* 35 (1960), 85–90.
- **[Er81]** P. Erdős, "On the combinatorial problems which I would most
  like to see solved", *Combinatorica* 1 (1981), 25–42. The \$1000 prize
  for $k = 3$.

## Map to the Coq sources

| Object | Coq |
|---|---|
| $r$-spread | `Spread.Spread` |
| $\deg(T)$ | `Spread.deg` |
| degenerate old definition + refutation | `Spread.w_spread_legacy`, `Spread.w_spread_legacy_degenerate` |
| candidate enumeration / decision | `Spread.subsets`, `Spread.spread_witness`, `Spread.spread_witness_none` |
| link $\mathcal{F}_T$ | `Spread.link`, `Spread.link_uniform`, `Spread.link_distinct` |
| set-indexed sunflower lift | `Spread.sunflower_lift_set`, `Spread.link_sunflower_lift` |
| hypothesis $(\ast)$ | `SpreadReduction.SpreadYieldsDisjoint` |
| the reduction | `SpreadReduction.spread_reduction` |
| elementary spread lemma | `SpreadReduction.elementary_spread_disjoint` |
| unconditional bound via the framework | `SpreadReduction.spread_erdos_rado` |
| the 2020 spread lemma (axiom) | `ALWZ.Rao20_spread_lemma` |
| the modern bound (derived) | `ALWZ.sunflower_bound_from_spread_lemma` |
