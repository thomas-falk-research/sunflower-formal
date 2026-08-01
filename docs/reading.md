# Reading log

What was actually read, page by page, and what it changed here.

This file exists because five sessions of machine-checked work were built
on a literature base that had never been opened. `docs/roadmap.md` §15
put the problem plainly: *"the repository's single axiom comes from an
eight-page open-access paper that nobody here has opened."* This session opened it, and thirty-two other papers, plus the
MathOverflow answer this repository had been citing without reading.
**Eleven papers were read cover to cover** — [Ra20] 8pp, [ALWZ20] 19pp,
[BCW21] 3pp, [Lovett] 28pp, [MNSZ22] 8pp, [ErRa60] 6pp, [Mis26] 12pp,
[Rao25] 12pp, [Fuk25] 8pp, [NaSa17] 5pp and [Kup25] **66pp**, the survey
of the method this problem belongs to — plus Hunter's answer in full and
seven more in part.

## The rules this file is written under

1. **Read** means: PDF downloaded, every page rendered with
   `pdftoppm -png -r 150`, every rendered page looked at. Anything less
   is reported as a page range.
2. `pdftotext` was used **only** to locate which page a term is on, and
   **its negatives are worthless** — see the box below. No quotation in
   this file comes from extracted text.
3. Every quotation is verbatim, from a rendered page, with the page
   number. Where a source is quoted second-hand that is said explicitly.
4. Nothing is quoted from a web-search snippet, an abstract, a survey's
   description of a third paper, or training data.
5. A source that could not be reached gets an entry saying so, with the
   reason and the attempts.

> **Rule 2 was not strong enough, and this file broke it.** The first
> pass at register row B12 concluded that the strings "covering number",
> "transversal" and "maximal intersecting" *"do not occur anywhere in
> [Kup25]'s 66 pages"*, from a page-by-page `pdftotext` search. Then
> page 19 was rendered:
>
> > he ... shows that `G` should be empty using a simple, but somewhat
> > tedious, 'covering number' argument which we avoid. [Kup25, p. 19]
>
> The extractor had broken the phrase across a line — `'covering` then
> `number'` — so a search for the two-word string missed it, silently, in
> a document that contains it. **`pdftotext` cannot be used to establish
> that something is absent.** Every negative in this file that rested on
> one has been re-derived from rendered pages or withdrawn.
>
> **And a negative is only as good as its worst synonym.** This corpus
> has five names for a sunflower — *sunflower*, *Δ-system*, *`s`-star*,
> *weak sunflower*, *pseudo-* and *near-sunflower* — and five for a
> cover — *cover*, *base*, *nucleus*, *generating set*, *crosscut*,
> *minimal cover*. Every "not found" here has been run against one or two
> of each. They are recorded as searches that happened, not as absences.

Evidence classes used throughout, here and in `docs/references.md`:

```
  read in full        every page rendered and read
  read pp. N–M        that range only; the rest is not claimed
  abstract only       the arXiv/journal abstract page, nothing else
  unreachable         attempted, blocked; attempts recorded
  not attempted       named but not chased this session
  inferred            from a citing paper or survey; never treated as read
```

---

## The register

The deliverable. One row per claim the repository makes about the
literature, resolved.

### Tier A — claims the formal development rests on

| # | Claim | Verdict | Evidence |
|---|---|---|---|
| A1 | `Rao20_lemma2` is Rao 2020 Lemma 2, weaker in exactly two recorded respects | **Refuted in part** | [Ra20] read in full (8pp). The statement is faithful; the *description of the gap* was wrong in one direction and incomplete in another. See A1a–A1c. |
| A1a | "the source allows sets of size at most `m`" | **Refuted** | [Ra20, p. 2]: *"a sequence of sets S₁,…,S_ℓ ⊂ [n] **of size k**"*. Exactly `k`. The "at most" convention is [ALWZ20]'s, p. 1. Wrong source cited. |
| A1b | `log2_up` over-estimates, so the axiom demands more of `r` | **Confirmed** | [Ra20, p. 3]: *"All logarithms are taken base 2."* `Nat.log2_up (S (k*n)) ≥ log₂(kn)`. |
| A1c | The axiom quantifies over all `r ≥ threshold`; Rao fixes one `r` | **New, unrecorded, now discharged** | [Ra20, p. 2] states Lemma 2 at `r(p,k)` only. `ALWZ.fractional_form_gives_the_axiom_shape` now derives the quantified shape from the fractional single-threshold form. |
| A2 | Whether the `log` is necessary in the *disjointness* form is open; "looked for and not found" | **Confirmed, and found** | [Ra20, p. 2]: *"As far as we know, it is possible that Lemma 2 holds even when r(p,k) = O(p). Such a strengthening of Lemma 2 would imply the sunflower conjecture of Erdős and Rado."* [ALWZ20] Lemma 3.1 and [BCW21] Lemma 4 are both tightness examples for the **robust/covering** form, not disjointness. |
| A3 | [AHS72] gives `ι(3)=10`, `g(ab) ≥ g(a)ι(b)^a`, and the exact `f(2,k)` | **Unreadable (primary); corroborated (secondary, now from rendered pages)** | Paywalled, see the entry below for the four attempts. [Kup25] pp. 5–6 rendered confirms both quoted sentences verbatim. |
| A4 | Erdős–Rado 1960's constant is `(k−1)ⁿ·n!` | **Refuted as "the original constant"; the Coq theorem is unaffected** | [ErRa60] read in full (6pp, 85–90). Theorem III's constant is `b!a^{b+1}(1 − 1/(2!a) − … )` for *systems with repeats*; the distinct-family bound the paper actually derives is `φ(a,b) ≤ b!a^b(1 − 1/(2!a) − …)`, **strictly sharper** than `b!a^b`. |
| A5 | `f(n,3) ≳ 10^{n/2}` is still the record in July 2026 | **Confirmed** (no counterexample found; search described below) | arXiv sweep of `all:sunflower AND cat:math.CO` and `all:"sunflower-free"`, 2024-06 → 2026-07, 30 hits: no lower-bound improvement. [Kup25] p. 6 still states `φ(k,3) ⩾ 10^{(k/2)−c log k}` as the bound. |
| A6 | Current best upper bound | **Confirmed: `(Cp log k)^k`, Bell–Chueluecha–Warnke** | [BCW21] read in full (3pp). Theorem 1, p. 1: *"There is a constant C ≥ 4 such that Sun(p,k) ≤ (Cp log k)^k for all integers p, k ≥ 2."* One 2025 preprint claims better; see A6a. |
| A6a | Anything since 2021 | **A claim exists, unrefereed** | Fukuyama, arXiv:2510.19037v2 (1 Dec 2025), read in full (8pp): `(ck² ln m / ln ln m)^m`. Preprint only, no journal; the author's own page describes the proof as not yet stable. Recorded, **not** adopted. |
| A7 | "the only fully machine-checked formalisation of the Erdős–Rado 1960 upper bound" | **REFUTED** | AFP entry *The Sunflower Lemma of Erdős and Rado*, René Thiemann, Isabelle/HOL, submitted **25 February 2021**. Its abstract: *"whenever a set of size-k-sets has a larger cardinality than (r − 1)^k · k!, then it contains a sunflower of cardinality r"* — the same bound, same convention, five years earlier. |
| A8 | [Mis26] still says what the repository read it as saying | **Confirmed with a correction to the *reason*** | Read in full (12pp). Still v2 (8 Jun 2026), not withdrawn, no v3. `f'` on p. 3 does say "cardinality **more than** m" — the repository's reading is right. But its explanation was wrong: the **abstract** genuinely says "at least m" for `f`. The paper is internally inconsistent, not mis-extracted. |

### Tier B — novelty claims, all previously "not found, not exhaustive"

| # | Claim | Verdict | Evidence |
|---|---|---|---|
| B9 | `ι(b)` (max *intersecting* sunflower-free family) is unnamed | **Not found** — but the search vocabulary was too narrow | Not in [Kup25] (now read in full, 66pp), [Ra20] (8pp), [ALWZ20] (19pp), [Lovett] (28pp), [Rao25] (12pp). **Caveat found this session:** [Kup25] fn. 6, p. 21, records that *"it is in this paper that `Δ(s)`-systems are called **`s`-stars**, a name that appears in the follow-up papers of Frankl and Füredi."* A third name for a sunflower, which every search here has missed. Empty is not absence, and this corpus is not vocabulary-complete. |
| B10 | The sandwich `2ι(b) ≤ g(b) ≤ 2b·ι(b)`, and the `k=3` equivalence | **Not found** | Same corpus. But see B10a — the *ingredients* are all published. |
| B10a | "the intersecting side has never been pointed at" | **REFUTED** | [ALWZ20] §4.2, titled *Intersecting set systems*, Theorem 4.2 p. 13: *"If F is an intersecting w-uniform set system, and for all T, \|F_T\| ≤ κ^{−\|T\|}\|F\|, then κ = O(log w)."* Different hypothesis from `ι` (spread, not sunflower-free), but the claim as written is false. Withdrawn in `coq/IotaRate.v`; the elementary version is now `IotaRate.intersecting_not_spread_above_uniformity`. |
| B11 | The cone `g(b−1) ≤ ι(b)` is folklore | **Technique found; exact statement still not found** | Hunter's answer uses the same move — *"start with a maximal `t`-sunflower-free collection in uniformity `k−1`, and then add a unique 'dummy element' to each edge"* — in exactly this context. His dummies are *distinct per edge* (which grows the ground set); the repository adds *one shared* fresh point to every member (which makes the family intersecting). Same idea, different construction, different conclusion. No novelty was claimed and none is now. |
| B12 | `τ(substitute(G,H)) = τ(G)τ(H)`, and the maximality of the AHS families | **The earlier "not found" is WITHDRAWN. The surrounding literature is central to the survey; the specific identity is still not found.** | [Kup25] read in full. Its §1.7 *Approaches to constructing bases* is about exactly this material, under names this repository did not search for: **base**, **nucleus**, **generating set**, **crosscut**, **minimal cover**. p. 52: *"the produced sets ... give exactly the family of **minimal covers** for the sets in `F`. These are the bases of the type used by Frankl in [44]. In a recent paper of Frankl [52], the family of minimal covers is efficiently analyzed in order to bound the maximal diversity of an intersecting family."* — and the construction is *"essentially due to Erdős and Lovász [39]"*. p. 59: *"a `d`-simplex are the simplest examples of non-trivial intersecting families, that is, **intersecting families with covering number 2**."* So `τ` of intersecting families is a studied quantity with a named literature. The multiplicativity identity itself is still not found, but the search that said the area was untouched was wrong twice over — wrong vocabulary, and a broken extractor. |
| B13 | `ρ` multiplicativity, and the AHS spreadness profile `κ = b^{log₃2}` | **Not found** | Not in [ALWZ20] §3 (read), not in [Kup25] (now read in full). But note [Kup25] §1.7, p. 49: spreadness is now a *tool* in this literature — *"r-spread families in many ways behave like sunflowers with r petals, albeit they are much easier to find"* — via the Kupavskii–Zakharov **peeling-simplification** and **spread approximation** methods, neither of which this repository knew about. Not exhaustive. |
| B14 | Zach Hunter's ground-set equivalence, credited to MathOverflow | **FOUND AND READ IN FULL** | `mathoverflow.net/a/463150`, 30 Jan 2024, answering domotorp's question 462924. Retrieved verbatim through the StackExchange API after `WebFetch` was blocked for the site. Quoted in full below; it confirms the equivalence *and* contains two further things this repository has. |
| B15 | Prescribed-symmetry / Kramer–Mesner applied to sunflower-free families | **Not found** | Nothing in the 2024–2026 arXiv sweep, nothing in [Kup25] pp. 5–6. Not exhaustive over design-theory venues. |
| B16 | `ι(3)=10` is the unique simple 2-(6,3,2) design | **VERIFIED — by exhaustion, not by citation** | The Handbook of Combinatorial Designs is not open access, so the uniqueness claim could not be read. It does not need to be: there are only `C(20,10) = 184756` ways to choose ten triples from the twenty on six points. Enumerated — exactly **12** are simple 2-(6,3,2) designs, and all 12 form a **single** isomorphism class under `Sym(6)`. `720/12 = 60` re-derives `\|Aut\|` independently of `structure::automorphisms`, and agrees with it. `rust/tests/iota_structure.rs::the_two_six_three_two_design_is_unique_and_that_is_checked_not_cited`. |

### Tier C — the four proofs, and the formalisation decision

| # | Question | Answer |
|---|---|---|
| C17 | Which of the four spread-lemma proofs is most formalisable in `nat`-only Coq? | **The counting proof — [ALWZ20] §2 as streamlined by Park–Pham, written out in Lovett PCMI §3.** Not Rao. See the analysis below. |

---

## Tier 1 — the spread layer

### [Ra20] Anup Rao, *Coding for sunflowers*, Discrete Analysis 2020:2

**Read in full: 8 of 8 rendered pages** (the Discrete Analysis version;
arXiv:1909.04774 is the same text). This is the source of the
repository's only axiom, and it had never been opened.

**The axiom, verbatim, p. 2:**

> Let `r(p, k)` denote the quantity `αp log(pk)`. We say that a sequence
> of sets `S₁, ..., S_ℓ ⊂ [n]` of size `k` is `r`-spread if for every
> non-empty set `Z ⊂ [n]`, the number of elements of the sequence that
> contain `Z` is at most `r^{k−|Z|}`. We prove that for an appropriate
> choice of `α`, the following lemma holds:
>
> **Lemma 2.** *If a sequence of more than `r(p,k)^k` sets of size `k` is
> `r(p,k)`-spread, then the sequence must contain `p` disjoint sets.*

Checked symbol by symbol against `ALWZ.Rao20_lemma2` and
`SpreadReduction.SpreadYieldsDisjoint`:

* `RaoSpread m F r := ∀ T, NoDup T → T ≠ [] → deg T F ≤ r^(m−|T|)` — matches
  "every non-empty `Z`", "at most `r^{k−|Z|}`", exactly. ✔
* `r ^ m < length F` — matches "more than `r(p,k)^k`". ✔ (Note [BCW21]
  states the same lemma with `≥`; the two differ by one and the
  repository takes the strictly weaker `>`.)
* `α p log(pk)` → `alpha * k * Nat.log2_up (S (k * n))` under the
  translation *Rao's `k` = our `n`*, *Rao's `p` = our `k`*. ✔
* `exists alpha, 1 <= alpha` against Rao's `α > 1`: weaker as an
  existential, so safe. ✔
* **`Distinct F` is an added hypothesis.** Rao states Lemma 2 for
  *sequences*; footnote 2, p. 2: *"Here we state the results for
  sequences of sets because some applications require the ability to
  reason about sequences that may repeat sets."* Adding a hypothesis
  assumes less. ✔ — but it was not listed among the recorded gaps.
* **The axiom quantifies over all `r ≥ threshold`. Rao does not.**
  This is the one respect in which the axiom said *more* than its
  source, and it was unrecorded. It is now discharged rather than
  argued: `ALWZ.fractional_form_gives_the_axiom_shape`.

**The open question, verbatim, p. 2** — this is register row A2, and it
settles `docs/roadmap.md` §5's "looked for and not found":

> As far as we know, it is possible that Lemma 2 holds even when
> `r(p,k) = O(p)`. Such a strengthening of Lemma 2 would imply the
> sunflower conjecture of Erdős and Rado.

**What the proof actually needs, p. 3–5.** The header of `coq/ALWZ.v`
called it *"elementary — injections between finite sets and binomial
estimates, no measure theory"*. That is withdrawn. §3 proves Lemma 2
from Lemma 4, over a **uniformly random partition** of `[n]` and a
uniformly random `W ⊆ [n]` of size at least `γn`; the engine is Lemma 5,
which is **Shannon's noiseless coding theorem** (p. 4), proved through
Kraft's inequality and the concavity of `log`. Real logarithms and
expectations are load-bearing on every page of the argument. Of the four
published proofs it is the *worst* fit for a `nat`-only development.

**Changes here:** `coq/ALWZ.v` header rewritten; two withdrawals
(the "at most" mis-citation, the "elementary" description); one new
theorem discharging the `∀ r` extension.

### [ALWZ20] Alweiss, Lovett, Wu, Zhang, *Improved bounds for the sunflower lemma*

**Read in full: 19 of 19 rendered pages** (arXiv:1908.08483v3, 31 Aug 2021 —
the Annals version, not the STOC one).

* **Definition 1.1, p. 1:** *"a `w`-set system if each set in `F` has
  size at most `w`"* — this is where the "at most" convention lives, and
  `coq/ALWZ.v` had attributed it to Rao.
* **Definition 1.10, p. 4** — confirms `docs/references.md` verbatim:
  *"We say that a `w`-set system `F` is `κ`-spread if `|F| ≥ κ^w` and
  `|F_T| ≤ κ^{−|T|}|F|` for all non-empty `T`"*, followed by *"The paper
  [16] calls these 'regular set systems', but we use the more
  descriptive term 'spread'."* ✔
* **The dichotomy, p. 4** — also confirmed verbatim. ✔
* **Theorem 1.4, p. 1:** *"For some constant `C`, any `w`-set system `F`
  of size `|F| ≥ (Cr³ log w log log w)^w` contains an `r`-sunflower."*
  `docs/references.md` said ALWZ *"establishes `f(n,k) ≤ (Ck log n)ⁿ`"*.
  **That is BCW21's bound, not ALWZ's.** Corrected.
* **§3, Lemma 3.1, pp. 11–12** — read in full, and it answers A2 in the
  negative direction the repository hoped for: the tightness example is
  built as a subfamily of `X₁ × ⋯ × X_w` (transversals, `|X_i| = log(w/c)`),
  and Claims 3.2/3.3 show it contains no `(1/2,1/2)`-robust sunflower.
  A transversal family with parts of size `m ≥ p` **does** contain `p`
  pairwise disjoint members. So it says nothing about the disjointness
  form. The `log` is proved necessary for **robust** sunflowers only.
* **§4.2 *Intersecting set systems*, p. 13, Theorem 4.2** — the finding
  that refutes B10a. Quoted in full in the register above.
* **§4, p. 12:** *"Bell, Chueluecha, and Warnke [4] observed that a small
  modification of the argument improves the bound in Theorem 1.4 further
  to `(Cr log(w))^w`."* ✔ — corroborates `coq/ALWZ.v`'s
  "what an improved spread lemma would buy" note.
* **The counting core, Lemma 2.8, p. 7**, is where the formalisable
  content is: an explicit encoding of "bad pairs" and its injectivity,
  *"From these four pieces of information one can uniquely reconstruct
  (W, Sᵢ)"*, then a binomial estimate. **Corollary 2.9 passes from
  fixed-size `W` to the product measure by a limiting argument.** That
  direction matters for `docs/roadmap.md` §1 — see C17.
* Final assembly (p. 10) uses **Janson's inequality**.

### [BCW21] Bell, Chueluecha, Warnke, *Note on sunflowers*, Discrete Math. 344 (2021)

**Read in full: 3 of 3 rendered pages.** The current peer-reviewed record.

> **Theorem 1.** *There is a constant `C ≥ 4` such that
> `Sun(p,k) ≤ (Cp log k)^k` for all integers `p, k ≥ 2`.* [p. 1]

> **Lemma 2.** *There is a constant `C ≥ 4` such that, setting
> `r(p,k) = Cp log k`, the following holds for all integers `p,k ≥ 2`.
> If a family `S` with `|S| ≥ r(p,k)^k` sets of size `k` is
> `r(p,k)`-spread, then `S` contains `p` disjoint sets.* [p. 1]

Also, p. 1, the framing of Erdős–Rado that everyone quotes:
*"In 1960, Erdős and Rado [4] proved that
`(p−1)^k < Sun(p,k) ≤ (p−1)^k k! + 1 = O((pk)^k)`."*

**Lemma 4, p. 3**, with *"Theorem 3 is essentially best possible with
respect to the `r`-spread assumption"*: the witness is again the
transversal family (`|S| = r^k` on `X = {1,…,rk}`), which contains `r`
pairwise disjoint sets. Second independent confirmation that the
tightness results do not touch the disjointness form.

### [Lovett] Shachar Lovett, *From sunflowers to thresholds*, PCMI 2025 lecture notes

**Read in full: 28 of 28 rendered pages.**
`https://www.ias.edu/sites/default/files/Shachar%20Lovett%20Lecture%20Notes%201.pdf`
(`docs/roadmap.md` §15.1 said 29pp; the version reachable in July 2026 is 28.)

Three quotations `docs/references.md` attributes to page 7, all
**verbatim confirmed on rendered page 7**:

> **Definition 2.5 (Spread family).** *Let `F` be a family of sets, and
> let `k > 1`. We say that `F` is `k`-spread if for every set `T`,
> `|F_T| ≤ |F|/k^{|T|}`.*

> Note that in the proof we only used the "structured" case where a
> single element belongs to many sets in `F`. But we also could have
> used two elements, or three elements, or any number of elements. This
> motivates the following definitions.

and **Lemma 2.2** proving `SF(n,r) ≤ n!(r−1)^n` with `k = (r−1)n`. So
`docs/roadmap.md` §14.5's correction — that `ρ` is the singleton clause
of spreadness — is confirmed at the primary source, on the cited page.
`Spread.Spread` **is** Definition 2.5, on the nose.

Two further things, both new here:

* **Lemma 2.6 (p. 8)** is `SpreadReduction.spread_reduction`, including
  the relativisation: *"Assume that for all `n' ≤ n`, every family of
  `n'`-sets which is `k`-spread contains an `r`-sunflower. Then
  `SF(n,r) < k^n`."* The repository's "relativised to all `m ≤ n`" is
  textbook, not an extension.
* **Lemma 2.9 (p. 8)** is the fractional disjointness statement: *"Let
  `F` be a family of `n`-sets which is `k`-spread for `k = cr log n`
  ... Then `F` contains `r` pairwise disjoint sets."* No size
  hypothesis — because `k`-spread already forces `|F| ≥ k^n`. This is
  the form the axiom should have been stated against, and
  `ALWZ.fractional_form_gives_the_axiom_shape` now bridges the two.

**§3 (pp. 11–15) is the counting proof, and it is the formalisation
target.** Claim 3.4's probability is literally a ratio of two
cardinalities, `|B| / (|F|·C(N,qN))`; the map `φ(S,V) = (Z, S′, M, S∖M)`
is decoded explicitly; the count is a binomial estimate and a geometric
sum. Nothing else in the four proofs is this close to `nat`.

§4 is Kahn–Kalai, §5 is monotone circuit lower bounds; both read, both
outside this repository's scope. Reference list read (pp. 27–28) and it
is where [Rao23]/[Tao20]/[Sto22] were found.

### [MNSZ22] Mossel, Niles-Weed, Sun, Zadik, *A second moment proof of the spread lemma*

**Read in full: 8 of 8 rendered pages** (arXiv:2209.11347).

Page 1 confirms `docs/references.md`'s enumeration of the four proofs.
Two things page 1 alone did not give:

* **The proof needs Radon–Nikodym derivatives, couplings and Hölder's
  inequality** (pp. 2–5). It is the *second* worst fit for `nat`-only
  Coq, after Rao.
* **Footnote 2, p. 6:** *"It was recently pointed out that the proof of
  [Tao20] has a gap, which has been corrected in [Hu21, Sto22]."*
  **One of the four proofs has a published gap.** This was not known
  here, and it removes Tao's argument from the candidate list unless the
  corrected version is used.

Also: `docs/references.md` lists the streamlining as "[Stoeckl] S.
Stoeckl". It is **M. Stoeckl**; the reference is
`https://mstoeckl.com/notes/research/sunflower_notes.html`, 2022.

### [FKNP19/21] Frankston, Kahn, Narayanan, Park, *Thresholds versus fractional expectation-thresholds*

**Read pp. 1–4 of 16** (arXiv:1910.13433v2). Enough to settle two things
the register needed and no more; §§3–8 were not read.

* **Its spread definition, (4) on p. 3**, is the fractional one, stated
  for hypergraphs *with repeats allowed*:
  `|H ∩ ⟨S⟩| ≤ κ^{−|S|}|H|` for all `S ⊆ X`, where `⟨S⟩ = {T : T ⊇ S}`.
  Same as `Spread.Spread` (which quantifies over `NoDup` lists, i.e. the
  same sets) and as Lovett's Definition 2.5. `ℓ`-bounded means *"each of
  its members has size at most `ℓ`"* — the ALWZ convention again, not
  Rao's.
* **Theorem 1.6, p. 3**, is the covering statement, and it is stated for
  a **fixed-size** random set: *"for any `ℓ`-bounded, `κ`-spread
  hypergraph `H` on `X`, a uniformly random `((Kκ^{−1} log ℓ)|X|)`-element
  subset of `X` belongs to `⟨H⟩` w.h.p."* Third independent confirmation
  that fixed size, not the product measure, is the primitive — see C17.
* p. 4: *"The heart of our argument, Lemma 3.1, is proved in Section 3;
  our approach here strengthens that of the recent breakthrough of
  Alweiss, Lovett, Wu and Zhang."*

### [Smooth] *A smoother notion of spread*, arXiv:2106.11882

**Not read.** Downloaded and rendered (12pp); budget went elsewhere.
Recorded as not read rather than "skimmed".

---

## Tier 2 — the history

### [ErRa60] Erdős and Rado, *Intersection theorems for systems of sets*, JLMS 35 (1960) 85–90

**Read in full: 6 of 6 rendered pages.** Reached via the Erdős archive at
`users.renyi.hu/~p_erdos/1960-04.pdf` — open, free, and it had never been
opened here either.

Four findings, and one of them corrects how this repository describes its
own foundational theorem.

1. **The paper is about *systems*, i.e. multisets.** p. 85: *"The system
   `Σ₀` is called a `(a, b)`-system if it consists of `a` (not
   necessarily distinct) sets of cardinal `b`."* Remark 3 on p. 86 gives
   `c = 12` at `a = b = 2` with the explicit witness
   `01, 01, 23, 23, 04, 04, 14, 14, 25, 25, 35, 35` — every pair
   doubled. That is why the headline constant is a factor `a` above the
   distinct-family one.

2. **Theorem III's constant is not `(k−1)ⁿ n!`.** p. 86:
   ```
   c = b! a^{b+1} (1 − 1/(2!a) − 2/(3!a²) − … − (b−1)/(b! a^{b−1}))
   ```
   and *"then every `(> c, ≤ b)`-system contains a `Δ(> a)`-system"*.

3. **The distinct-family bound, p. 90, is sharper than what everyone
   quotes.** Writing `φ(a,b)` for the distinct version (*"which satisfies
   `X_μ ≠ X_ν`"*), the paper derives
   ```
   φ(a,b) ≤ b! a^b (1 − 1/(2!a) − 2/(3!a²) − … − (b−1)/(b! a^{b−1}))
   ```
   `coq/ErdosRado.v` proves `UpperBound n k (S ((k−1)^n * fact n))` —
   correct, and **weaker than the 1960 paper's own bound** by the
   bracketed factor. `docs/references.md` said the paper *"proves
   `f(n,k) ≤ (k−1)ⁿ n! + 1`"*; that is the modern rounding, not the
   original. Corrected there.

4. **The modern textbook proof is Erdős and Rado's own**, and it is on
   p. 90: *"Let `N₀` be a maximal subset of `N` such that `X_μ X_ν = ∅`
   ... Then `|N₀| ≤ a`, since `X_ν (ν ∈ N₀)` is a `Δ`-system"*, then
   pigeonhole over `X* = ⋃ N₀`. At `a = 2` that is exactly
   `StarDefect.star_defect_bound`'s cover of `2b` points, and
   `SpreadReduction.elementary_spread_disjoint`'s at `a = k−1`. Both
   branches of `StarDefect.the_two_branches_of_the_dichotomy` are on
   page 90 of the 1960 paper. (Theorem I's proof, pp. 87–89, is the
   transfinite *Ramification Lemma* — that is the paper's main argument,
   and it is not what anyone formalises.)

**The conjecture, in the authors' own words, p. 86** — weaker phrasing
than "conjectured", and worth having exactly:

> It is not improbable that in (1) the factor `b!` can be replaced by
> `c₁^b`, for some absolute positive constant `c₁`. Such a sharpened
> version of III would have some applications in the theory of numbers,
> and in fact these applications originally gave rise to the present
> investigations.

**Theorem II, p. 86**, is the lower bound: *"For every `a, b` such that
`a, b ≥ 1` there exists a `(a^{b+1}, b)`-system which does not contain
any `Δ(> a)`-system"*, constructed on p. 89 as all maps `B → A`. This is
the transversal family that reappears as every tightness example in the
2020–2021 papers.

### [AHS72] — **UNREACHABLE**, and now definitively so

**The full citation, verified against Crossref rather than recalled:**

> H. L. Abbott, D. Hanson and N. Sauer, *Intersection theorems for
> systems of sets*. **Journal of Combinatorial Theory, Series A**,
> volume **12**, issue **3**, May **1972**, pages **381–389**.
> Publisher: Elsevier. **DOI: `10.1016/0097-3165(72)90103-3`.**

Two notes on the citation itself. [Kup25] p. 62 renders the journal as
"J. Combinatorial Theory 12 (1972)" without the series letter — JCT split
into Series A and Series B at volume 10 (1971), so volume 12 is Series A
and the two agree. And an earlier attempt in this session guessed the DOI
suffix as `-4`, which is why it returned 404; the real one ends `-3`.
**Guessed identifiers 404; looked-up ones do not.**

**It is closed access, and that is now established rather than assumed.**
OpenAlex's record for the DOI reports

```
  open_access: {is_oa: False, oa_status: "closed",
                oa_url: None, any_repository_has_fulltext: False}
```

— i.e. no open copy exists in any indexed repository, not merely none
that this session found. That is a stronger negative than a list of
failed fetches, and it is the right kind: a machine-readable answer from
a comprehensive index rather than an exhausted search.

Five attempts, all recorded:

1. `sciencedirect.com/science/article/pii/0097316572901034/pdf` → HTTP 403.
2. `doi.org/10.1016/0097-3165(72)90103-4` → HTTP 404 (DOI suffix guessed).
3. `core.ac.uk` search → HTTP 403.
4. Erdős archive (`users.renyi.hu/~p_erdos/`) — Erdős is not an author,
   and the archive index has no entry for it. Confirmed by grepping the
   full index for "Intersection theorem": the four hits are ER60, EKR61,
   ER69 II, EMR74 III.
5. `doi.org/10.1016/0097-3165(72)90103-3` with the **correct** DOI →
   resolves to the ScienceDirect landing page; the PDF endpoint returns
   HTTP 403.

**Elsevier paywall, no legitimate open copy found. Recorded as unread.**
Per `docs/roadmap.md` §15.2's own instruction: nothing further is built
on it.

What *is* now confirmed, from **rendered pages** of [Kup25] rather than
its arXiv HTML:

> The authors of [1] showed that `φ(2,s) = s(s+1)` for even `s` and
> `s² + (s−1)/2` for odd `s`. [Kup25, p. 6]

> Abbott, Hanson and Sauer also showed a lower bound
> `φ(k,3) ⩾ 10^{(k/2)−c log k}` with some positive constant `c`, which is
> exponentially better than `3^k` which follows from the construction
> above. They used a construction of a 3-uniform family of size 10 and
> with no `Δ(3)`-system, and then leveraged it to any uniformity using
> an iterated product construction, which gives a recursion
> `ψ(ab) ⩾ ψ(a)ψ(b)^a`, where `ψ(a)` is the size of their iterated
> construction of uniformity `a`. [Kup25, p. 6]

Both were previously recorded from extracted text; both survive
rendering unchanged. **One new fact:** the same survey, p. 5, says
*"Abbot, Hanson and Sauer [1] in 1972, and then Spencer [116] in 1977
improved upper bounds on `φ(k,s)`. The result of Spencer states that for
any fixed `s` and `ε > 0` there exists `C` such that
`φ(k,s) ≤ C k!(1+ε)^k`."* — so [AHS72] also improved the **upper**
bound, which this repository did not know, and **Spencer 1977** is a
reference the bibliography lacks entirely.

### [Kup25] Kupavskii, *Delta-system method: a survey*, arXiv:2508.20132

**Read in full: 66 of 66 rendered pages.** Previously two pages, and
before that only the arXiv HTML. It is the densest single source in the
corpus and it changes four register rows.

**Confirmations, all re-checked on the rendered page:**

* Definition (1.1), p. 5 — `φ(k,s)` has second argument one *below* the
  petal count. ✔
* p. 6, the two [AHS72] sentences, verbatim as recorded. ✔
* p. 6, **Observation 2**: *"We have `φ(a+b,s) ⩾ φ(a,s)φ(b,s)`"*, with
  proof — `coq/DirectSum.v`'s supermultiplicativity, published.
* p. 7, Tao's proof *"contained a mistake"*; Stoeckl's bound
  `(64s log k)^k`.

**Five things that were not known here.**

1. **A third name for a sunflower.** Footnote 6, p. 21: *"It is in this
   paper that `Δ(s)`-systems are called **`s`-stars**, a name that
   appears in the follow-up papers of Frankl and Füredi."* Every "not
   found" search in this repository has used "sunflower" or
   "Δ-system". Neither finds a Frankl–Füredi paper that says *star*.

2. **Spreadness is a tool in the Δ-system method itself.** §1.7, p. 49:
   *"In recent papers, Zakharov and the author [98] and then the author
   [95] developed the peeling-simplification procedure... A family `F` is
   `r`-spread for some `r > 1` if `|F(X)| < r^{−|X|}|F|` for any set `X`.
   We will see that **`r`-spread families in many ways behave like
   sunflowers with `r` petals, albeit they are much easier to find.**"*
   And p. 53: *"Zakharov and the author recently introduced a **spread
   approximation** method [98]."* Two research programmes built on the
   notion `Spread.Spread` formalises, neither of which this repository
   had heard of.

3. **`SpreadReduction.spread_reduction`'s conclusion is Observation 58.**
   p. 50: *"If `G ⊂ ([n] choose ℓ)` is such that there is no `X` such
   that `G(X)` is `r`-spread, then `|G| ≤ r^ℓ`."* — two lines, followed
   by *"This bound is already better than the bound coming from not
   containing a sunflower."* That is exactly what this repository proves
   as a theorem, stated as a passing observation.

4. **`g` is the leading constant of a Frankl–Füredi asymptotic.**
   **Theorem 37**, p. 35: for fixed `k, s` and `k ≥ 2ℓ+3`,
   `f(n,k,ℓ,s) = (φ(ℓ+1,s) + o(1))·C(n−ℓ−1, k−ℓ−1)`, where `f(n,k,ℓ,s)`
   is the Duke–Erdős forbidden-sunflower-with-a-fixed-core number. At
   `ℓ=1, s=2` the constant is `φ(2,2) = f(2,3) − 1 = 6`, which
   `coq/F23.v` **proves**. The repository's small exact values are not
   only curiosities; they are constants in a published asymptotic. Its
   Example 1 on the same page is a *substitution* of exactly the AHS
   shape, and Example 2 uses a partial Steiner system.

5. **The covering-number literature, under other names** — the answer to
   B12, quoted in the register above. §1.7 and §1.9.4 reach
   Erdős–Lovász, Füredi's *nucleus*, Frankl's *base*, Ahlswede–
   Khachatrian's *generating set*, and Frankl's recent analysis of
   *minimal covers*.

Three smaller things worth carrying:

* **p. 29, Theorem 29 (Frankl–Katona)** is proved by a containment
  bipartite graph, *"a Hall's condition in disguise"*, and a matching.
  `coq/HallCore.v`, `coq/KoenigHall.v` and `coq/Matching.v` are exactly
  that machinery, built for the uniformity-2 programme.
* **p. 55**: the largest `ℓ`-avoiding system is *"the independence number
  of the generalized Johnson graph `J(n,k,ℓ)`"* — roadmap M2's Johnson
  scheme, in this problem's own literature.
* **p. 10**: Deza's theorem on `|A ∩ B| = ℓ` families, with the
  **projective plane of order `k−1`** as the extremal example — an
  intersecting family, and the closest thing in the survey to the
  intersecting side of the sunflower question.

**Two citations resolved on the reference pages** (pp. 62–66):

* **[1]** *H. L. Abbott, D. Hanson, and N. Sauer, "Intersection theorems
  for systems of sets", J. Combinatorial Theory 12 (1972), 381–389.*
* **[75]** is **Lunjia Hu**, *Entropy Estimation via Two Chains:
  Streamlining the Proof of the Sunflower Lemma* (2021). So the body
  text's "Lu [75]" on p. 7 is a typo, and this repository's "L. Hu" was
  right. Recorded because a previous revision of `docs/references.md`
  flagged it as an unresolved discrepancy.
* **[116]** *J. Spencer, "Intersection theorems for systems of sets",
  Canadian Mathematical Bulletin 20 (1977), N2, 249–254*,
  doi:10.4153/CMB-1977-038-7. **Unreachable** — Cambridge Core, no open
  access.

### [EKR61], [ErRa69-II] — downloaded, not read

`users.renyi.hu/~p_erdos/1961-07.pdf` (8pp, Erdős–Ko–Rado) and
`1969-02.pdf` (13pp, *Intersection theorems for systems of sets II*) were
fetched and rendered. **Not read** this session. The second is the more
interesting for `ι`; it is the top of the next session's list.

---

## Tier 3 — the 2024→2026 sweep

**Method.** arXiv API, `sortBy=submittedDate`, three queries:
`all:sunflower AND cat:math.CO`, `all:"sunflower-free"`,
`abs:sunflower AND cat:cs.CC`, 100 results each, filtered to
`≥ 2024-06-01`. Thirty distinct hits. This is a sweep, not a list; it is
also not exhaustive over venues that do not post to arXiv.

The full sweep, so the next session does not repeat it:

```
2026-07-30  2607.28253  An improved range for the maximum critically t-intersecting hypergraphs
2026-07-01  2607.02589  Thresholds for the Frankl-Wang 3/7 conjecture on maximum-degree ratios
2026-06-29  2606.30593  A Polynomial Improvement of Naslund-Sawin Bound ... Triangular Tensors
2026-06-11  2606.13656  On the sunflower property and the galah property
2026-06-01  2606.02667  Erdos Rado Sunflower Theorem for Shifted Families            [read]
2026-05-12  2605.12232  On set-like sunflower-free families of subspaces over finite fields
2026-05-09  2605.08676  Moonflowers and efficient code sparsification
2026-04-23  2604.21855  Counting sunflowers with restricted matching number
2026-04-21  2604.19183  Counting sunflowers in hypergraphs with bounded matching number
2026-04-07  2604.05607  Forbidding Exactly One Hamming Distance
2026-02-04  2602.04610  Structured sunflowers and canonical Ramsey properties
2025-12-23  2512.20055  Harmonic LCM patterns and sunflower-free capacity
2025-11-26  2511.21659  Nearly Tight Lower Bounds for Relaxed LDCs via Robust Daisies
2025-11-21  2511.17142  Duke-Erdos forbidden sunflower: exact results, extremal structure
2025-10-21  2510.19037  Sunflower Bound with a Sub-Logarithmic Base                  [read]
2025-09-19  2509.16355  The Sunflower-Free Process
2025-09-18  2509.14790  The Story of Sunflowers  (Rao)                              [read]
2025-08-26  2508.20132  Delta-system method: a survey  (Kupavskii)                  [pp.5-6]
2025-07-27  2507.20381  Structured Sunflowers
2025-07-21  2507.16105  Monotone Circuit Complexity of Matching
2025-06-21  2506.17628  The characteristic polynomial of sunflowers
2025-05-06  2505.03671  The Erdos-Rado Sunflower Problem for Vector Spaces
2025-04-21  2504.15264  Sunflowers and Ramsey problems for restricted intersections
2025-01-16  2501.09545  Hardness of clique approximation for monotone circuits
2024-10-31  2410.23611  Focal-free uniform hypergraphs and codes
2024-10-08  2410.06156  Duke-Erdos forbidden sunflower: linear dependencies
2024-08-08  2408.04165  Sunflowers in set systems with small VC-dimension
2024-06-26  2406.18437  Towards odd-sunflowers: temperate families and lightnings
2024-06-19  2406.13402  When t-intersecting hypergraphs admit bounded c-strong colourings
```

**No lower-bound improvement anywhere in that list.** That is the
evidence for register row A5, and it is negative evidence, not proof.

### [Rao25] Anup Rao, *The Story of Sunflowers*, arXiv:2509.14790

**Read in full: 12 of 12 rendered pages.** A 2025 survey by the author
of the axiom's source, and it answers A2 a third time, on p. 3:

> The only difference between this bound and the conjecture of Erdős and
> Rado is the presence of the `log k` term. **This dependence is
> necessary for robust sunflowers**, as shown by [3], who found a family
> of `Ω(log k)^{k−√k}` sets that does not contain a `(1/2,1/2)`-robust
> sunflower. **Nevertheless, it is quite possible that the sunflower
> conjecture of Erdős and Rado holds in its original form.**

**§3 was read, and it is *not* the shortcut its abstract suggests.** The
abstract advertises *"a short elementary proof of the best known bounds
for the robust sunflower lemma"*, which looked like it might beat Lovett
§3 as a formalisation target. It does not. The proof (pp. 8–10) needs, in
addition to the counting:

* a **Chernoff bound** to fix the size of `A(γ)` (p. 9);
* **Azuma's inequality** for the `ℓ` rounds of sampling (p. 9);
* **Markov's inequality** and a geometric series (p. 10).

Lovett §3 needs Markov and a geometric series and nothing else.
**Recommendation unchanged: Lovett §3.** This is what "read it before
writing a line" is for — the alternative was named in `docs/roadmap.md`
§1 as worth ten minutes, and ten minutes is what it cost to rule out.

**But §3's outer structure is already in this repository, verbatim.**
p. 8: *"For `k > 1`, if there exists a set `Z` with `0 < |Z| < k`
contained in some `r^{k−|Z|}` sets of `F`, we apply induction on the
family of sets containing `Z` ... Otherwise, it must be that for every
non-empty set `Z`, the number of sets of the family containing `Z` is at
most `r^{k−|Z|}`."* That is `SpreadReduction.spread_reduction`'s
dichotomy — the `rao_witness` branch and the `RaoSpread` branch — with
`Spread.RaoSpread` as the "Otherwise". So the induction is done; only
the covering step is missing.

**Tier 4, and the only Tier-4 reading this session achieved.** §2 is
applications, and it is where the circuit-lower-bound and data-structure
connections live: §2.1 the `t ≳ log m / log log m` cell-probe bound
(Ramamoorthy–Rao), §2.2–2.3 Razborov's approximation method and
Alon–Boppana for `k`-CLIQUE, §2.4 perfect matching following
Cavalar–Göös–Riazanov–Sofronova–Sokolov, arXiv:2507.16105 (2025) — a
2025 paper this bibliography does not have. The mechanism, p. 5:
*"If `w` is large, and `S₁,…,S_w` forms a sunflower with core `C`, then
`⋁_j clique_{S_j}(G) ≤ clique_C(G)`"* — replacing a sunflower by its
core is the whole approximation step, and it is why a better sunflower
bound improves the circuit bound.

Two more references the bibliography lacks: **[Rao23]** *Sunflowers: from
soil to oil*, Bulletin of the AMS 60(1):29–38, 2023, by the same author;
and **[CGRSS25]** *Monotone Circuit Complexity of Matching*,
arXiv:2507.16105.

### Fukuyama, *Sunflower Bound with a Sub-Logarithmic Base*, arXiv:2510.19037v2

**Read in full: 8 of 8 rendered pages.** Theorem 1.1, p. 1:

> There exists `c ∈ ℝ_{>0}` such that for every `k, m ∈ ℤ_{>2}`, a family
> `F` of sets each of cardinality `m` includes a `k`-sunflower if
> `|F| ≥ (ck² ln m / ln ln m)^m`.

If correct this beats [BCW21]. **It is an unrefereed preprint**; no
journal publication is recorded, and the author's own project page
describes the proof as not yet stable. The same author's
arXiv:1809.10318 (cited by [ALWZ20] as [11]) made a comparable claim in
2018 and is likewise unpublished. **Recorded, not adopted.** The
repository's threshold table (`docs/roadmap.md` §12) does not change.

### Ahmadi and Norouzi, arXiv:2606.30593 (30 June 2026)

**Read p. 1 of 12.** Improves [NaSa17] from
`O(n^{1/2}(3/2^{2/3})^n)` to `O(n^{1/6}(3/2^{2/3})^n)` for sunflower-free
`F ⊆ 2^{[n]}`. The **base is unchanged**, so
`SliceRank.NaslundSawinBound` is unaffected in substance — but see the
correction to how the repository *states* [NaSa17], below.

### [NaSa17] Naslund and Sawin, *Upper bounds for sunflower-free sets*

**Read in full: 5 of 5 rendered pages** (arXiv:1606.09575).

**This entry contains a withdrawal of a withdrawal, and it is the
clearest lesson of the session.** After reading page 1 only, the register
recorded that `docs/references.md` misquoted the bound: the abstract says
`3n Σ_{k≤n/3} C(n,k)`, where the repository said `3(n+1)C^n`. Reading
pages 2–5 shows the repository was right and the correction was wrong.
**Theorem 3, rendered page 2:**

> `|F| ≤ 3(n+1) Σ_{k ≤ n/3} C(n,k)`, and `μ₃^S ≤ 3/2^{2/3} = 1.889881574…`

The abstract and the theorem disagree with each other about the
polynomial factor, and the theorem is the claim. And
`Σ_{k≤n/3} C(n,k) ≤ 2^{H(1/3)n} = (3/2^{2/3})^n` exactly, because
`H(1/3) = log₂3 − 2/3` — so `3(n+1)C^n` is a genuine upper bound, not a
sloppy paraphrase.

**Rule 3 said "nothing is quoted from an abstract". This session then
based a correction on one.** Page 1 is not the paper. [Mis26] has the
same disease — abstract "at least", introduction "more than" — so this
is not a one-off.

Two further things from the full read:

* **Theorem 8, p. 4**: `μ₃^S ≤ √(1+C)` where `C ≤ 2.7552` is the capset
  capacity (Ellenberg–Gijswijt), giving `1.938` — weaker than Theorem 3,
  and a clean statement of how the two capacities relate.
* **Theorem 5, p. 2**: for sunflower-free `A ⊂ (Z/DZ)^n`, `|A| ≤ c_D^n`
  with `c_D = (3/2^{2/3})(D−1)^{2/3}`. That is the [ASU12] Conjecture 4
  setting, and p. 2 notes the Erdős–Rado conjecture is equivalent to
  `c_D < D^{1−ε}` [ASU12, Thm 2.7].

### [Mis26] Mishra, *Erdős Rado Sunflower Theorem for Shifted Families*, arXiv:2606.02667v2

**Read in full: 12 of 12 rendered pages.** Version history checked: v1
1 Jun 2026, v2 8 Jun 2026, **no v3, not withdrawn**.

* p. 3, `f'` is defined with *"cardinality **more than** `m`"*. The
  repository's reading holds, and `coq/Compression.v`'s off-by-one
  convention is right. ✔
* But `docs/references.md` explained the discrepancy as *"an
  extracted-text summary, which had it as 'at least'"*. **Wrong reason.**
  The paper's own **abstract** says *"cardinality at least `m`"* while
  its **introduction** says *"cardinality more than `m`"*, for the same
  `f(k,s)`. The paper is internally inconsistent. Corrected.
* **Theorem 1, p. 3**, verbatim: `f'(k,s) ≤ s^{2k}` if `k ≤ s−1`, else
  `2f'(k−1,s)`. **Corollary 1, p. 7**: `f'(k,s) ≤ s^{2s−2}2^k`. ✔ Both
  as `docs/references.md` records them.
* Two statements are both labelled "Theorem 1" (p. 5 for `f`, p. 6 for
  `f'`), with different hypotheses. Noted so nobody re-derives the
  confusion.
* p. 2 confirms the record chain independently:
  *"The current best known Sunflower bound due to Bell, Chueluecha, and
  Warnke [BCW] is `(Cs log k)^k`."*

`coq/Compression.v`'s `f'(k,s) = C(k+s−2,k)` is consistent with the
paper's recursion (`C(k+s−2,k) ≤ 2·C(k+s−3,k−1)`), and is exact where
the paper gives only an upper bound. Unchanged.

---

## Zach Hunter's MathOverflow answer — read in full, and denser than its citation

`docs/references.md` has credited this to [FPPTZ24] for two sessions
without anyone seeing it, and this file was going to record it as
unreachable: `WebFetch` refuses mathoverflow.net in this environment.
**The StackExchange API is not blocked**, and
`api.stackexchange.com/2.3/answers/463150?site=mathoverflow&filter=withbody`
returns the body. That is the whole trick, and it is worth writing down
because the same route reaches any MathOverflow post.

**The question** — Dömötör Pálvölgyi (`domotorp`), 26 Jan 2024, MO 462924,
*"How many base elements can a sunflower-free system have?"*:

> But what can we say about the base set of a `t`-sunflower-free
> `k`-uniform family? ... I'm looking for an upper bound for the size of
> the union of the sets. The number of base elements is at most `k` times
> the number of the sets, but maybe there is a way to prove without using
> the Erdős-Rado conjecture that there can be at most `C_t^k` elements in
> the base set. This question first appeared in our recent preprint.

**The answer** — Zach Hunter, 30 Jan 2024, MO 463150, accepted, in full:

> As I mentioned in the comments, this is not an easier question. Indeed,
> one can start with a maximal `t`-sunflower-free collection in
> uniformity `k-1`, and then add a unique "dummy element" to each edge in
> this construction. Thus, your problem has a bound of `exp(O_t(k))` if
> and only if the original Erdos-Rado problem has a bound of
> `exp(O_t(k))`.
>
> Here's an attempt to propose a new question in the spirit you intended:
>
> > Let `H` be a `k`-uniform `t`-sunflower-free family. Is there some
> > vertex that is contained in at least `c_t^k |H|` of the edges (where
> > `c_t > 0` is some absolute constant)?
>
> EDIT: my question is also silly. If no element is contained by a
> `(1/tk)`-fraction of the edges from `H`, then we can greedily find `t`
> disjoint sets.

Three things follow, and only the first was known here.

1. **The equivalence is confirmed at source**, and it is one sentence.
   `IotaGround` and `SliceRank.GroundBounded` are a *linear* strengthening
   of a known-equivalent formulation, exactly as `docs/roadmap.md` §7.5
   records.

2. **The "EDIT" is `StarDefect.star_defect_bound`.** *"If no element is
   contained by a `(1/tk)`-fraction of the edges from `H`, then we can
   greedily find `t` disjoint sets"* is the Erdős–Rado dichotomy in one
   line, and it is what that file proves — with a slightly better
   constant: the repository gets `|F| ≤ 2b·deg(x)` at `t = 3`, a
   `1/(2b)`-fraction, against Hunter's `1/(3b)`. §14.5 already withdrew
   the novelty claim there against Lovett's Lemma 2.2; this is a second,
   independent, informal statement of it, from 2024.

3. **The question Hunter proposes and then withdraws is the weak form of
   `StarDefect.StarBounded`,** and the two are worth keeping apart.
   Hunter asks for a vertex of degree `>= c_t^k |H|` — an *exponentially
   small* fraction — and immediately notes the answer is trivially yes,
   because `1/(tk)` beats `c_t^k`. `StarBounded c` asks for degree
   `>= |H|/c` with `c` a **constant**, which is enormously stronger,
   settles the conjecture (`star_bounded_settles_k3`), and is *false* —
   `star_bounded_needs_c_at_least_five` forces `c >= 5` from data, and
   §14.2's `rho = b^(log_3 2)` rules out every constant. So the
   interesting question is neither of Hunter's: it is the *rate* at which
   the best fraction decays, which §14.3 identifies as the geometric mean
   of the chain.

## Formal-verification context — and the claim this refutes

### AFP: *The Sunflower Lemma of Erdős and Rado*, René Thiemann

**Read pp. 1–4 and 13–14 of 14 rendered pages** (pp. 5–12 are the
Isabelle proof script of the induction and were not read).
Isabelle/HOL, Archive of Formal Proofs, submitted **25 February 2021**.

> We formally define sunflowers and provide a formalization of the
> sunflower lemma of Erdős and Rado: whenever a set of size-`k`-sets has
> a larger cardinality than `(r − 1)^k · k!`, then it contains a
> sunflower of cardinality `r`. [p. 1]

That is `coq/ErdosRado.erdos_rado_upper_bound`, with the same bound and
the same strict-inequality convention, five years earlier, in a
different prover. The entry also proves two things this repository does
not (p. 14): `Erdos-Rado-sunflower-card-core` (cores of prescribed
cardinality) and `Erdos-Rado-sunflower-nonempty-core`.

**`docs/references.md`'s claim that this repository holds "the only
fully machine-checked formalisation of the Erdős–Rado 1960 upper bound"
is refuted.** Withdrawn there in the text, not silently edited.

The narrower claim — that there is no *Mathlib* or *Mathematical
Components* formalisation — was checked separately and appears to hold:
Mathlib has no `sunflower` definition, and
`google-deepmind/formal-conjectures` issue #2284 tracks the Erdős–Rado
sunflower conjecture as an open formalisation target. That is a
web-search result, not a rendered page, and is recorded as such.

---

## C17 — which proof to formalise, and what each needs

Four proofs, all now read or read far enough to cost them.

| Proof | Prerequisite | Verdict for `nat`-only Coq |
|---|---|---|
| **[ALWZ20] §2 / [FKNP21], as streamlined by Park–Pham and written out in Lovett §3** | Binomial coefficients; an explicit encoding and its injectivity; `C(N, qN+m) ≤ q^{−m}C(N,qN)`; a geometric sum. Rationals for `q`, or cleared denominators. | **Recommended.** Every "probability" is a ratio of two explicit finite cardinalities. Nothing else is needed. |
| **[Ra20]** | Shannon's noiseless coding theorem, Kraft's inequality, concavity of `log`, expectations over random partitions. | Worst fit. Needs real analysis this development does not have and does not want. |
| **[Tao20]** | Shannon entropy manipulations — **and the published proof has a gap** ([MNSZ22] fn. 2, p. 6), corrected only in [Hu21]/[Sto22]. | Excluded. |
| **[MNSZ22]** | Radon–Nikodym derivatives, couplings, Hölder. | Excluded. |
| *(checked and rejected)* **[Rao25] §3**, advertised as *"a short elementary proof"* | Chernoff (p. 9), Azuma (p. 9), Markov and a geometric series (p. 10), on top of the counting. | Not a shortcut. Lovett §3 needs Markov and a geometric series and nothing else. |

**The technical choice in `docs/roadmap.md` §1 was backwards, and this is
the session's most actionable finding.** §1 proposed stating the covering
step *for the product measure with `p = 1/2`*, so that "probability
becomes plain cardinality over the powerset, which `Spread.subsets`
already enumerates". Three things are wrong with that:

1. The proof needs `W` to be a **small** random set — `q ≈ 1/log n`, not
   `1/2`. At `p = 1/2` the product measure is plain cardinality; at
   `p = 1/log n` it is a weighted sum, which is strictly worse than the
   fixed-size version.
2. In the actual proofs the **fixed-size** version is the primitive.
   Lovett's Claim 3.4 computes `|B| / (|F|·C(N,qN))` — already a ratio of
   cardinalities, with no measure anywhere.
3. The product-measure statement is *derived* from the fixed-size one,
   by a limiting argument (Lovett p. 11: *"Take now `U′` of growing
   size"*) or by ALWZ's Corollary 2.9. Starting from the product measure
   means either redoing the encoding count in it, or formalising a limit.
   Surveys do sometimes *state* the conclusion in the product measure —
   [Kup25] Theorem 3, p. 7, is *"`W` is a `(βδ)`-random subset of `[n]`"*
   — but no published proof works there.

So Stage A should build **fixed-size subset enumeration and binomial
counting**, not powerset enumeration. `docs/roadmap.md` §1 is rewritten
accordingly.

---

## Downloaded, rendered, not read

Honest list. Each is one `pdftoppm` away from being read next session,
and none of them is claimed here.

```
  fknp.pdf                 16pp   read pp.1-4 only
  smoother_spread.pdf      12pp   A smoother notion of spread
  dukeerdos.pdf            30pp   arXiv 2511.17142
  sfprocess.pdf            37pp   arXiv 2509.16355, the sunflower-free process
  vecspaces.pdf             9pp   arXiv 2505.03671
  sfsubspaces.pdf           8pp   arXiv 2605.12232
  moonflowers.pdf          26pp   arXiv 2605.08676
  vcdim2025.pdf            25pp   arXiv 2501.13850
  fox_pach_suk.pdf         14pp   arXiv 2103.10497
  harmonic_lcm.pdf         19pp   arXiv 2512.20055
  near_sunflowers.pdf      11pp   Alon-Holzman, arXiv 2010.05992
  structured_canon.pdf     16pp   arXiv 2602.04610
  galah.pdf                21pp   arXiv 2606.13656
  naslund_improved.pdf     12pp   read p.1 only
  afp_sunflowers.pdf       14pp   read pp.1-4, 13-14 only
  ekr61.pdf                 8pp   Erdos-Ko-Rado 1961
  er69_ii.pdf              13pp   Erdos-Rado, Intersection theorems II
```

## Tier 4 — beyond the problem

### [ASU12] Alon, Shpilka, Umans, *On Sunflowers and Matrix Multiplication*

**Read pp. 1–5 and 8 of 16** (ECCC Report No. 67, 2011;
`eccc.weizmann.ac.il/report/2011/067`). The paper this repository has
been citing second-hand for the matrix-multiplication obstruction.

* **Theorem 1.1**, p. 2, is a third independent rendering of the bound
  `coq/ErdosRado.v` proves, with the same strict inequality: *"Let `F` be
  an arbitrary family of sets of size `s`... If `|F| > (k−1)^s · s!` then
  `F` contains a `k`-sunflower."*
* **Theorem 2.2 settles a discrepancy this file recorded.** *"There
  exists a constant `c` such that every family of `s`-sets of size at
  least `cs!·((log log log s)/(log log s))^s` contains a
  3-sunflower"* [Ko97]. That matches [Rao25] p. 2 exactly and shows
  [Kup25] p. 5's rendering `(log log k)²/(α log log k)` is garbled. The
  Kostochka entry in `docs/references.md` is fixed accordingly — still
  *inferred*, but now from two agreeing sources instead of two
  disagreeing ones.
* **Theorem 2.3**, p. 3, is the precise link to the *other* problem this
  bibliography keeps warning against mis-citing: the uniform conjecture
  with constant `c` implies the Erdős–Szemerédi conjecture with
  `ε = 1/4c`. One direction, with a two-paragraph proof on p. 4.
* **Theorem 2.6**, p. 5: the classical conjecture and the sunflower
  conjecture in `Z_D^n` are **equivalent**, `c_k ↔ e·b_k`. The
  `Conj. 1 ⇒ Conj. 3` direction encodes a vector `v` as the set
  `{p_1^{1+v_1}, …, p_n^{1+v_n}}` over the primes.
* The headline, p. 1: the Erdős–Rado conjecture *"implies a negative
  answer to the 'no three disjoint equivoluminous subsets' question of
  Coppersmith and Winograd"*, and their multicolored variant kills the
  strong-USP route of Cohn et al. Also p. 1: a [CKSU05] construction
  gives `(2.51…)^n` multicolored 3-sunflower-free sets, beating
  `(2.21…)^n` [Edel04] for ordinary 3-sunflower-free sets in `Z_3^n`.

### Also downloaded and rendered, not read

`blasiak_capset.pdf` (27pp, arXiv:1605.06702, Blasiak–Church–Cohn–
Grochow–Naslund–Sawin–Umans, the cap-set obstruction) and
`gmr_dnf.pdf` (27pp, arXiv:1205.3534, Gopalan–Meka–Reingold, DNF
sparsification).

**Coding theory (Schrijver's SDP, Gijswijt, the Terwilliger algebra of
the Johnson scheme), design-theoretic nonexistence (Fisher,
Bruck–Ryser–Chowla), flag algebras and Stanley–Reisner were not
attempted at all.** What was learned about the circuit side came from
[Rao25] §2 and Lovett §5, recorded above.

**One methodological note, because it cost a wasted read.** The first
attempt at [ASU12] fetched `arXiv:1109.6216` — an identifier recalled
from training rather than looked up. That is *Observation of the Perseus
galaxy cluster with the MAGIC telescopes*, an astrophysics conference
paper, and four of its pages were rendered and read before the mismatch
was obvious. [ASU12] is not on arXiv at all; it is an ECCC report.
**Identifiers get looked up, never recalled** — the same rule as
quotations, for the same reason.

---

### [FPPTZ24] Frankl, Pach, Pálvölgyi, *Odd-sunflowers* — pp. 1–3 re-read

Read in an earlier session; pp. 1–3 re-read here for two things.

* **p. 1 confirms the [DEGKM97] warning at its source**: *"They showed
  that `μ < 1.89`, while the best currently known lower bound
  `μ > 1.551`, follows from a construction of Deuber et al. [7]."* Both
  numbers are about `μ = lim f(n)^{1/n}` for subsets of `[n]` — the
  **Erdős–Szemerédi** quantity. Neither displaces [AHS72] on the uniform
  problem, exactly as `docs/references.md` says.
* **p. 2 is a third corroboration of [AHS72]'s mechanism**: *"The
  starting point of our approach is a 50 years old idea of Abbott,
  Hanson, and Sauer [2] concerning ordinary sunflowers: one can use
  'direct sums' to recursively produce larger constructions from smaller
  ones."*

And a fourth and fifth name for the object: p. 1, *"Erdős, Milner and
Rado [9] called a family of at least three sets a **weak sunflower** if
the intersection of any pair of them has the same size"*, plus
*"pseudo-sunflowers [13] and near-sunflowers [3]"*. With [Kup25]'s
**`s`-star**, that is five names in the corpus this repository has read,
and its searches have used two.

## The spread-approximation programme — read in full

### [KuZa22] Kupavskii and Zakharov, *Spread approximations for forbidden intersections problems*

**Read in full: 27 of 27 rendered pages** (arXiv:2203.13379v3, 1 Apr 2024;
to appear in Advances in Mathematics). Named in §18.3 as the highest-value
unread item, because it decides what `Spread.Spread` is *for*.

* **p. 1**, the method: *"a new approach to approximate families of sets,
  complementing the existing 'Delta-system method' and 'junta
  approximations method' ... based on the notion of `r`-spread families
  and builds on the recent breakthrough result of Alweiss, Lovett, Wu and
  Zhang for the Erdős–Rado 'Sunflower Conjecture'."*
* **p. 3**, why it matters here: their Ahlswede–Khachatrian theorem for
  permutations is proved without the previous authors' machinery — *"The
  proof is also much simpler and avoids the use of heavy machinery of the
  previous authors."* [Ku23] p. 2 names it: representation theory of
  symmetric groups, Hoffman–Delsarte bounds, Fourier analysis.
* **p. 5**, their spread definition is `Spread.Spread`: `μ` is `r`-spread
  if `μ({F : X ⊂ F}) ≤ r^{−|X|}`, with `μ_F(F) = 1/|F|` the natural
  measure of a family.
* **p. 5, equation (1)**, the sunflower bound *with an explicit constant*:
  a family of `k`-sets with `|F| > (C·ℓ·log₂(kℓ))^k` contains an
  `ℓ`-sunflower, `C = 2^10`.
* **pp. 9–12**, Lemma 10 is the peeling procedure, and **Lemma 14(iii)–(iv)
  applies the sunflower bound as a subroutine**: `T_i` is shown to have no
  sunflower with `q−i−t+2` petals, and (1) then bounds `|W_i| ≤
  (C₀ q log₂ q)^{q−i−t}` with `C₀ < 2^15`.
* **p. 12, Lemma 14(v)** uses `τ` explicitly: *"Recall that, for a family
  `F`, `τ(F)` is the size of the smallest set `Y` such that `Y ∩ F ≠ ∅`
  for each `F ∈ F`."* — register row B12's quantity, as a tool.
* **pp. 21, 24**: Kruskal–Katona, and Lemma 21 on independent sets in
  biregular bipartite graphs. More bipartite/matching machinery.

### [Ku23] Kupavskii, *Erdős–Ko–Rado type results for partitions via spread approximations*

**Read pp. 1–2 and 5–8 of 22** (arXiv:2309.00097v3, 12 Nov 2025). Read
because its abstract says it is the entry point: *"As a byproduct, this
makes the present paper a self-contained presentation of the spread
approximation technique for `t`-intersecting problems."*

Its §3 base layer is three statements this repository already has:

* **Observation 11**, p. 6: *"Given `r > 1` and a family `F ⊂ 2^{[n]}`,
  let `X` be an inclusion-maximal set that satisfies
  `|F(X)| ≥ r^{−|X|}|F|`. Then `F(X)` is `r`-spread as a family in
  `2^{[n]\X}`."* — `Spread.rao_witness` plus `Spread.link`, with
  maximality doing the work.
* **Observation 12**, p. 7: *"If for some `α > 1` and `F ⊂ C([n],k)` we
  have `|F| > α^k` then `F` contains an `α`-spread subfamily of the form
  `F(X)` for some set `X` of size strictly smaller than `k`."* — that is
  `SpreadReduction.spread_reduction`'s dichotomy, proved in two
  sentences, followed by *"this observation together with Theorem 10
  implies bound (1)."*
* **Theorem 13**, p. 7, is the peeling procedure; of the next one, p. 6
  says *"Theorem 14 alone can be seen as a strengthening of one of the
  important parts of the Delta-system method."*

**Not formalisable as it stands** — `p`-random subsets, expectations,
Markov, real-valued `τ, ε, θ`. What is formalisable is the base layer,
which is already here, plus the ALWZ input, which is §1's campaign.

## Tier 4 — where it stops

### [Schrijver05] *New code upper bounds from the Terwilliger algebra and semidefinite programming*

**Read pp. 1–2 of 8.** IEEE Trans. Inform. Theory 51:2859–2866,
doi 10.1109/tit.2005.851748; **green OA** at
`ir.cwi.nl/pub/14098/14098B.pdf`, found via OpenAlex after two guessed
URLs 404'd.

The method is block-diagonalising the non-commutative **Terwilliger
algebra** of the Hamming cube — a C\*-algebra, `dim A_n = C(n+3,3)`,
blocks `B_k` of order `n−2k+1` with multiplicity `C(n,k) − C(n,k−1)` —
and then semidefinite programming. **Roadmap M2 is not viable for this
development**: complex matrices, positive semidefiniteness and a
numerical SDP solver, none of them `nat`. The Johnson-scheme connection
[Kup25] p. 55 points at is real; it is on the far side of that stack.

### Not read

Flag algebras (Razborov 2007, J. Symbolic Logic 72(4):1239–1282,
doi 10.2178/jsl/1203350785 — closed, and the author's copy is behind a
TLS failure this environment cannot resolve), design-theoretic
nonexistence, Stanley–Reisner. The covering-number primaries
(Erdős–Lovász 1975, Frankl 1978 doi 10.1016/0097-3165(78)90003-1,
Füredi 1983 doi 10.1016/0012-365x(83)90081-x, Ahlswede–Khachatrian 1997)
are all **index-confirmed closed** by OpenAlex, so they are unreachable
rather than unsearched.

### Five wrong identifiers, and the procedure that caught four of them

Four Tier-4 arXiv IDs were recalled rather than looked up. They fetched a
PDE paper, *What Scalars Should We Use?*, a condensed-matter paper on
heat conduction, and a lattice-QCD paper on kaon masses. A fifth, for
[ASU12], fetched an astrophysics paper on the Perseus cluster — and that
one cost four rendered pages, because it was read before being checked.

**Rendering page 1 and confirming the title before reading is now the
rule.** It caught four of the five for the price of one page each. The
correct citations, from Crossref, are in `docs/roadmap.md` §19.7.

## The corpus is now pinned

The papers vanish with the container, and this session lost time
re-fetching what the previous one had already found. `docs/papers/` is
the fix: 29 records, each with the SHA-256 of the exact bytes that were
rendered and read, the page count verified with `pdfinfo`, the source
URL, and the retrieval date. `docs/papers/fetch.sh` rebuilds the corpus
and **fails on a hash mismatch**, so a paper revised upstream cannot be
quoted as though it were the version that was read.

Fourteen PDFs are stored. The rest are not ours to store — the arXiv
non-exclusive licence grants arXiv distribution rights and not
third-party redistribution, and the 1960/1961/1969 journal scans and the
PCMI notes are in copyright or carry no stated licence. The
`redistributable` flag in `manifest.json` is read from the licence each
publisher states, fetched from arXiv's OAI-PMH interface, which reports
it. `docs/papers/pdf/.gitignore` is a whitelist generated from that flag,
so rebuilding the full corpus locally cannot turn into a copyright
problem in a later commit. `ATTRIBUTION.md` carries the per-file
attribution CC BY requires.

## What could not be read, and why

| Source | Reason |
|---|---|
| [AHS72], JCTA 12 (1972) 381–389 | Elsevier paywall; four routes tried (see above). No legitimate open copy. |
| [BaKh09], Discrete Math. 309 (2009) 4176–4180 | Paywalled; unchanged from earlier sessions. |
| [ChHa76], JCTB 20 (1976) 128–138 | Not attempted this session. |
| Handbook of Combinatorial Designs | Not open access. **No longer needed**: the `2-(6,3,2)` uniqueness is now verified by exhaustion in `rust/tests/iota_structure.rs`. |
| Spencer 1977, Canad. Math. Bull. 20, 249–254 | Cambridge Core, no open access. Full citation now known from [Kup25] p. 66; doi:10.4153/CMB-1977-038-7. |
| [Rao23], Bull. AMS 60(1):29–38 | Newly discovered via [Mis26]; not attempted. |
| [CGRSS25], arXiv:2507.16105 | Newly discovered via [Rao25] §2.4; not attempted. |
| [ES78], JCTA 24(3):308–313 | The primary source of the *other* (bounded-ground-set) problem this bibliography keeps warning against mis-citing without ever naming; not attempted. |
