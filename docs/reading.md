# Reading log

What was actually read, page by page, and what it changed here.

This file exists because five sessions of machine-checked work were built
on a literature base that had never been opened. `docs/roadmap.md` §15
put the problem plainly: *"the repository's single axiom comes from an
eight-page open-access paper that nobody here has opened."* This session opened it, and thirty-four other papers, plus the
MathOverflow answer this repository had been citing without reading.
**Twelve papers were read cover to cover** — [Ra20] 8pp, [ALWZ20] 19pp,
[BCW21] 3pp, [Lovett] 28pp, [MNSZ22] 8pp, [ErRa60] 6pp, [Mis26] 12pp,
[Rao25] 12pp, [Fuk25] 8pp, [NaSa17] 5pp, [Kup25] **66pp** (the survey of
the method this problem belongs to) and [KuZa22] **27pp** — plus
Hunter's answer in full and seven more in part.

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
>
> **And rule 2 is weaker still than that, because extracted text is not
> in the same alphabet as the mathematics.** Rendering
> `kupavskii_survey.pdf` p. 49 and extracting it give different documents.
> `pdftotext` returns `Δ(𝑘 𝑟 )-system` where the page reads `Δ(k^r)-system`,
> and the codepoints are
>
> ```
>   Δ  U+0394   GREEK CAPITAL LETTER DELTA
>   𝑘  U+1D458  MATHEMATICAL ITALIC SMALL K      <- not ASCII 'k'
>   𝑟  U+1D45F  MATHEMATICAL ITALIC SMALL R      <- not ASCII 'r'
> ```
>
> so `grep "Delta(k^r)"` returns 0 and `grep "B(k)"` returns 0 on a page
> that contains both. The superscript has become a space; every italic
> variable has become a *different character*. **A search for a formula,
> a condition, a variable name or an inequality cannot be run on extracted
> text at all** — not unreliably, but structurally: the characters are not
> there to be matched. `pdftotext` locates **prose words in ASCII** and
> nothing else. For anything with mathematics in it, the only search is
> `pdftoppm` and reading every page.

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
| B9 | `ι(b)` (max *intersecting* sunflower-free family) is unnamed | **Not found under three vocabularies — sunflower, `Δ`-system, `s`-star — and the `[63]`/`[54]` chase is now COMPLETE. Still NOT EXHAUSTIVE.** The row's earlier caveat is discharged; its "not exhaustive" is not. | Not in [Kup25] (read in full, 66pp), [Ra20] (8pp), [ALWZ20] (19pp), [Lovett] (28pp), [Rao25] (12pp). **The caveat that opened this row is now chased.** [Kup25] fn. 6, p. 21 records that *"it is in this paper that `Δ(s)`-systems are called **`s`-stars**, a name that appears in the follow-up papers of Frankl and Füredi."* The two papers it names are [Kup25] `[63]` = Füredi, *On finite set-systems whose every intersection is a kernel of a star*, Disc. Math. 47 (1983) 129–132, and `[54]` = Frankl–Füredi, *Forbidding just one intersection*, JCTA 39 (1985) 160–176 — **both reference-list entries confirmed here by rendering [Kup25] pp. 63–64**. A commissioned session (N+15) then rendered and read both papers in full, 4/4 and 17/17 pages: [Fü83] p. 129 defines *"a `Δ`-system … or a `t`-star"* and proves a structural theorem; [FF85] p. 163 defines *"a strong `Δ`-system or an `s`-star"* and uses stars as a proof tool. **Neither names an intersecting sunflower-free extremal function.** **And the third vocabulary has a trap — see rule 33:** in [FT85] (Füredi–Tuza, *Hypergraphs without a large star*, Disc. Math. 55 (1985) 317–321, 5/5 rendered) a *"`t`-star"* is a **different object** — `t` sets each with a private point — not a `Δ`-system. Same word, same author, adjacent years. Still unfetched, so still not exhaustive: Chung 1983 ([Kup25] `[17]`, the origin of "`s`-star") and Chung–Frankl 1987 (`[19]`). |
| B10 | The sandwich `2ι(b) ≤ g(b) ≤ 2b·ι(b)`, and the `k=3` equivalence | **Not found — and the negative now stands on the RIGHT KIND of evidence.** The rule-18 objection is discharged: session N+15 rendered 136 pages and read 96 as images, no text extraction at any point, and the chain is on none of them. Still **NOT EXHAUSTIVE**. | Same corpus, plus the nine sources of the N+15 rendered pass. Specifically: [Kup25] pp. 5–7 (the `φ(k,s)`/AHS pages) carry `φ(k,3) ⩾ 10^{k/2 − c log k}` and Observation 2 `φ(a+b,s) ⩾ φ(a,s)φ(b,s)` — **no intersecting-side function and no two-sided chain**; §1.7 pp. 47–53 none; [Fü83], [FF85], [FT85], [Fü80], [EL75], [KM17] none. **The nearest published relative, and it is close enough to name:** [EL75] p. 612 Theorem 7, `r!(e−1) ≤ M(r) ≤ r^r`, where `M(r)` is the maximum number of edges of a 3-chromatic `r`-uniform *clique* — that is, an intersecting family with `τ = r` — and p. 623 §4 states the same bounds for *"`r`-uniform cliques which cannot be covered by less than `r` points"*. So an intersecting extremal function **is** bounded on both sides in print; the hypothesis is `τ`, not sunflower-freeness, and no unrestricted sunflower-free function stands beside it. Corpus still not searched: [AHS72] (unreachable, see below), Abbott–Hanson 1974/1977, Kostochka's `Δ`-system survey. But see B10a — the *ingredients* are all published. |
| B10a | "the intersecting side has never been pointed at" | **REFUTED** | [ALWZ20] §4.2, titled *Intersecting set systems*, Theorem 4.2 p. 13: *"If F is an intersecting w-uniform set system, and for all T, \|F_T\| ≤ κ^{−\|T\|}\|F\|, then κ = O(log w)."* Different hypothesis from `ι` (spread, not sunflower-free), but the claim as written is false. Withdrawn in `coq/IotaRate.v`; the elementary version is now `IotaRate.intersecting_not_spread_above_uniformity`. |
| B10b | Theorem 4.2 is independent of the spread lemma, so it could give the modern bound at `k=3` without the axiom | **REFUTED, and the target it supported is closed** | The *proof* is on the same page as the statement, four lines below, and had never been read. [ALWZ20] p. 13 introduces it with *"We note the following corollary of Theorem 2.5:"* and proves it in full by *"If `F` is intersecting then it is not `(1/2, 1/2)`-satisfying (apply Lemma 1.6 for `r = 2`). Thus by the improvement of Theorem 2.5 from [19], it cannot be `(C log w)`-spread for a large enough constant `C`."* Theorem 2.5 **is** the spread lemma and [19] is Rao, i.e. `ALWZ.Rao20_lemma2`. Formalising 4.2 would consume the axiom, not demote it. Independently, the chain it was to feed is arithmetically worse than Erdős–Rado — see `docs/roadmap.md` §21.2 and `coq/IntersectingSpread.v`. Rule 6: page 1 is not the paper, and neither is the statement of a theorem on it.|
| B11 | The cone `g(b−1) ≤ ι(b)` is folklore | **Technique found; exact statement still not found** | Hunter's answer uses the same move — *"start with a maximal `t`-sunflower-free collection in uniformity `k−1`, and then add a unique 'dummy element' to each edge"* — in exactly this context. His dummies are *distinct per edge* (which grows the ground set); the repository adds *one shared* fresh point to every member (which makes the family intersecting). Same idea, different construction, different conclusion. No novelty was claimed and none is now. |
| B12 | `τ(substitute(G,H)) = τ(G)τ(H)`, and the maximality of the AHS families | **Split verdict, and the halves now go opposite ways. The OPERATION is FOUND, published in 1975. The IDENTITY is still not found, now on rendered evidence rather than on a broken extractor.** | [Kup25] read in full; §1.7 *Approaches to constructing bases* is this material under names this repository did not search for — **base**, **nucleus**, **generating set**, **crosscut**, **minimal cover**. p. 52: *"the produced sets ... give exactly the family of **minimal covers** for the sets in `F`. These are the bases of the type used by Frankl in [44]. In a recent paper of Frankl [52], the family of minimal covers is efficiently analyzed in order to bound the maximal diversity of an intersecting family."* — and the construction is *"essentially due to Erdős and Lovász [39]"*. **Session N+15 followed `[39]` to the source and the operation is there verbatim.** [EL75] p. 620, construction (d), rendered: *"Let `H` be a 3-chromatic `r`-uniform clique, `V(H) = {1, …, n}`. Let `H₁, …, Hₙ` be 3-chromatic `ρ`-uniform cliques, `V(Hᵢ) ∩ V(Hⱼ) = ∅`. Define `H* = {E_{i₁} ∪ … ∪ E_{iᵣ} : Eᵢ ∈ Hᵢ, {i₁, …, iᵣ} ∈ H}`. Then `H*` is a `(ρr)`-uniform 3-chromatic clique."* That is `substitute` — `coq/Substitution.v` — and the paper records that it preserves intersecting-and-not-2-colourable. **What is multiplied there is the SIZE, not `τ`:** p. 621, proof of Theorem 6, *"`|H^{(k+1)}| = 7^{3^k} · |H^{(k)}|`, whence `|H^{(k)}| = 7^{(3^k−1)/2}`"* — iterated substitution with the Fano plane, the same shape as AHS's `10^{b/2}` with a 7-set base. The paper's `τ` statements are p. 621 (the `r^r` upper bound uses only *"that `H` is an `r`-uniform clique which cannot be covered by less than `r` points"*) and p. 623 §4; **no line states `τ(H*)` in terms of `τ(H)` and `τ(Hᵢ)`**, and `τ(H*) = ρr` is implied only through 3-chromaticity, never written. [Fü80] (*Maximal intersecting families of finite sets*, JCTA 28 (1980) 282–289, 8/8 rendered) is the follow-up on maximal intersecting families with `τ = k`: Proposition 3 gives `|H| ≤ k^r` with equality *"only in the case described in the statement"* — a maximality statement for a `τ`-extremal family, but for the Erdős–Lovász problem, not for AHS sunflower-free families. **So: cite [EL75] for the operation. The identity and the AHS maximality remain not found.** See also the [52] mis-citation recorded in session N+15. |
| B13 | `ρ` multiplicativity, and the AHS spreadness profile `κ = b^{log₃2}` | **Not found — and, like B10, the negative now rests on rendered pages rather than on extraction.** Still **NOT EXHAUSTIVE**. | Not in [ALWZ20] §3 (read), not in [Kup25] (read in full). Session N+15 re-rendered the two regions that could hold it. [Kup25] §1.7 p. 49, rendered: *"A family `F` is `r`-spread for some `r > 1` if `|F(X)| < r^{−|X|}|F|` for any set `X`. We will see that `r`-spread families in many ways behave like sunflowers with `r` petals, albeit they are much easier to find."* — spread is a **tool** here, via Kupavskii–Zakharov **peeling-simplification** and **spread approximation**. pp. 49–53 contain **no spreadness computed for any explicit construction and no product rule**; pp. 5–7 (the AHS pages) contain no spreadness statement at all. **The exponent `log₃ 2` appears on no rendered page.** The object the profile describes *is* in print — [EL75] p. 621's iterated 3-fold substitution `|H^{(k)}| = 7^{(3^k−1)/2}` on `3^k`-uniform families — but no degree or spreadness statistic is computed for it there. Corpus not re-rendered: ALWZ20 §3, Rao 2020, Lovett's notes, Kupavskii–Zakharov 2022 — all previously extraction-read only, so rule 18 still stands over that part. |
| B14 | Zach Hunter's ground-set equivalence, credited to MathOverflow | **FOUND AND READ IN FULL** | `mathoverflow.net/a/463150`, 30 Jan 2024, answering domotorp's question 462924. Retrieved verbatim through the StackExchange API after `WebFetch` was blocked for the site. Quoted in full below; it confirms the equivalence *and* contains two further things this repository has. |
| B15 | Prescribed-symmetry / Kramer–Mesner applied to sunflower-free families | **Not found** | Nothing in the 2024–2026 arXiv sweep, nothing in [Kup25] pp. 5–6. Not exhaustive over design-theory venues. |
| B16 | `ι(3)=10` is the unique simple 2-(6,3,2) design | **VERIFIED — by exhaustion, not by citation** | The Handbook of Combinatorial Designs is not open access, so the uniqueness claim could not be read. It does not need to be: there are only `C(20,10) = 184756` ways to choose ten triples from the twenty on six points. Enumerated — exactly **12** are simple 2-(6,3,2) designs, and all 12 form a **single** isomorphism class under `Sym(6)`. `720/12 = 60` re-derives `\|Aut\|` independently of `structure::automorphisms`, and agrees with it. `rust/tests/iota_structure.rs::the_two_six_three_two_design_is_unique_and_that_is_checked_not_cited`. |
| B19 | `HM(m,r)` — the Hilton–Milner family thinned to a grid so that it is Rao(`r`)-spread — and `¬ StarExtremalAt m m` at every `m` | **Not found in [Kup25], now on a COMPLETE rendered pass — 66 of 66 pages. Not found anywhere else either, but nowhere else has been searched properly.** The first version of this row was a `pdftotext` word-grep and was withdrawn within the hour (rule 18): the claim is a *condition*, `deg T ≤ r^(m−|T|)`, and conditions do not survive text extraction. Redone by rendering every page of the survey — log in `docs/papers/kup25-rendered-pass.md` — no page poses or uses an extremal problem for *intersecting* families under an *absolute, level-wise* cap. The three neighbouring corners are occupied; see B19d and B19g. | The *underlying object is classical, and that is now verified rather than assumed*. [FHHZ17] (Frankl–Han–Huang–Zhao, *A degree version of the Hilton–Milner theorem*, arXiv:1703.03896v2), **p. 1 rendered and read**, defines it verbatim: `HM_{n,k}` *"consists of a `k`-set `S` and all `k`-subsets of `[n]` containing a fixed element `x ∉ S` and at least one element of `S`."* `HM(m,r)` is exactly that family with the star part thinned to a transversal grid. What is not found is the thinning, or any extremal problem posed under a **level-wise** cap. See the search description below. |
| B19a | §24.13's claim that the neighbouring literature caps *one* degree statistic rather than every level | **Confirmed — from a rendered page rather than from assertion** | Same page. [FHHZ17] p. 1: *"Let `Δ(F) := max_x d_F(x)` and `δ(F) := min_x d_F(x)` denote the maximum and minimum degree of `F`, respectively. There were extremal problems in set theory that considered the maximum or minimum degree of families satisfying certain properties. For example, Frankl [7] extended the Hilton–Milner theorem by giving sharp upper bounds on the size of intersecting families with certain maximum degree."* One statistic, capped once. Rao's condition caps `deg T ≤ r^(m−|T|)` at every `|T|` simultaneously and geometrically, which is a different hypothesis — as §24.13 said and could not then cite. |
| B19b | The word "spread" in this literature means what it means here | **REFUTED twice over** | A web search for spread intersecting families returns the **fractional** notion — a family is `r`-spread when the maximum `s`-degree is at most `r^(−s)·|F|` — which is `Spread.Spread` in this development, *not* `Spread.RaoSpread`. `Spread.RaoSpread_Spread` relates them in one direction only, and the absolute form is the stronger hypothesis once a family exceeds `r^m`. A literature search on "spread" that does not disambiguate returns the wrong object. And the notion is *also* studied under a name containing neither word — see B19c. |
| B19c | A **level-wise, geometric** cap on the degrees of a family is not a studied notion | **REFUTED. It is studied, it is named, and the name contains neither "spread" nor "degree".** | [Kup25] p. 53, **rendered and read**: *"We say that a family `F ⊂ A` is `τ`-homogeneous with respect to `A`, if for any set `X` we have `|F(X)|/|F| ≤ τ^|X| · |A(X)|/|A|`. ... then it transforms into `μ(F(X)) ≤ τ^|X| μ(F)`."* Attributed to Zakharov and the author [98], alongside the *spread approximation* method, with a footnote recording a notation clash with Füredi's `τ`-homogeneous. This is a cap at **every** level, **geometric in `|X|`** — the shape of Rao's condition, generalised to an arbitrary ambient family `A`. With `A = binom([n],k)` it is the fractional condition (`Spread.Spread`) rather than the absolute one (`Spread.RaoSpread`), so it is not the same hypothesis; but §24.13's framing — that the neighbouring literature caps *one* statistic and a level-wise cap is a different kind of object — is **too strong as written**. What remains not found is what B19d says: the **extremal question** under the absolute condition together with an intersecting hypothesis. *The absolute condition itself is published and is in this corpus* — this row used to claim otherwise and was contradicted by the RaoSpread transcription check below and by [BCW21]'s own definition, *"a family `S` of `k`-element sets is called `r`-spread if there are at most `r^{k−\|T\|}` sets of `S` that contain any non-empty set `T`"*. Corrected session N+11; see the note at the end of this file. |
| B19d | Where this development's hypothesis sits, now that the rendered pass has read the neighbours | **A 2×2, and only one corner is unoccupied** | Two axes: **relative** (`deg ≤ c·|F|`) vs **absolute** (`deg ≤ r^(m−|T|)`), and **one level** vs **every level**. [Kup25] p. 20, rendered: Frankl [44] *"studies the families in which no element is contained in more than a `c`-fraction of sets"* — relative, level 1. p. 53: `τ`-homogeneous — relative, every level. p. 46, Jiang–Longbrake's quantitative Füredi (Thm 52), rendered: the subfamily it produces satisfies *"for every `J = A ∩ B` ... and every `x ∈ [n] \ J` we have `|F*(J ∪ {x})| ≤ (1/s)|F*(J)|`"*, with a matching lower bound — relative, every level, **two-sided**, and phrased exactly as Rao's is, as a decay by a factor per added point. The unoccupied corner is **absolute at every level under an intersecting hypothesis**, which is `Spread.RaoSpread` and the setting of `I(m,r)`. §24.13's "the neighbouring literature caps one statistic" is right about Frankl and wrong as a general characterisation: the axis separating this work from the literature is relative-vs-absolute, not one-level-vs-all-levels. |
| B19e | `SpreadReduction.spread_reduction`'s recursion is peculiar to this development | **It has a published counterpart, one setting over** | [Kup25] p. 50, rendered, Observation 58: *"If `G ⊂ binom([n],ℓ)` is such that there is no `X` such that `G(X)` is `r`-spread, then `|G| ≤ r^ℓ`"* — proved by taking an inclusion-maximal `X` violating spreadness, so that `G(X)` is spread by maximality. That is the same argument as this repository's reduction (find a violating `T`, pass to the link, recurse, conclude `|F| ≤ r^m`), in the fractional setting rather than the absolute one. No novelty was ever claimed for `spread_reduction`; this records where its counterpart is. |
| B19f | §24.13 dates the degree-condition line to "Frankl 1987" | **Two earlier sources, both 1978, and one of them is titled the question** | [Kup25] reference list, rendered. p. 63, [44]: *P. Frankl, "On intersecting families of finite sets", J. Combin. Theory Ser. A 24 (1978), 146–161* — the paper p. 20 attributes the `c`-fraction max-degree condition to, so that condition is Frankl **1978**. p. 64, [62]: *Z. Füredi, "**Erdős–Ko–Rado type theorems with upper bounds on the maximum degree**", Colloquia Math. Soc. J. Bolyai 25, Szeged, 1978, pp. 177–207* — the closest-titled paper found anywhere, and nine years earlier than the attribution §24.13 carries. Neither is in this corpus. Both are the first targets of any continuation of the B19 search, together with p. 65's [89] *Kostochka–Mubayi, "The structure of large intersecting families", PAMS 145 (2016)* and [96] *Kupavskii–Noskov (2025), arXiv:2410.06156*, on the Duke–Erdős corner. **Session N+15 closed two of the four targets and neither is the missing corner.** [KM17] (Kostochka–Mubayi, *The structure of large intersecting families*, arXiv:1602.01391) read 11/11 rendered — see B19f-KM. [KN24] (Kupavskii–Noskov, arXiv:2410.06156) read pp. 1–8 of 61 — see B19f-KN. The two that remain are Füredi 1978 `[62]` and Frankl 1978 `[44]`; Füredi 1978 was separately obtained and refuted at rows A15/A15a (`docs/papers/furedi78-rendered-pass.md`, 31/31 pages), so **`[44]` is the only one of the four still owed.** |
| B19g | The absolute-one-level corner of B19d's 2×2 is empty | **REFUTED — it is the Duke–Erdős function, and the corpus already holds the paper** | [Kup25] p. 57, rendered, §1.9.3: `f(n,k,ℓ,s)` is the largest `k`-uniform family with no `Δ(s)`-system of kernel size `ℓ`, which the survey states for `k=3, ℓ=2` as *"no pair of elements is contained in `s` triples"* — that is `deg T < s` for every `\|T\| = ℓ`, an **absolute cap at one level**. Quoted values: `f(n,3,2,s) ~ (1/6)sn²`; `f(n,k,ℓ,s) = Θ_k(s^(ℓ+1)n^(k−ℓ−1))` for `k ≥ 2ℓ+2` (Bradač–Bucić–Sudakov). So Rao's condition is the **simultaneous, geometric** version of Duke–Erdős's single-level cap. **With one precision, found on p. 34 and worth the correction:** `f(n,k,ℓ,s)` forbids a `Δ(s)`-*system* with kernel of size `ℓ`, and a sunflower needs **pairwise disjoint petals**, so that condition is strictly *weaker* than `deg T < s` for `|T| = ℓ` — except at `ℓ = k−1`, where the petals are singletons and disjointness is automatic. p. 57's phrasing is exactly that case (`k=3, ℓ=2`). So Duke–Erdős occupies the corner **exactly at `ℓ = k−1`** and only approximately below it. `dukeerdos.pdf` has been in the corpus throughout and was never connected to `I(m,r)`. |
| B19f-KM | Whether [KM17]'s `B*(H)` layers impose sunflower-freeness as a hypothesis, or derive it | **CONFIRMED BY RENDERING, both exponents exactly as previously extracted — and it is a DERIVED structural decomposition, not an imposed hypothesis. A23's verdict stands.** | [KM17] p. 5, rendered: *"Define `B*(H)` to be the set of `T ⊂ V(H)` such that (i) `0 < |T| < r`, and (ii) `T` is the core of an `(r+1)^{|T|}`-sunflower in `H`."* Then `B′(H)` = inclusion-minimal members, `B″(H)` = edges containing no member of `B*(H)`, `B(H) = B′ ∪ B″`, `B_i` = members of size `i`. p. 6, rendered: *"Claim. `B_i` contains no `(r+1)^{i−1}`-sunflower."* with a half-page proof, then *"Applying the Claim and Lemma 11 yields `|B_i| < f((r+1)^{i−1}, i)` for all `i > 1`."* The **only** hypotheses on `H` (p. 5) are *"intersecting `r`-graph with `τ(H) ≥ 2` and `|H| > hm″(n,r)`"*, and the paper attributes the machinery: *"The following crucial claim proved by Frankl can be found in Lemma 1 in [6, 8]"* — Frankl's `Δ`-system base construction, applied with petal count `r+1` chosen by the authors. **So it is a theorem *about* intersecting families that *produces* a sunflower-free base, not a theorem *bounding* intersecting families *assumed* sunflower-free with prescribed `τ`.** It does not replace the `ι(4,11)` computation. Note the degree-type condition is **relative** (`n` large, `|H| ~ (r−2)·C(n, r−2)`), stated at **one** level at a time but for **every** `i` — Rao's shape in the fractional setting, which is B19d's *relative / every level* corner again. |
| B19f-KN | Where [KN24] sits in B19d's 2×2, from the primary source rather than from the survey | **Absolute, one level — B19g confirmed from the primary.** Read pp. 1–8 of 61. | p. 1, abstract, rendered: the Duke–Erdős problem *"determine the maximum size of an `n`-vertex `k`-uniform hypergraph without a sunflower with `s` petals and a kernel of size `ℓ`"* — the extremal function `f(n,k,ℓ,s)`, an **absolute** cap (`< s` petals on a kernel of size exactly `ℓ`) at a **single** level `ℓ`. Main results pp. 2–4: exact `f(n,k,ℓ,s)` for `n ≥ n₀(k,s)` in several `(k,ℓ)` ranges plus extremal structure, via the `Δ`-system method with spread approximations. **No intersecting hypothesis and no cap at every level.** B19g reached this corner through [Kup25] p. 57; this reaches it through the paper. |

### Tier C — the four proofs, and the formalisation decision

| # | Question | Answer |
|---|---|---|
| C17 | Which of the four spread-lemma proofs is most formalisable in `nat`-only Coq? | **The counting proof — [ALWZ20] §2 as streamlined by Park–Pham, written out in Lovett PCMI §3.** Not Rao. See the analysis below. |
| C18 | Does `r*(m,3)` track `⌈g(m)^{1/m}⌉`? | **Tight at both known points; recorded as a hint, not a result** | `spread_reduction` gives `g(m) ≤ r^m`, so `r*(m,3) ≥ ⌈g(m)^{1/m}⌉` is a theorem (`IotaRate.spread_threshold_bounds_g`). At `m=2`: `g(2)=6`, `⌈2.449⌉=3`, measured `r*=3`. At `m=3`: `g(3)≥20`, `⌈2.714⌉=3`, measured `r*=3`. Falsifiable now — `r*(3,3)=3` forces `g(3) ≤ 27`, against the known `20 ≤ g(3) ≤ 48`. See `docs/roadmap.md` §18.2. |

---

## The B19 search, and why it was not a search

The first version of this section reported a negative. It was withdrawn
within the hour, and the reason is worth more than the row.

**What was done.** All 16 PDFs in `docs/papers/pdf`, page by page,
located with `pdftotext` on `hilton`, `milner`, `diversity`,
`maximal degree`, `maximum degree`, `non-trivial intersecting` — each word
separately, because the rule 2 box records that this corpus breaks
hyphenated phrases across lines. Three files hit; two of the hit pages
(`vcdim2025.pdf` p. 3, `kupavskii_survey.pdf` p. 59) were rendered and
read. Two web queries. One primary paper, [FHHZ17], downloaded, rendered
and read at p. 1.

**Why that is not a search for this claim.** Every term in the list above
is an English word. The claim is not: it is the *condition*
`deg T ≤ r^(m−|T|)`. A paper that poses exactly this extremal problem
would state it as displayed mathematics, and displayed mathematics does
not survive extraction — `pdftotext` returns `Δ(𝑘 𝑟 )-system` for
`Δ(k^r)-system`, with the superscript flattened to a space and every
italic variable replaced by a *different Unicode character* (`𝑘` is
U+1D458, not `k`). `grep "B(k)"` returns 0 on a page containing `B^(k)`.
So the locator was blind to precisely the thing being looked for, and a
paper could state the condition on every page and still register zero
hits.

The word list would find a paper that *talks about* Hilton–Milner or
degree conditions in prose. It cannot find a paper that *writes down* a
level-wise cap. Those are different searches and only the first was run.

> **Rule 18. `pdftotext` locates prose words in ASCII, and nothing else.
> A claim about a formula, a condition, an inequality or a variable can
> only be searched by rendering every page and reading it.** Rule 2 said
> extraction cannot establish absence because it breaks lines. The deeper
> reason is that it does not preserve the alphabet: mathematical italics
> are a different Unicode block from Latin letters, and superscripts are
> whitespace. A grep over extracted text is not a weak search for
> mathematics — it is not a search for mathematics.

**What this costs elsewhere.** B10, B12 and B13 are negatives about a
sandwich inequality, a multiplicativity identity and a spreadness
exponent. All three are formulas, all three were searched the same way,
and all three are now flagged in the register as unsupported on the same
grounds. None is *refuted*; each is simply not evidenced.

**What was actually established, and it survives.** The positive half of
B19 needs no search: [FHHZ17] p. 1 was **rendered and read**, and defines
`HM_{n,k}` verbatim, so the classical object underlying `HM(m,r)` is
confirmed rather than assumed. B19a and B19b likewise rest on rendered
pages. Only the *absence* claim is withdrawn.

### The rendered pass, completed

Redone the only way that counts: `pdftoppm` at 130–150 dpi, pages looked
at one at a time, asking whether the page poses or uses a **level-wise**
cap on the degrees of a family. **[Kup25] is now complete — all 66 pages
— logged in `docs/papers/kup25-rendered-pass.md`.** Also read: [FHHZ17]
p. 1, `vcdim2025.pdf` p. 3.

**Six pages in, the negative collapsed.** [Kup25] p. 53 — a page the
*earlier* grep had already listed as a hit and which was then never
rendered — defines exactly the missing notion:

> *"We say that a family `F ⊂ A` is `τ`-homogeneous with respect to `A`,
> if for any set `X` we have `|F(X)|/|F| ≤ τ^|X| · |A(X)|/|A|`."*

A cap at every level, geometric in `|X|`. That is the shape of Rao's
condition, generalised to an arbitrary ambient family, introduced by
Zakharov and Kupavskii alongside spread approximation. It is B19c, and it
means §24.13's "the neighbouring literature caps one statistic" is too
strong as written — B19a's quotation is accurate about *Frankl's* line but
was never the whole picture.

The same page is worth reading twice for a second reason. It appears in a
run of neighbouring notions this repository has been circling without
names: **diversity** of an intersecting family (p. 52, Frankl [52],
bounded via minimal covers) is the closest published relative of `I₂`, the
largest *non-star* intersecting family.

**Two failures produced this, and they compound.** The word-grep could not
see a formula (rule 18). And of the pages it *did* flag, only some were
rendered — pp. 18, 52, 53, 64, 65 of the survey were located and skipped,
and p. 53 is the one that mattered. Locating and not reading is the same
error as not locating, with the excuse removed.

**Finished, and what it came to.** All 66 pages. No page poses or uses an
extremal problem for *intersecting* families under an *absolute,
level-wise* cap. What the pass did produce is the map in B19d and B19g:
the three neighbouring corners are occupied, each now cited from a
rendered page — Frankl 1978 (relative, level 1, p. 20), `τ`-homogeneous
and Jiang–Longbrake (relative, every level, pp. 53 and 46), Duke–Erdős
(absolute, one level, exactly at `ℓ = k−1`, pp. 57 and 34). And the
closest-titled paper anywhere, Füredi 1978, is named in the reference
list and is **not in this corpus** (B19f).

**What is still not read.** All 15 other corpus PDFs in full, and
everything outside the corpus except [FHHZ17] p. 1. No MathSciNet, no
zbMATH. Füredi 1978 and Frankl 1978 not obtained. So the negative is now
a complete pass over *one* survey — a far better negative than the grep
it replaced, and still a negative about one paper.


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

Six attempts, all recorded:

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
6. The ScienceDirect `pdfft` download route, with a **browser
   user-agent** rather than the default — the one variable the earlier
   five had not changed. HTTP 403 for both the article page and the
   download. Tried in the session N+15 commissioned pass, from a
   different container and a different network path, which also rules
   out this container's proxy as the cause.

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

**Used, August 2026 (session N+4).** The Spencer sentence above was
recorded last session as "a reference the bibliography lacks entirely" and
left there. It has now been *applied*: `coq/PureLink.v` proves
`g(b) <= b(g(b-1) + iota(b-1))`, hence `g(b) <= (3/2) b g(b-1)` against
Erdős–Rado's `2b g(b-1)`, and Spencer's `C k!(1+ε)^k` for **every** `ε`
subsumes that outright. Since the survey also says (p. 5, four lines above)
that `φ(k,s)` is attained on sets of size exactly `k`, `φ(k,2) = g(k)` and
the comparison is direct. So the new recursion is asymptotically not new,
and it was checked before the claim was written rather than after —
`roadmap.md` §20.3.

What the survey does *not* contain is any exact value of `φ(3,2)`;
searching the rendered text for `φ(3`, "exact value" and "is known" returns
only unrelated hits about extremal numbers for paths and cycles. So the
finite values — `g(3) <= 27`, `f(3,3) <= 28` — are new to this development
and of unknown status against [AHS72] and [Sp77], both index-confirmed
closed.

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
the fix: 36 records, each with the SHA-256 of the exact bytes that were
rendered and read, the page count verified with `pdfinfo`, the source
URL, and the retrieval date. `docs/papers/fetch.sh` rebuilds the corpus
and **fails on a hash mismatch**, so a paper revised upstream cannot be
quoted as though it were the version that was read.

Sixteen PDFs are stored. The rest are not ours to store — the arXiv
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
| [AHS72], JCTA 12 (1972) 381–389 | Elsevier paywall; **six** routes tried (see above), the sixth from a different container and network path in session N+15. No legitimate open copy. |
| [BaKh09], Discrete Math. 309 (2009) 4176–4180 | Paywalled; unchanged from earlier sessions. |
| [ChHa76], JCTB 20 (1976) 128–138 | Not attempted this session. |
| Handbook of Combinatorial Designs | Not open access. **No longer needed**: the `2-(6,3,2)` uniqueness is now verified by exhaustion in `rust/tests/iota_structure.rs`. |
| Spencer 1977, Canad. Math. Bull. 20, 249–254 | Cambridge Core, no open access. Full citation now known from [Kup25] p. 66; doi:10.4153/CMB-1977-038-7. |
| [Rao23], Bull. AMS 60(1):29–38 | Newly discovered via [Mis26]; not attempted. |
| [CGRSS25], arXiv:2507.16105 | Newly discovered via [Rao25] §2.4; not attempted. |
| [ES78], JCTA 24(3):308–313 | The primary source of the *other* (bounded-ground-set) problem this bibliography keeps warning against mis-citing without ever naming; not attempted. |

---

## An internal citation that ran backwards

Not a source claim, but it belongs in the register for the same reason
the source claims do: it was quoted three times in this repository's own
planning documents, and it is the wrong way round.

**Claim as quoted:** `r*(3,3) = 3`, because `g(3) <= 26` forces it
(attributed to `docs/roadmap.md` §3.6 and §20.5).

**What the theorem says.** `IotaRate.flat_threshold_at_three_forces_g_three_at_most_27`
is

```coq
  SpreadYieldsDisjoint 3 3 3 -> GAtMost 3 27
```

— `r*(3,3) = 3` implies `g(3) <= 27`, an implication whose *hypothesis*
is the thing in question. §20.5 says so in its own words: proving
`g(3) <= 27` "**removed** the decision rather than making it — the
experiment cannot refute `r*(3,3) = 3` however it comes out."

**What §3.6's search establishes.** Its grid reaches ground 9 at
uniformity 3, and its own text says that is "ground sets that provably
cannot contain a counterexample plus nothing beyond". That is now exact:
`rstar::min_ground` computes the counting floor
`ceil(m(r^m + 1)/r^(m-1))`, and at `(m,r) = (3,3)` it is **10**. So
grounds 6 through 9 are settled by one division, `counting_settles_the_small_ground_sets`
settles them with zero search nodes, and the measured content of §3.6's
uniformity-3 rows is empty. Ground 10 is open and neither the SAT
encoding (90 minutes) nor the depth-first search reached a verdict.

`r*(3,3)` is in `[3, 6]`: below by the refutation at `r = 2`, above by
`SpreadThreshold.r_star_three_at_most_six`. It is not 3 as far as this
repository knows, and never was.

**The rule this adds.** Rule 3 asks for a page number and a quotation
before a claim about a *source* goes in. The same applies to a claim
about a theorem in this development: **quote the statement, and check
which side of the arrow the claim is on.** Both §18.2 and §20.5 state
the implication correctly; only the summary table inverted it, and a
summary table is exactly where nobody looks for the arrow.

---

## What re-reading the development changed, session N+7

Three entries, all about statements *in this repository* rather than in
the literature — which is where the last three sessions' corrections have
also come from.

### The first open term of `r*(m,3)` is m = 3, and the brief pointed at 4

The session brief aimed its top priority at `r*(4,3)` and described the
lower half of that interval as "the highest-information experiment
available". §22.2's table, written by the previous session, says
otherwise: `r*(1,3) = 2` and `r*(2,3) = 3` are exact, and **`r*(3,3)` is
the first term that is not**. The question the brief wants asked at
`m = 4` — is the sequence bounded, or still growing? — is available one
uniformity down, where the object sought has 28 members rather than 82
and the ground set starts at 10 points rather than 13.

Nothing in the brief is wrong about *why* the question matters. What was
wrong was where to ask it, and the table that says so was already in the
repository. **Read the development's own status table before accepting a
brief's choice of target.**

### `iota(4,8) = 24`, and a test written against 23

The differential test for the parallel search was first written with
target 24 at `(b, g) = (4, 8)` in the belief that this was above the
maximum, so that both routines would return an exhaustive negative and
their node counts would have to agree exactly. They did not agree, and
the first two hypotheses — a double-pop bug, then a race — were wrong
about the cause even though the first was a real bug found on the way.

The actual cause: §23.3's own table records the *control* (unrestricted
pool) at `b = 4`, `g = 8` as **24**, so 24 is reached, the search stops
at the first success, and how much of the space was explored before that
depends on how many workers were racing. A thread-dependent node count
there is correct behaviour.

The lesson is about what a differential test may assert. Node-count
determinism is a property of **exhaustive negatives** only; asserting it
for a reachable target asserts that a parallel search is not parallel.
The test now says so in its own name.

**The rule this adds.** Before pinning a search's node count, establish
which side of the threshold the target is on — and take the value from
the repository's measured table, not from a guess about what the maximum
"should" be.

### `g(3) ≤ 26` is not proved, and the brief quoted it as a fact

The session brief tabulates `f(3,3) ∈ [21,27]`, which reads as
`20 ≤ g(3) ≤ 26`. The lower half is right — `Intersecting.lower_bound_3_3_20`
is a 20-member family. The upper half is not proved. What `IotaRate.v`
says in its own text (line 378, and again at 436) is

> "The development only knows `20 <= g(3) <= 48`."

48 is Erdős–Rado. The 27 in the brief traces to
`Sharp.AHSOptimal implies f(3,3) <= 32` and to
`IotaRate.flat_threshold_at_three_forces_g_three_at_most_27`, whose
hypothesis is `r*(3,3) = 3` — the very thing this session was trying to
decide. Quoting it as an unconditional bound assumes the answer.

This is the third consecutive session in which a number carried forward
in a brief did not survive being checked against the module that proves
it, and the pattern is the same each time: the number is real, but it
sits on the far side of an implication whose hypothesis is open. **When
a brief quotes a bound, find the theorem and read what is to the left of
the arrow.**

### An extremal question that appears not to have been asked

`I(m,r)` — the largest `m`-uniform intersecting family satisfying Rao's
condition `deg T ≤ r^(m-|T|)` at every level — is what the spread
threshold turns on, and §24.13 is the first time this repository has
treated it as a question in its own right rather than as a term to be
bounded.

What is in the literature is the neighbouring problem: intersecting
families under a bound on the **maximum degree**. Frankl's 1987 "Erdős–Ko–Rado
theorem with conditions on the maximal degree" is the origin; Huang–Zhao,
Frankl–Han–Huang–Zhao and Kupavskii continue it. Those all cap one
statistic. Rao's condition caps every level at once, and the caps are
geometric in `|T|` — which is a different object, and the one that
actually appears when the spread reduction is unwound.

Two things suggest it is worth posing rather than merely bounding.

* The extremal family **changes** with `r`, and the crossover is at
  exactly `r = m+1` in both cases where it can be computed: below it a
  small design wins (the triangle at `m = 2`, `C([5],3)` at `m = 3`),
  from it on the star does. A degree-capped EKR problem whose answer
  switches families at a specific parameter is the kind of question that
  usually has a clean answer.
* `r = m+1` is not an arbitrary place to look: it is where the two-way
  split of §24.2 stops being able to close at all, since at `r = m` the
  cover term alone already equals `r^m`.

**No claim of novelty is being made beyond "I did not find it".** The
search here was over what this repository has read (`docs/references.md`)
plus the degree-condition line above; it was not a systematic literature
search, and the neighbouring results are close enough that a specialist
may well recognise this. What is recorded is the question, its exact
consequence (`I(m,m+1) ≤ (m+1)^(m-1)` implies `r*(m,3) ≤ m+1`), and the
two data points.

---

## What re-reading the development changed, session N+8

Nothing new was read from outside. What changed is a *use* of what was
already read, and one claim about the development itself that did not
survive being checked.

### The `tau = 3` hypothesis was false, and no reading was needed to see it

`TwoCover.TauThreeAtMost K` — §24.12's stand-in for Frankl's theorem —
quantified over families with `Uniform 3 G` and no distinctness
condition. `Uniform` constrains the points inside each member, not the
members; `length G` counts members with multiplicity; every other
hypothesis in the statement is preserved by repeating a family. The Fano
plane, taken three times, is a counterexample at `K = 16` and the same
construction refutes every `K`.

This is not a reading error. Every source involved states the theorem for
*families of distinct sets*, and [Ra20]'s entry above already records
`Distinct F` as an added hypothesis in `ALWZ.Rao20_lemma2` — noticed
there, and not carried across to the file that restated a classical
theorem by hand a session later. **The rule this adds is about
transcription, not about sources:**

> **11. When a classical theorem is entered as a hypothesis rather than
> proved, check that the hypothesis is *true*, not only that it is
> faithful to the source's words.** A conditional theorem with a false
> antecedent passes `Print Assumptions`, passes the statement baseline,
> and passes its own mutations. Nothing in the gate stack asks the
> question.

### Priority 0, answered from the entries already here

The brief asks what the published spread lemmas give for `r*(m,3)` under
this repository's `RaoSpread`, and says nobody has done it cleanly. Two
entries above answer it and neither needed re-reading.

* **Upper.** `ALWZ.Rao20_lemma2` is Rao's Lemma 2 in exactly the
  `SpreadYieldsDisjoint` shape, checked symbol by symbol in the [Ra20]
  entry, and `Spread.RaoSpread_Spread` shows the repository's absolute
  condition is the stronger one — so the published lemma applies
  verbatim and `r*(m,3) = O(log m)` is published. §22.7 had this. The
  consequence for §24.13 is new and is recorded in `docs/roadmap.md`
  §25.5: **`r*(m,3) <= m+1` is asymptotically weaker than what is
  known**, and the split's value is exact small values, not growth.
* **Lower.** Entry A2 above: [Ra20, p. 2] says it is open whether Lemma 2
  holds with `r(p,k) = O(p)` — which in this repository's notation is
  precisely "`r*(m,3)` is bounded in `m`" — and that such a strengthening
  would imply the sunflower conjecture. The same entry records that the
  tightness examples that exist ([ALWZ20] Lemma 3.1, [BCW21] Lemma 4) are
  for the **robust/covering** form, not the disjointness form. So there
  is **no published lower bound on `r*(m,3)` at all**.

That last point is the one worth carrying forward, and it corrects the
tone of §22.7 without contradicting its arithmetic. Finitely many terms
cannot separate bounded from `log m` — true. But on the lower side the
literature is empty, so `r*(2,3) = 3` and `r*(9,3) >= 4` are, as far as
this corpus goes, the only concrete values written down anywhere, and the
first term that moved past 4 would be the first evidence of unboundedness
in the form Rao asks about.

### What did not survive from the incoming brief

* *"§22.7 says the repo's `Θ(m)` bound is asymptotically behind the
  published `O(k log m)` ... nobody has done this cleanly."* — the check
  had been done: it is `docs/reading.md`'s [Ra20] entry plus
  `Spread.RaoSpread_Spread`, and §22.7 states the conclusion. What was
  genuinely missing is the *consequence* for the `m+1` framing, now §25.5.
* *"`r*(3,3) ≤ 4` conditional on `TauThreeAtMost 16`, a hypothesis, not
  an axiom"* — true as stated and useless in fact, because the hypothesis
  is false. See above.
* *"`I(3,3) = 10` is now measured, so the decomposition against a maximum
  matching gives `|F_A|, |F_B| <= 10` and `|F_AB| >= 8`"* — the
  arithmetic is right but it does not constrain the search as much as the
  brief suggests: the split bound `|F| <= 3·3² + I(3,3)` gives `|F| <= 37`
  against the 28 a witness needs, so nothing is excluded. The
  decomposition is a better *search order*, not a decision procedure.
* *"`9 >= 4` §18.2, via `g(9) >= 3^9`"*, quoted in the brief's sequence
  table alongside the proved rows — **conditional**.
  `IotaRate.substitution_would_refute_the_flat_threshold_at_nine` takes
  `LowerBound 9 3 (3^9 + 317)` as a hypothesis and its own header says
  the Abbott–Hanson–Sauer substitution it rests on *"is not formalised
  here"*. `docs/roadmap.md` §22.2's table lists the row flat, with no
  caveat, next to rows that are theorems; both that table and `STATUS.md`
  are corrected in this session's commit. It is the one number in the
  brief that failed rule 9.

### A derived route, stated as "the gap", that had never been measured

§26.4 reduced `r*(4,3) ≤ 5` to one four-family inequality —
`Σ_x |A_x| ≤ 48` for four pairwise cross-intersecting 3-uniform
Rao(5)-spread families — and called it "the gap, stated exactly". Nothing
in the gate stack objects: it is prose, it names no theorem, and the
arithmetic that produced it (`125 − (1 + 16 + 60) = 48`) is correct.

It is also false. Four copies of one 25-member star give `Σ = 100`; four
copies of a 16-member non-star give `Σ = 64` with no common point, which
is what the covering-number hypothesis actually forces. Both were found by
writing the families down and evaluating them, which is what rule 1 of
this session's brief — measure the quantity, do not just bound it — asks
for, and the one thing the derivation had not done.

> **Rule 12. A reduction is a claim, and a claim about a quantity gets
> measured before it gets called a gap.** The arithmetic of a
> decomposition can be right while the inequality it produces is false,
> because a decomposition bounds each layer *separately* and the layers
> need not be simultaneously full. "Necessary if the other layers are
> full" is a different statement from "necessary", and only the second
> one earns the word *exactly*.

`docs/roadmap.md` §26.4 now carries the retraction inline, and §27 records
what the measurement bought instead: a 65-member witness that pins the
open constant into `[65, 125]`, and two general transfer lemmas the
counterexample turned out to be an instance of.

The rule then had to be applied to this session's own work, twice.
§27.6's upper bound on `I₂(3,5)` was first written down as a few lines of
arithmetic and labelled, in bold, *not Coq*. It is now
`CrossRefined.nonstar_three_bound`, the label is gone, and the difference
between the two states is the only thing that decides whether the sketch
was right — which is the whole content of rule 12.

And the sketch was *not quite* right: it gave 17 where the truth is 16.
Formalising it exposed that the loss was entirely in the pair bound at
uniformity two, which the exhaustive search had been saying was `2r+1`
against a proved `2r+2` for two sessions. Proving that one
(`cross_pair_two_exact`) closed `I₂(3,5) = 16` exactly. The measurement
had been sitting in `rust/tests/cross_intersecting.rs` the whole time,
correctly labelled as a measurement; what was missing was anyone asking
it to become a theorem.

The same thing happened twice more, one level down each time. The first
proof of `cross_pair_two_exact` carried `r ≥ 4`, and §27.6 recorded —
correctly — that the threshold was an artefact of the case analysis and
that the measured maximum at `r = 3` was still `2r+1`. Asked to close
`r = 3`, the first thing to do was measure the case the analysis was
losing on: the neither-pointed configurations, where the greedy tree gives
`4 + 4 = 8`. The exhaustive maximum there is **6**, not 8, and seeing that
is what named the two missing lemmas (`triangle_bound`,
`disjoint_squeeze`).

That measurement also said `r = 2` is different in kind: the statement
`2r+1` is *false* there, with 6 against 5. That was recorded as a
sharpness witness — and then, asked for the `r = 2` bound too, the same 6
turned out to be a theorem with no `r` in it at all
(`unpointed_pair_bound`), so the two rows are one statement:
`max(2r+1, 6)`, tight at every `r ≥ 2`. Twice in a row the honest
"measured, not proved" note was the thing that named the next theorem —
which is the only reason to write such notes down precisely rather than
as hedges.

Asked for the same at uniformity three, measuring first paid again, and
this time by *stopping* a wrong plan. Two shapes worked out by hand gave
13 and 15 at `r = 2`; the maximiser found 17 within a minute. Had those
hand shapes been written up as "the extremal configurations" — the tone
§26.4 used — the section would have been wrong before it began.

The measurement also decided the architecture. At `u = 2` the second
branch of the maximum is the constant 6, so `unpointed_pair_bound` needs
no `r`; at `u = 3` the neither-pointed maximum *grows*, so there is no
constant to prove and no analogue of that lemma to write. Knowing that
before starting is what turned a search for a non-existent theorem into a
correct statement of what does close (`r ≥ 6`) and what does not (`r = 2`
refuted, `r = 3,4,5` open).

> **Rule 13. A lower bound from a stochastic search is a lower bound on
> that search's effort, not on the quantity.** The neither-pointed row was
> first recorded as `17 24 33 36` and the numbers were used to argue how
> hard the open rows were. Re-running the same search for three times as
> long gave `17 28 36 41`, and the `r = 3` entry moved from "24, with 4 to
> spare against 28" to "28, with nothing to spare" — which is the
> difference between a row that might close and one that cannot close
> without an exactly tight argument. Nothing was *false*; the inference
> drawn from the numbers was worth less than it looked. Re-measure before
> a measurement is asked to carry an argument about difficulty.

## What re-reading the development changed, session N+9

Nothing in the corpus was re-read this session; the two rules below were
earned inside the development, which is where rules 12 and 13 came from
too.

### Six sessions inside a route whose ceiling nobody had multiplied out

`TwoCover.star_extremal_gives_m_plus_one` has been in the development
since §24, and §§24–27 are largely work inside it: prove
`StarExtremalAt m r`, feed it to that theorem, get
`SpreadYieldsDisjoint n 3 r`, get `f(n,3) ≤ r^n + 1`. The route was
instantiated at `r = n+1` from the day it was written, and the question
"what does `(n+1)^n` come to, against the 1960 bound?" was never asked.

It comes to a loss. Erdős–Rado is `2^n·n! + 1 ≈ √(2πn)·(2n/e)^n` with
`2/e = 0.7358`; the route's ceiling is `(n+1)^n + 1 ≈ e·n^n`. The ratio
is `(e/√(2πn))·(e/2)^n` with `e/2 = 1.3591`, and the gap in decimal digits
is 12 at `n = 100`
and 25 at `n = 200`. **The route cannot produce a record at `k = 3` even
if every conjecture in §§24–28 were proved.**

The arithmetic is one line and it is not new mathematics. Worse: **it was
already in the repository.** `docs/roadmap.md` §21.5, written four
sections earlier about the `τ`-indexed bound of §8, contains

>     b^b  >  (2b/e)^b  =  Erdos-Rado,     by a factor (e/2)^b = 1.359^b.

and concludes "not merely on the wrong side of the barrier — it is worse
than 1960 outright". The same constant, for the same reason: both routes
bottom out at `n^n`. Nobody carried it across to the neighbouring route,
because a route that is *making progress* — and §§25–27 did make progress,
three exact values of it — never asks to be costed.

> **Rule 14. A route has a ceiling, and you compute it in the first
> hour, not the sixth session.** Before proving anything *inside* a
> reduction, instantiate its best case and compare it with the bound you
> are trying to beat. If the best case loses, the reduction is a source
> of mathematics but not of records, and saying so is worth more than
> another constant inside it. The cost of not doing this is not a wrong
> theorem — everything §§25–27 proved is true and stands — it is
> direction.

Three things make this rule cheap to follow and there is no excuse for
skipping it. First, the comparison is arithmetic, not analysis. Second,
the same comparison had already been done in this repository for a
neighbouring route, so it did not even have to be derived — only looked
up. Third, the *statement* of the reduction already contains its
parameter: the
hypothesis of `star_extremal_gives_m_plus_one` quantifies over every
uniformity `m ≤ n` at one `r`, and the moment `¬ StarExtremalAt m m` is
known the parameter is pinned at `r ≥ n+1` with no further work.

That last step is why the barrier became a theorem this session rather
than a remark: `HiltonMilner.not_star_extremal_at_m_m` makes the
hypothesis *unsatisfiable* below `r = n+1`, so the ceiling is not "the
best we currently know how to do" but "the best the route can do".

### An algebraic restatement, checked one case too late

`RaoSpread` is `deg T F ≤ r^(m-|T|)`, and truncated subtraction makes
that painful to induct on, so the whole of `HiltonMilner.v` is written in
the multiplicative form. The first draft of that form was
`deg T F · r^|T| ≤ r^(m-1)`, which is wrong by a factor of `r`: it should
be `r^m`. The draft survived several hundred lines of proof outline
before evaluation at `T = {w}` — the one set the whole construction is
about, whose degree is `m·r^(m-2)` — showed it demanded `m ≤ 1`.

The error cost only a rewrite because the proof had not been attempted
yet. It would have cost a session if the restatement had been buried in
a lemma and the tight case never tried.

> **Rule 15. An algebraic restatement gets evaluated at the tight case
> before anything is built on it.** A reformulation is a claim of
> equivalence, and the cheapest possible refutation is the instance where
> the original is known to hold with equality. One substitution, before
> the first `Proof.`

### The novelty question, asked after the fact instead of during

Session N+9 built `HM(m,r)`, proved `¬ StarExtremalAt m m` at every
uniformity, and wrote it up — and only then, asked directly whether any
of it was new, went back and read §24.13 properly. §24.13 already had the
crossover at `r = m+1` as a measured phenomenon, both witnesses below it
by name (the triangle, `C([5],3)`), and `PG(2,q)` tabulated. The
measurement `I(3,3) = 10 > 9` in that section *is* `¬ StarExtremalAt 3 3`,
recorded two sessions earlier.

Nothing written was false, and the general construction is genuinely the
missing piece — §24.13's table of classical designs implies there is no
family beating the star below the crossover past `m = 3`, and `HM` is one,
at every `m`, because it is not a design. But §28 was drafted as though
the phenomenon were being discovered rather than generalised, and the
remark that the search "returns `C([5],3)` first" read as a find when the
object was already named upstream. §28.1a and §28.11 now carry the
correction and the ledger.

The mechanical fault is smaller than it looks and worth naming exactly:
the session read §27 and the handoff in §27.9 closely, because those were
the sections the brief pointed at, and skimmed §24. The prior work most
likely to have anticipated a result is not the work immediately before it;
it is the section where the question was first posed.

> **Rule 16. Before writing up a result, read the section that first
> posed the question — not the section you inherited.** A handoff tells
> you where the previous session stopped, which is not where the question
> started. Everything a result might duplicate is upstream of the handoff
> by construction, because a handoff only forwards what is still open.

And a second, blunter one, since this session also ran no literature
search:

> **Rule 17. "New" without a search is "new to this repository", and it
> gets written that way.** The register in this file exists to hold
> novelty claims to evidence. A result that never acquired a register row
> has not earned the unqualified word, however elementary the search would
> have been.

### Rule 18, and the pass that proved it in six pages

Session N+9 recorded a Tier B negative built on a `pdftotext` word-grep.
Asked to render the pages instead, it took **six pages** to refute its own
row: [Kup25] p. 53 defines `τ`-homogeneous families, a cap at every level
that is geometric in `|X|`, which is the shape the search was looking for
and the shape extraction cannot represent.

The mechanism is worth stating precisely, because "pdftotext is
unreliable" understates it. Extraction does not degrade mathematics; it
**re-encodes it into a different alphabet**. On p. 49 of the same survey,
`Δ(k^r)-system` comes out as `Δ(𝑘 𝑟 )-system`, where

```
  𝑘  is U+1D458  MATHEMATICAL ITALIC SMALL K   -- not U+006B 'k'
  𝑟  is U+1D45F  MATHEMATICAL ITALIC SMALL R   -- not U+0072 'r'
```

and the superscript is a space. `grep "B(k)"` returns 0 on a page
containing `B^(k)`. So a grep for a variable, a condition or an
inequality is not a weak search — the characters are not present to be
matched.

> **Rule 18. `pdftotext` locates prose words in ASCII and nothing else. A
> claim about a formula, a condition, an inequality or a variable can only
> be searched by rendering every page and looking at it.**

There is a second, less excusable half. The grep had flagged pp. 18, 52,
53, 64, 65 of the survey; four of the five were never rendered, and p. 53
was the one that mattered. **Locating a page and not opening it is the
same failure as not locating it, with the excuse removed.**

> **Rule 19. Render every page the locator flags, before reporting
> anything about the ones you did render.** A hit list is a work item, not
> a result. Reporting a negative while part of the list is unopened
> misrepresents the search as finished.

Three earlier rows — B10, B12, B13 — are negatives about an inequality, an
identity and an exponent. All three were searched the same way and are now
flagged in the register as unsupported. None is refuted; each is simply
not evidenced, and re-running them is a rendered-pass job.

---

## What re-reading the development changed, session N+10

**No literature was read this session and no register row was opened or
closed.** Nothing below is a novelty claim; rule 17 governs
`docs/roadmap.md` §29.8's ledger, which says in full that this session
produced no new mathematics. The three rules here were earned inside the
development, as rules 12–17 were.

### The bar was the wrong bound, in the section that set it

§28.4 costed the star-extremality route against **Erdős–Rado 1960** and
concluded — correctly — that `(n+1)^n` loses to `2^n·n!` by a factor
growing like `1.359^n`. That is true, it is machine-checked, and it is
the weakest available criticism of the route.

The record is not `2^n·n!`. It is Bell–Chueluecha–Warnke's
`(C·p·log k)^k` — register row **A6**, read in full, quoted verbatim in
this file — which at `p = 3` is `(C' log n)^n`. Against *that* bar, every
linear route in the development loses by far more and for a structural
reason: the base of a linear route grows like `n`, the record's like
`log n`, and the target's not at all. `tools/ceiling.py` puts the three
side by side and shows that the star-extremality route, the `τ`-indexed
route, the cover bound and §22.1's quadratic bound are *the same shape*,
which no pairwise comparison against 1960 makes visible.

> **Rule 20. Cost a route against the record, not against the last bound
> you can name.** Beating a superseded bound is not progress toward the
> problem, and the comparison that decides whether a route is in the
> running is one of *shape* — constant, logarithmic, linear — not of
> value at any particular `n`. A route that loses to 1960 is dead; a
> route that beats 1960 and is linear is also dead, and saying only the
> first understates it.

### The brief's first task had been done for several sessions

Session N+10's incoming brief opened its highest-ranked track with:
*"State it: `∃ C, ∀ n k, SpreadYieldsDisjoint n k (C·k)` … as a named
`Prop` in Coq, next to `Rao20_lemma2`, and derive `f(n,3) ≤ C^n` from it
through the existing `spread_reduction`. **Do this first**."*

`coq/Conjecture.v` has carried exactly that since it was written:
`spread_conjecture` is the `Prop` (in the more general shape
`∃ c : nat → nat`), `spread_conjecture_suffices` derives the whole
conjecture from it, `k3_corollary` specialises. `docs/roadmap.md` §2
points at it by name. The check cost one `grep` and it was run after
forty minutes of reading rather than in the first two.

The same brief asserted that "nobody in this programme has ever pointed
the machinery at" whether the spread threshold is bounded. §22's opening
paragraph is that observation, attributed to §18.5, and §22 is a whole
session's attack on it.

> **Rule 21. A handoff's "do this first" is a hypothesis about the
> repository, and it is checked against the repository before it is
> acted on.** Rule 16 says the prior work most likely to have anticipated
> a *result* is upstream of the handoff. This is its converse for
> incoming work: the prior work most likely to have already done a
> *task* is also upstream of the handoff, for the same reason — a
> handoff forwards what its author believed was open, and belief is not
> the index.

### A test that disagreed with the kernel, and was wrong

The first draft of `rust/tests/profile.rs` reported
`2^n·n! ≤ (n+1)^n` **failing at `n = 28`** — a statement `coqc` had
already accepted, as `Profile.erdos_rado_below_the_n_to_the_n_ceiling`,
at every `n` with no range. The test was wrong: `u128::pow` wraps
silently in release mode and `(n+1)^n` leaves `u128` at `n = 27`.

The trap is specific to this repository's arrangement. The testbed exists
to *falsify* the Coq layer — `rust/src/testbed.rs` is described in
`lib.rs` as exactly that — so a disagreement is the interesting outcome,
and the instinct is to believe it. Here the disagreement was silent
arithmetic in the falsifier.

> **Rule 22. When the testbed contradicts a machine-checked theorem, the
> testbed is wrong until its arithmetic has been re-derived.** The kernel
> does not have an overflow mode. Any exhaustive claim in `u128` states
> the range it is valid on and pins the first input outside it; every
> power is `checked_pow`, so the failure is an error rather than a
> number.


---

## What the development taught, session N+10 (second half)

No literature was read for Stage A either: §1's proof-level read of
[Lovett] §3 was done in the July 2026 session and this one worked from
its notes. The rule below was earned by formalising them.

### The hypothesis the application supplies is not the hypothesis the proof needs

`docs/roadmap.md` §1 records Lovett's Claim 3.4 as needing
`C(N, qN+m) ≤ q^(−m)·C(N, qN)` — the sample `V` has fixed size `qN`, so
with `q = c/d` the hypothesis is `c·N ≤ d·j` at `j = qN`. That is what
the *application* hands in, and it is what §1 wrote down.

The argument needs less. The step reduces by absorption to
`c·(N−j) ≤ d·(j+1)`, and `c·(N−j) ≤ c·N` makes `c·N ≤ d·(j+1)` enough.
One notch weaker, and **exactly** one: at `c·N ≤ d·(j+2)` the estimate is
false, the smallest witness being `N=1, j=0, c=2, d=1, m=1` — hypothesis
`2 ≤ 2`, conclusion `2 ≤ 1`.

Stating it at `c·N ≤ d·j` would not have been wrong. It would have been a
gap of the kind that costs a later session: reaching for the estimate one
index over and finding it unavailable, that session either re-proves it
or weakens its own statement to fit, and neither shows up as an error.

> **Rule 23. Prove a lemma at the weakest hypothesis its own argument
> needs, not at the one the application supplies — and record the witness
> that shows the weakening stops there.** Rule 15 says to evaluate a
> restatement at the tight case. The tight case is where the *argument*
> stops working, which is not in general where the *application* sits;
> when they differ, both belong in the file — the sharp lemma, and a
> corollary in the shape the caller wants.

`Counting.binom_ratio` carries the sharp hypothesis,
`Counting.binom_ratio_at_threshold` carries §1's, and
`Counting.binom_ratio_needs_the_successor` carries the witness.
`rust/tests/counting.rs` finds 102 counterexamples to the `j+2`
relaxation in a small box, so the boundary is measured and not merely
asserted.

### A set-level identity is two obligations in a list formalisation

Stage B of the spread lemma (`docs/roadmap.md` §31) turned on one
sentence of [Lovett] p. 13, quoted in §1 as the stage's easiest step:

> *"Note that we can decode `(S,V)` given `φ(S,V)` since
> `S = M ∪ (S \ M)` and `V = Z \ M`."*

§1 reads that as *"the formal obligation is not '`φ` is injective' — it
is `ψ (φ (S,V)) = (S,V)` for an explicit `ψ`, which is a rewrite, not a
case analysis."* Half of it is.

`V = Z \ M` **is** literal in lists: `Z` is built as `V ++ M` and `M` is
disjoint from `V`, so filtering `M` out returns `V` itself, no `NoDup`
required. `S = M ∪ (S \ M)` **cannot** be literal: as lists that is
`M ++ (S \ M)`, a permutation of `S`, not `S`. So the stated equation is
false in the encoding, and the thing the count actually needs —
injectivity — has to be reached through `SetEq` and closed with
`Sets.SetNoDup_setEq_eq`, which requires `Distinct F`.

That hypothesis is invisible at the level of sets, where the identity
really is an identity. It is now on every downstream statement.

> **Rule 24. A set-level identity in a source becomes two obligations in
> a list formalisation: the half that is literal, and the half that is
> only up to permutation — and the second half needs a hypothesis the
> source never states.** Decide which half is which before planning the
> stage. The cost of not doing so is not a wrong proof; it is a plan
> whose "one rewrite" step turns out to propagate a hypothesis through
> everything after it.

### And a limit on what a falsifier in the wrong representation can see

`rust/tests/fragment.rs` ran the fragment, Claim 3.3, the encoding and
the decoder over 32968 exhaustive `(F,S,V)` triples **before** any of it
was proved, exactly as §1 instructs, and every claim passed — including
`ψ(φ(S,V)) = (S,V)`.

It passed because the Rust implementation represents sets as **bitmasks**,
which are canonical: `M ∪ (S \ M)` and `S` are the same `u32`. The
permutation problem of rule 24 is an artefact of the *list* encoding and
is invisible to a set implementation. It was found by the kernel
rejecting the proof, not by the testbed.

> **Rule 25. A falsifier in a canonical representation cannot falsify a
> representation defect.** An exhaustive sweep bounds the mathematics,
> not the encoding. When the testbed and the formalisation differ in how
> they represent the objects — bitmask against list, set against
> sequence — say so where the sweep is reported, because the two are
> checking different statements.

### The same representational obstacle, three times, and what it cost

Rule 24 was earned on the decode of Claim 3.4: a set-level identity
becomes two obligations in a list formalisation. Finishing the *count*
met the same obstacle twice more, and the pattern is worth naming.

1. **The decode** (`S = M ∪ (S \ M)`): literal for `V`, only `SetEq` for
   `S`. Cost: the hypothesis `Distinct F`, now on every downstream
   statement.
2. **The injectivity**: had to be routed through `SetEq` and
   `Sets.SetNoDup_setEq_eq` rather than proved by rewriting.
3. **The count of the key space**: `Z = V ++ M` is not an *ordered
   sublist* of the universe, so it is not in `Counting.subsets_of_size`
   and carries no binomial count until it is canonicalised
   (`docs/roadmap.md` §31.9).

Each is the same fact — lists carry order that sets do not — and each was
paid for separately, at the point of use, after the plan had been made.

> **Rule 26. In a list formalisation of a set-theoretic argument, build
> the canonicalisation layer once and early, not at each point of use.**
> A `norm U A := filter (fun x => memb x A) U` with its four lemmas
> (lands in `subsets`, preserves length, idempotent on sublists, commutes
> with `setminus`) is perhaps forty lines. Paying it three times in
> fragments, each with its own workaround, cost more than that and left
> the third instance unfinished.

None of this is a defect in the source. Lovett's §3 is about sets and is
correct about sets. It is a defect in *staging a list formalisation from
a set-theoretic plan*, and it is the thing to budget for next time.

### The one document nothing checked

Everything in this repository that makes a claim is gated. A theorem is
gated by the kernel, then by `coqchk`, then by `tools/statements.txt`
against the statement it had when it was reviewed. A definition is gated
by mutation testing, which asks whether it is load-bearing. A number in
the prose is gated by `tools/docnumbers.py` against the list it counts.
A route's worth is gated by `tools/ceiling.py` against the record.

The pull request was gated by nothing at all — and it is the only one of
those documents a reader forms their opinion from. Worse, it has every
property that makes drift likely: written once at the end of a session,
never regenerated, and quoting counts, theorem names and novelty
judgements from memory of work done days earlier. Every failure this
repository has already had in prose is available there in a form nobody
would notice: a count copied from the previous session, a theorem cited
by a name a rebase renamed, an unqualified "new" with no search behind
it.

`tools/prcheck.py` closes it, and it earned its place on first run by
finding that six `Example`s in `coq/Counting.v` had never reached
`tools/audited.txt` — so a claim citing one of them resolved to nothing.
They were unaudited, not wrong; but the audit list is the artefact that
says which is which, and it did not.

> **Rule 27. The write-up is an artefact of the work and is gated like
> one.** If a claim in a pull request cannot be resolved mechanically to
> a theorem, a test, a mutation or a path, it is a sentence rather than
> a result. The gate cannot check whether the prose is true — no gate
> here can — but it can check that everything the prose names exists,
> that every count matches the list it counts, and that rule 17 was
> obeyed rather than intended.

The template carries one section that is mandatory and cannot be
mechanised: **What did not move.** A branch that cannot name the bounds,
exact values and ledger rows it failed to move has not been read
carefully by its author, and no tool can tell the difference between an
honest answer there and a hollow one. Presence is checked; honesty is
the author's. That asymmetry is the same one `tools/statements.py` has —
it checks that a statement did not move, never that it is the right
statement — and it is stated here so nobody mistakes a green gate for a
reviewed claim.

---

## What re-reading the development changed, session N+11

### An instrument, for the third time

`docs/roadmap.md` §32.6a's own summary of the mutation-job change
carried a causal sentence that the *next* measurement refutes, and it
was carried in three places at once — the workflow file, `docs/
testing.md`, and the commit message of `b0f9d25`:

> "the contention is why both were slower than a solo run"

The three data points, in the order they were taken:

```
  2decd53   mutation job    1h20m34s    partly contended  <- the "reference"
  d524766   mutation jobs   1h28m, 1h32m   fully contended
  b0f9d25   mutation job    1h36m04s    SOLO              <- the slowest of all
```

The solo run is the slowest of the three. Contention cannot be what made
the contended pair slow, and the 1h20m figure everything was measured
against was **itself a contended run**, so it was never a clean baseline
in the first place. What is actually true is that the job varies by
roughly a quarter of an hour on GitHub runners for reasons none of these
three measurements isolates.

**The change itself is unaffected and stays.** One job instead of two is
half the runner minutes whatever either takes, and the check-run count
went 12 to 6. Only the explanation was wrong, and it has been deleted
from both files.

This is the third time in this programme that the thing that bit was an
instrument rather than the mathematics — rule 13 (a search reported as
an answer), rule 22 (a measurement compared against a differently-scoped
one) — and it is the second time the specific defect was a *baseline
that shared the property being measured*.

> **Rule 28. A baseline must not carry the defect it is being used to
> measure.** Before attributing a difference to a cause, check that the
> number it is compared against was taken without that cause present. If
> it was not, the comparison measures nothing, however large the
> difference is. A saving established by *counting* — one job instead of
> two — survives this; an explanation established by *comparing* does
> not.

### B19c contradicted B19d, and B19c was the one that was wrong

B19c ended: *"What remains not found is the absolute form and the
Hilton–Milner-shaped extremal question under it."* That is two claims,
and the first of them is refuted by this file's own transcription check
further down, which confirms `Spread.RaoSpread` matches [Ra20]'s Lemma 2
verbatim — *"every non-empty `Z`"*, *"at most `r^{k−|Z|}`"* — and by the
[BCW21] section, which records the same lemma being quoted there.
Bell–Chueluecha–Warnke's own definition **is** the absolute form:

> "a family `S` of `k`-element sets is called `r`-spread if there are at
> most `r^{k−|T|}` sets of `S` that contain any non-empty set `T`"

So the absolute condition is published, named and in this corpus. B19c
now claims only what B19d already got right: the unoccupied corner of
the 2×2 is the **extremal question** under the absolute condition with an
intersecting hypothesis, not the condition itself. Two rows of the same
register disagreeing is a defect the register is supposed to prevent, and
the fix is to make the weaker row quote the stronger one rather than
restate it.

---

## Session N+11: the corpus, and one exact value that was in it all along

The brief for this session named two papers as the first targets of any
continuation of the B19 search (row B19f) — Kostochka's Δ-system survey
and Füredi's 1978 Bolyai paper — and one as the highest-priority
acquisition for the `ι(4)` search: Abbott–Exoo 1992. One of the three was
obtained and read in full. What it contains is not what it was fetched
for.

> **The commissioned deep-research report that the brief refers to was
> not included in the brief.** The prompt ends with the literal
> placeholder `[PASTE THE DEEP RESEARCH REPORT HERE]`. Every row below is
> therefore evidenced by this session's own reading, at the evidence
> class stated, and the report's findings are **not** transcribed. Rows
> the brief asked for that could not be independently evidenced here are
> recorded as not done rather than copied.

### [Kos00] — read in full, 9 of 9 pages rendered

A. V. Kostochka, *Extremal problems on Δ-systems*, in *Numbers,
Information and Complexity* (Bielefeld, 1998), Kluwer, 2000, 143–150.
Retrieved from the author's page,
`kostochk.web.illinois.edu/docs/2000/survey3.pdf`, 9 pp,
sha256 `ab75a3f3081b86f90b1880771d646036c23a996e28d6d2fce0d8916a9ad94d9d`.
The PDF is a 25 October 2011 re-typeset; the text is the survey.

**Notation.** Kostochka's `f(k,r)` is the *largest* family, not the
threshold. p. 1: *"Define `f(k,r)` to be the least cardinal so that any
`k`-uniform family of more than `f(k,r)` sets contains a Δ-system
consisting of `r` sets."* So `f(k,3)` **is** this development's `g(k)`,
and `Sunflower.UpperBound k 3 (f(k,3)+1)`. His `g(k,r)` is the *weak*
Δ-system function and is a different object; the collision with this
repository's `g` is total and is why every number below is restated in
the local convention.

| # | Claim | Verdict | Evidence |
|---|---|---|---|
| A9 | `f(3,3)` is *"the first unknown sunflower number"* (`STATUS.md`, `docs/roadmap.md` §20) | **REFUTED. It has been known since 1969, and this repository's own lower bound is the exact answer.** | [Kos00] p. 4, rendered: *"Abbott and B. Gardner [2] proved in 1969 that `f(3,3) = 20`, and since then no other exact value of `f(k,r)` for `k ≥ 3` and `r ≥ 3` became known."* In local convention: `g(3) = 20`, so `f(3,3) = 21`. `Intersecting.lower_bound_3_3_20` proves `f(3,3) ≥ 21` — **tight** — and `PureLink.f_3_3_at_most_27` was six too high. Now `coq/AbbottGardner.v`, as a carried `Prop`. |
| A9a | The primary source for A9 | **Not read; paywalled** | [2] = H. L. Abbott and B. Gardner, *On a combinatorial theorem of Erdős and Rado*, in W. T. Tutte, ed., *Recent progress in Combinatorics*, Academic Press, 1969, 211–215. Not open access, no preprint, not on arXiv. What is read is Kostochka's sentence, verbatim, from a rendered page. |
| A9b | A second, independent source for A9 | **Confirms the shape, not the number** | Bennett–Priestley, *The sunflower-free process*, arXiv:2509.16355 — **already in this corpus as `pdf/sfprocess.pdf`** — p. 7 rendered: *"in some of the best known constructions, the authors make use of the fact that the precise answer is known for very small cases of `r` and `w` (e.g., [AG69b])"*, and p. 25 rendered gives `[AG69b]` as the Tutte-volume paper. So a 2025 paper in the corpus cites Abbott–Gardner for exactly this and nobody here had opened p. 7. |
| A10 | The Abbott–Hanson–Sauer substitution's **intersecting** side condition is *"not stated"* in the literature (`STATUS.md`, the `10^(n/2)` row) | **REFUTED. It is stated, twice, on the same page.** | [Kos00] p. 2: *"It is derived from their construction for every positive integer `t` of an **intersecting** `3^t`-uniform family `F_t` of cardinality `10^((3^t−1)/2)` not containing a Δ-system of size 3."* And p. 3, in the proof: *"Since `F_{t−1}` and `F_1` both are intersecting families, `F_t` also is an intersecting family."* This repository found the condition by computation and recorded it as a gap in the secondary literature; the gap was in the corpus, not in the literature. |
| A11 | The 1972 seed family | **Printed in full, and it matches** | [Kos00] p. 2: *"`F_1 = {{1,2,3},{1,2,4},{1,3,5},{1,4,6},{1,5,6},{2,3,6},{2,4,5},{2,5,6},{3,4,5},{3,4,6}}` with the ground set `{1,…,6}`"*. Ten triples on six points: `Intersecting.iota3` up to relabelling, and `rust/tests/iota_structure.rs` proves there is only one isomorphism class, so "up to relabelling" is the whole of it. |
| A12 | `Sharp.AHSOptimal` — *"the sharp conjecture"*, that `ι(b)² ≤ 10^(b−1)` | **The question is published; the formal statement is this repository's** | [Kos00] p. 3, immediately after the construction: *"It would be very interesting to improve the construction even just a bit. But maybe it is optimal."* That is the same uncertainty `Sharp.AHSOptimal` names, in prose, from the survey of the area. It is **not** stated as a conjecture and carries no `ι`; what this development adds is the reduction to a single uniformity and the integer threshold at each one (`Sharp.refutation_threshold`). Novelty is claimed for the *formalisation and the thresholds*, not for the question. |
| A13 | Abbott–Exoo 1992, *"the closest prior computational work"* to the `ι(4)` search | **Unreachable (primary); its `r = 3` content is recorded second-hand and is empty** | H. L. Abbott and G. Exoo, *On set systems not containing delta systems*, **Graphs and Combinatorics 8 (1992), 1–9**. Springer, paywalled, no preprint; `link.springer.com/article/10.1007/BF01271703` returns a 303 to an authorisation endpoint. Two rendered secondary sources say what it contains. [Kos00] p. 4: *"Abbott and G. Exoo [1] obtained the lower bounds `f(k,4) ≥ C·38^{k/3}` and `f(k,6) ≥ C·146^{k/3}`"*, and p. 5: *"Abbott and Exoo [1] gave the lower bounds `g(k,4) ≥ C·10^{k/2}` and `g(k,5) ≥ C·20^{k/2}`"* — **every one of them is `r ≥ 4`**. Bennett–Priestley p. 25, rendered, describes its method: *"the algorithm described in [AE92] includes an additional backtracking step. The authors use a basic learning algorithm to help determine which edges should be removed in the backtracking step, and also use it to bias the algorithm towards choosing specific sets."* So it **is** a computational attack, as the brief said, and its published results are for `r = 4, 5, 6`; nothing in either secondary source attributes an `r = 3` construction to it. That is a second-hand negative and is recorded as one. |
| A14 | The greedy/covering barrier (`Profile.greedy_forces_erdos_rado`) is unpublished | **Still "not found, not exhaustive" — but both named blockers are now cleared** | [Kos00] read in full: no barrier remark of that shape anywhere in it. Its §6, *Concluding remark*, is the whole of what it says about limits: *"One of the aims of the present article was to show that there was some progress lately in studying every of the functions `f(k,r)`, `g(k,r)`, `F(n,r)` and `G(n,r)`, but none of the main problems is solved."* Füredi 1978 was **not obtained in session N+11** and rule 19 blocked the negative there. It was obtained and read in full in session N+12 — see A15 — and contains no Δ-system material at all. So the two papers the brief named are both read and neither carries the remark. That is what changed; what did **not** change is the novelty verdict: two papers is not a literature search, rule 17 is not satisfied by clearing a two-item list, and the barrier's status stays *not found, not exhaustive*. |

### A moonshot proposed in conversation that the repository had already done

Asked what the session's results opened up, this session proposed as its
sharpest idea: `AHSOptimal` is exactly tight at `b = 9`, where the
substitution family has 10 000 members against a threshold of 10 001, so
one extra 9-set would refute it — and nobody has checked whether it
extends. It then derived the reduction, computed that the 3-element
covers of `ι(3)` are exactly its ten members, and reported the family
maximal, describing the result as a find.

`docs/roadmap.md` §13.1 already contained the table, including the
`b = 9` row with `τ = 9` and *"none"* addable, measured three
independent ways. It already stated the mechanism — the covering number
is multiplicative under substitution — and drew the same conclusion for
the whole 3-adic tower. `STATUS.md` already carried the `b = 9` margin.
`rust/tests/extension.rs` already contained the identical test, using
`extend::minimal_hitting_sets`, which already existed. The Rust file
written before this was noticed reimplemented all of it and was deleted.

What was genuinely missing is what §13.1 says is missing, in the
sentence immediately after the table: *"The general statement needs
`substitute` in Coq."* That is now `coq/Substitution.v`.

The failure is not the proposal — the proposal was correct, and it was
correct because the mechanism is real. The failure is the word
*"nobody has checked"*, asserted about a repository that had checked,
from a conversation in which nothing had been read. Rule 21 covers the
incoming-handoff version of this. It does not cover the version that
bit, where the claim about the repository is one the session invented
itself, and the enthusiasm of having invented it is exactly what makes
it feel unnecessary to check.

> **Rule 30. An idea generated in conversation is a hypothesis about the
> repository, and it is checked against the repository before it is
> reported — especially when it feels like a discovery.** Rule 21 is the
> same rule for incoming handoffs. A proposal arrives with no index
> attached, and the confidence that comes from having derived something
> is not evidence that it is absent from the tree. Grep first, and grep
> for the *object* (`10000`, `iota(9)`, `maximal`), not for the phrasing
> the idea happened to arrive in.

### Session N+12: [Fur78] — read in full, 31 of 31 pages rendered

Z. Füredi, *Erdős–Ko–Rado type theorems with upper bounds on the maximum
degree*, Colloq. Math. Soc. J. Bolyai **25** (Szeged 1978), North-Holland
1981, 177–207. Page-by-page log in `docs/papers/furedi78-rendered-pass.md`.

| # | Claim | Verdict | Evidence |
|---|---|---|---|
| A15 | Füredi 1978 might carry a published barrier remark about the greedy/covering method (the brief's second target for A14) | **REFUTED — the paper has no Δ-system content whatsoever, so it cannot carry such a remark** | All 31 pages rendered at 140 dpi and read. The words *Δ-system* and *sunflower* occur nowhere; Erdős–Rado 1960 is not among the nine references (p. 207) and neither is Abbott. The paper is about the Erdős–Rothschild–Szemerédi problem — the largest **intersecting** `r`-uniform family whose maximum degree is at most `c\|F\|` (p. 178) — and its machinery is fractional matchings and covers, `ν`-critical nuclei, Baranyai's factorisation theorem and Pelikán's theorem on projective planes. The brief's premise about this paper was wrong, and recording *why* it was wrong is the point of this row: no future session should spend budget on it again. |
| A15a | It was said to have no digitisation (session N+11, four routes tried) | **Wrong; it is on the author's own page, at a host nobody tried** | `www.renyi.hu/~furedi/PUBS3/furedi_005_ekr_with_upper_bound.pdf`, 723 721 bytes, 31 pp, image scan, retrieved 2026-08-10. The Illinois host session N+11 tried (`faculty.math.illinois.edu/~z-furedi/`) resets the connection; the Rényi host serves the whole publication list with scans. **Look there first for any Füredi paper.** The four routes that failed were not exhaustive and were reported as exhausted; that is the failure mode, not the missing scan. |
| A15b | Notation hazard | **A third `f`, and it collides with both the others** | [Fur78] p. 178 writes `f(n,r,c)` for the largest intersecting `r`-uniform family on `n` points with maximum degree `≤ c\|F\|`. This development's `f(n,k)` is a threshold with the uniformity first; [Kos00]'s `f(k,r)` is a largest family with the uniformity first. Three functions, one letter. Re-derive any `f`; never copy the symbol. Also present and unique to this paper: `ν*(R,ν)`, `Cap_B(c)`, `C(c)`, `L(R,ν)`, `K(r,c)`, `T(B)`. |
| A16 | Füredi's `H_1` — *"a 3-uniform, intersecting set system with 10 members on a 6-element set… There exists exactly one such `H_1`"* (p. 186) — is the `ι(3) = 10` witness | **Parameters coincide exactly; the identification is NOT made** | Figure 1 (p. 187) is a dot diagram this pass did not decode, and Füredi's uniqueness is inside his own hypotheses, so this row claims only the coincidence. What *is* checked, and is the substantive half: `10 = ½C(6,3)`, so any 10-member intersecting family of 3-sets on six points is **EKR-extremal at `n = 2r`**, taking exactly one set from each of the ten complementary pairs. `Intersecting.iota3` does that, and its covering number is 3 — the maximum possible at `b = 3`. So **at `b = 3` the sunflower-free constraint costs nothing**: the largest intersecting sunflower-free family of 3-sets is exactly as large as the largest intersecting family of 3-sets on six points. Checked in `rust/tests/support.rs::the_iota_three_witness_is_also_ekr_extremal`. |

### An acquisition reported as impossible, found on the fifth try

Session N+11 wrote that Füredi's 1978 Bolyai paper *"was not obtained…
no digitisation found, not on arXiv, not on the author's page"* and
listed four routes: title search, author page, the Bolyai series, and
the citing papers' bibliographies. The sentence is doing two jobs and
only one of them is honest. *"Four routes were tried and failed"* is a
budget. *"The volume appears to have no digitisation"* is a claim about
the world, and it was false: the paper is a scan on the author's own
publication list at `www.renyi.hu/~furedi/`, and one request fetched it.

The mistake was in the phrase *"the author's page"*. Session N+11 tried
`faculty.math.illinois.edu/~z-furedi/`, which resets the connection from
this environment, concluded "the author's page has nothing", and wrote
down a fact about the paper rather than a fact about that host. A dead
host is not an absent document.

This is rule 13's shape — a search reported as an answer — in the one
place rule 13 was not being applied, because acquisition did not feel
like search. It is the fourth instrument-caused bite in this programme
(rules 13, 22, 28).

> **Rule 29. A failed acquisition is a statement about the routes tried,
> never about the document.** Report it as *"not obtained; routes tried:
> …"* and stop there. In particular a host that times out, resets or
> 403s has told you nothing about whether the file exists — name the host
> and the failure mode, not the document. Authors commonly have more than
> one institutional page and the live one is often not the current
> affiliation.

### Session N+12: a commissioned prior-art search on `ι`, and what it found

The first real literature search this programme has run on its own
central object. Commissioned as a separate session, delivered as a
report, and **not** independently verifiable from this container for the
one row that matters. Evidence classes below are exact about that.

| # | Claim | Verdict | Evidence |
|---|---|---|---|
| A17 | `ι` is unnamed in the literature (asserted by this repository in every session since N+9) | **REFUTED — it was named in 2015, on a research blog** | Dömötör Pálvölgyi ("domotorp"), comment **23193** on *Polymath 10 Post 3: How are we doing?*, **2015-12-23T17:53:31+03:00**, verbatim: *"A further possible simplification could be to try constructions for intersecting families. If we denote the size of the largest k-uniform intersecting family without an r-sunflower by `f^{int}(k,r)`, then we have `(r-1)\cdot f^{int}(k,r)\le f(k,r)`."* In local notation `f^{int}(k,3) = ι(k)`. **PRIMARY, retrieved and read in this container** — see the retrieval note below; the LaTeX is from the `alt` attributes of the two rendered formula images, which is where WordPress keeps the source. |
| A17a | The inequality `(r−1)·f^{int} ≤ f` is this repository's own `Intersecting.doubling_lower_bound` | **YES — and this is the load-bearing hit, not the naming** | At `r = 3` Pálvölgyi's inequality reads `2·ι(k) ≤ g(k)`, which is `Intersecting.doubling_lower_bound` on the nose (proved here by `double`, the same two-disjoint-copies construction). The repository re-derived a December 2015 blog result and built five modules on top of it. That is the citation `Intersecting.v` now owes; it does not change a single proof. |
| A17b | Pálvölgyi's *equality* remark | **New to this repository, and directly about its central object** | Same comment, continuing verbatim: *"In fact, if I understood well, it is even possible (though unlikely) that equality holds for all values of k and r. This is the case for all best constructions for r=3, but not for r=4, k=3 (see our wiki and Abbott-Exoo)."* At `r = 3` that is `g(k) = 2·ι(k)`, which holds at the two known points (`g(2)=6=2·3`, `g(3)=20=2·10`) and is **stated by its own proposer as unlikely**. Carried as `Palvolgyi.PalvolgyiEquality` (`coq/Palvolgyi.v`), with the kernel checking what it is worth; see `docs/roadmap.md` §36. Note the second sentence: equality is *known to fail* at `r = 4, k = 3`, so this is a conjecture about `r = 3` and nothing wider. |
| A18 | Nobody has proposed the `ι(4)` search this repository is running | **REFUTED** | Same author, comment **23032**, **2015-12-14T01:50:01+03:00**, verbatim: *"So for example, for k=4, one could try to search for an intersecting sunflower-free family on 10 elements by enumerating all permutation groups of size at most 30 or so, and check whether they yield a solution. Unfortunately, I really have no clue how many such groups there are and I don't have enough confidence in my coding skills to attempt to write such a program, but maybe someone else is more talented."* That is the `ι(4)` ground-set search, and it is the *orbit* method `rust/src/orbit.rs` implements and §13.3 reports as exhausted over 136 (ground, group) pairs. Same idea, arrived at independently, eleven years apart. Gil Kalai replied (comment **23212**, 2015-12-25): *"I will also try to get some experimentation going in a few weeks."* Nothing in any of the seven Polymath10 threads reports that it happened. |
| A19 | No executed computational work on **intersecting** sunflower-free families exists | **REFUTED BY MY OWN RETRIEVAL — but read the scope line before quoting this row** | Philip Gibbs ("GFP"), comment **22690** on *Polymath10, Post 2: Homological Approach*, **2015-11-25T22:42:32+03:00**, verbatim: *"I have implemented a small variation of the process, where I also require that the family is intersecting."* He then reports, over **100 runs per parameter**, the mean and max family size at fifteen `(k, n)` pairs. His maxima: **`k=3`: 10** (at `n = 7, 10, 13`); **`k=4`: 21, 22, 24, 21** (at `n = 9, 13, 17, 21`); **`k=5`: 42, 46, 58, 49, 52** (at `n = 11 … 31`). See A19a for what those numbers are worth. **Scope, exactly.** The previous version of this row said *"no executed intersecting search **in any refereed source**"*, and that qualified claim still stands — a blog comment is not a refereed source. What is refuted is the unqualified belief the qualified sentence was standing in for, which is how every session since N+9 has used it, and which the commissioned report restated without the qualifier. The lesson is rule 13's again: a negative survives only inside the scope it was searched in, and a scope that lives in a subordinate clause will be dropped by the next reader. Note also that Gibbs's run **predates** Pálvölgyi's proposal by three weeks and is a different method — a random fill, not the permutation-group enumeration of A18. A18's "never executed" is about the permutation-group search and is *not* refuted by this row. |
| A19a | Where this repository stands against the one executed intersecting computation | **Ahead at `b = 4` and `b = 5`, level at `b = 3`** | `ι(3) = 10` exhaustively (`wide.rs`) against his max 10 — an independent 2015 corroboration of the value, by a different method. `ι(4) ≥ 27` (`Product.iota_four_at_least_27`) against his max **24**. `ι(5) ≥ 78` (§13, `plateau`) against his max **58**. One coincidence worth recording rather than reading into: `docs/roadmap.md` §9 reports `ι(5,10) ≥ 42` as *"the first value ever computed at `b = 5` here"*, and Gibbs's maximum at `(5, 11)` is also **42** — a SAT decision and a hundred random fills, eleven years apart, stopping on the same number. **His search was randomised, not exhaustive**, so none of it is an upper bound and none of it is in tension with anything here; and the repository is strictly better at both rungs where the answer is unknown. `rust/examples/gibbs2015.rs` re-runs all fifteen rows — see A19b. |
| A19b | The 2015 process is reproducible here, and reproducing it explains its own ceiling | **Reproduced; fourteen of fifteen rows, every mean within 0.5** | `plateau::search` with zero force moves *is* the random-fill process. Re-run at 100 runs per row it gives means 8.49 / 7.55 / 6.83 (`k=3`) against his 8.61 / 7.24 / 6.97, and 17.93 / 17.47 / 17.32 / 17.30 (`k=4`) against his 18.06 / 17.56 / 17.67 / 17.45. `(5, 31)` is beyond `plateau::candidates`' 28-point enumerator and was not re-run. **What the reproduction buys:** at `(4, 9)` — the ground set the 27-member family actually lives on — the fill reaches 27 nineteen times in a million runs. In 100 runs the expected number of hits is 0.002, so the 2015 report of 21 was not near-miss bad luck; the experiment was about five hundred times too small to see the answer once. `docs/roadmap.md` §36.2. |
| A19c | `ι(4)` is known, or bounded better than `[27, 71]`, or has been searched exhaustively | **NOT FOUND** | Routes (commissioned): arXiv full-text, Google Scholar forward-citation chains from AHS 1972 and from Kostochka's survey, Springer, ScienceDirect, zbMATH, Semantic Scholar. Routes (here, first-hand): all seven Polymath10 comment threads, **434 comments**, read through the WordPress API and grepped for `intersecting`. The completeness is checked rather than assumed — the API returns a `found` total per thread and the seven totals (143, 127, 104, 12, 37, 6, 5) match the number of distinct comments retrieved, so nothing was truncated by paging. No exact value, no improved bound, **no exhaustive intersecting search anywhere**. The interval `[27, 71]` is not a literature interval and should never be cited as one: 27 is this repository's substitution witness and 71 is `PureLink.iota_four_at_most_71_if_iota_three_is_ten`. Both ends are its own. |
| A20 | The AHS substitution and the value 10 are attributable to Abbott–Hanson–Sauer 1972 | **STILL DISPUTED, and the correction has itself been corrected** | The first report gave Abbott–Hanson, *On finite Δ-systems*, Discrete Math. **8** (1974), 1–12 for `α(3,3) = 10`; the verification report moves it to *On finite Δ-systems II*, Discrete Math. **17** (1977), 121–126, and adds the point that decides how much any of this matters: **`α` is the weak Δ-system function** — `r` sets with *equal* pairwise intersections, not a common core. Kalai says so in the same thread (comment **23773**, 2016-02-04, verbatim: *"r sets with equal pairwise intersecting size are called weak delta system"*), which is first-hand here. So `α` is **a different object from `ι` and from `g`**, and an `α` attribution cannot settle a `g` attribution either way. Row A10 still rests on a rendered page of Kostochka in which the intersecting construction is *"their"* — Abbott, Hanson and Sauer's — and rule 4 forbids preferring an abstract to a rendered page. **Owed: one of the three primaries.** Until then the repository's attribution stands. **What *is* now settled is the bibliography**, from Crossref (`api.crossref.org` — a registry rather than a snippet, and reachable from this container): Abbott–Hanson–Sauer, *Intersection theorems for systems of sets*, **J. Combin. Theory Ser. A 12 (1972), 381–389**, `doi:10.1016/0097-3165(72)90103-3`; Abbott–Hanson, *On finite Δ-systems*, **Discrete Math. 8(1) (1974), 1–12**, `doi:10.1016/0012-365X(74)90103-4`; Abbott–Hanson, *On finite Δ-systems II*, **Discrete Math. 17(2) (1977), 121–126**, `doi:10.1016/0012-365X(77)90139-X`; and, confirming row A13, Abbott–Exoo, *On set systems not containing delta systems*, **Graphs and Combin. 8(1) (1992), 1–9**, `doi:10.1007/BF01271703`. So all three Abbott papers exist with the years both reports gave, and the disagreement is purely about *which one contains the substitution* — a content question a registry cannot answer. Abbott–Gardner 1969 is **not** in Crossref, which is expected of a chapter in an Academic Press volume, so its title stays unconfirmed and `coq/AbbottGardner.v`'s wording is not changed on a report's say-so. |
| A21 | Rows A14 (greedy-cover barrier), and the AHS-optimality conjecture, and the maximality of substitution families | **All three still NOT FOUND, now against a wider search** | No named conjecture for `ι(b)² ≤ 10^(b−1)` beyond Kostochka's prose; no published maximality statement for the AHS families; no barrier statement for the classical greedy/covering method. Consistent with A12, A14 and §13.1. Three independent negatives do not make an exhaustive search, and none of these is upgraded. **A19b is now a barrier *measurement* for one specific greedy method**, which is not the same thing as a barrier theorem and is not recorded as one. |

| A22 | The covering-number literature can close the `ι(4,11)` rung, because `τ ∈ {3,4}` is forced there and a maximum below 32 would end it (`docs/roadmap.md` §37.5's proposal) | **REFUTED, decisively, and the refutation is checked here** | Commissioned search, then verified first-hand. **`k=4, τ=3`:** the maximum is not bounded below 32. Frankl–Wang, *Intersecting families with covering number three*, arXiv:2207.05487v3, Example 1.3 (JCTB **171** (2025), 96–139) construct `G(n,k)`, and at `n=11` it has **74 members**. ~~it grows like `Θ(n³)`~~ — **corrected in session N+13, see A24a: the growth is `Θ(n)`, and exactly `13n − 69` for `n ≥ 8`.** The conclusion is unaffected, because `13·8 − 69 = 35 > 32` already at the smallest admissible `n`. **`k=4, τ=4`:** this is Erdős–Lovász's `r(k)`; the best bracket is `42 ≤ r(4) ≤ 64`, with the classical `n`-free bound `k^k = 256`. Every one of these is above 32. **So no citation from that literature excludes a 32-member family**, and the reduction below 32 must come from 3-sunflower-freeness. |
| A22a | Where the `τ = 4` line's numbers actually come from | **Both ends of A22's `k^k = 256` and the `42` are one theorem on one page, and it is now read. The `≤ 64` is not, and is uncited anywhere in this repository.** | A22 and §37.6 attribute the `τ = 4` case to *"Erdős–Lovász `r(k)`"* and quote `42 ≤ r(4) ≤ 64` with *"the classical `n`-free bound `k^k = 256`"*, all on report from a commissioned search. Session N+15 rendered the primary: **[EL75] p. 612, Theorem 7, `r!(e−1) ≤ M(r) ≤ r^r`**, `M(r)` the maximum size of a 3-chromatic `r`-uniform clique — an intersecting family with `τ = r`, which is exactly this case. The arithmetic is checked here, in this container, not taken from the report: `4!(e−1) = 24 × 1.718281828… = 41.2388…`, so `⌈4!(e−1)⌉ = **42**; and `r^r = 4^4 = **256**`. **So the two numbers this repository carried on report are the two ends of a single displayed inequality, and both are now confirmed from a rendered primary source.** **What is not confirmed, and is the reason this row exists:** `r(4) ≤ **64**` is *not* Theorem 7 — Theorem 7's upper bound is 256 — so that half of A22's bracket comes from some other source that neither §37.6, A22 nor `docs/references.md` names. It is quoted in two places and cited in none. It is also not load-bearing: 64 > 32 and so is 256, so A22's conclusion holds on the weaker number alone. Recorded so that a later session does not mistake it for something this development checked. |
| A22a | `G(11,4)` rebuilt and tested here, rather than taken on report | **Reproduces exactly, and it confirms a prediction this development makes about it** | Example 1.3 quoted verbatim from the arXiv PDF (fetched, 30 pp, `pdftotext`; **p. 2 has since been rendered to an image and read, A24a**): `B = {[2,k+1], {2}∪[k+2,2k], {3}∪[k+2,2k]}` and `A = {A ∈ ([n] choose k) : 1 ∈ A and A ∩ B ≠ ∅ for each B ∈ B}`, `G(n,k) = A ∪ B`. Built at `n=11, k=4`: **74 members** (matching the paper's own inclusion–exclusion), intersecting, and `τ = 3` with `{1,2,3}` a transversal exactly as the paper says. **The prediction:** `PureLink.iota_four_at_most_71_if_iota_three_is_ten` gives `ι(4) ≤ 71` on the exhaustive `ι(3) = 10`, and `74 > 71`, so `G(11,4)` *cannot* be sunflower-free. It is not — it contains **3481** three-sunflowers, and a randomised greedy retains only **17 of 74**. `rust/tests/frankl_wang.rs`. This is the concrete form of the gap in A22: the extremal family for the covering-number problem is useless for the sunflower problem. |
| A24 | A published bound exists on the **support** — the number of points — of an extremal sunflower-free 4-uniform family, which would make the `ι(4,n)` ladder a finite search | **NOT FOUND — and this repository already knew why, which is the finding about the report and not about sunflowers** | Third commissioned search, then every page of all three primaries rendered to an image and read here (Majumder 6 pp, Frankl–Pach–Pálvölgyi 10 pp, Frankl–Wang 30 pp; PyMuPDF at 150 dpi, `pdftotext` deliberately not used). **Nothing in the report's central section was new to this repository.** `docs/references.md`'s [FPPTZ24] entry already records, from an earlier session's rendered read of the same pages: that Conjecture 14 is *equivalent* to Erdős–Rado, crediting Hunter; that `g_v(k) ≥ 2^k − 1`; and the sentence *"We could not find any papers studying the quantity `g_v(k)`"*. Row B14 has Hunter's answer read **in full** (MathOverflow 463150, to Pálvölgyi's question 462924, via the StackExchange API). So the report re-derived a finding this repository had and presented it as news, and the first draft of this row did the same thing back. **What stands, restated as prior art rather than discovery:** `g_v` is the support function §37.6 wanted bounded; bounding it is equivalent to the whole conjecture; therefore **no ladder design may be predicated on obtaining a support bound.** That instruction is the useful residue, and it was already implicit in `docs/roadmap.md` §7's treatment of `SliceRank.GroundBounded`. One citation correction: FPP's ref. **[17] is MathOverflow question 163689**, which is the *direct-sum / wreath-product* discussion cited on their pp. 2 and 4 — **not** Hunter's equivalence, which is the inline URL truncated in the p. 8 render and is 463150 per B14. Do not merge the two. |
| A24a | The `k=4, τ=3` maximum "grows like `Θ(n³)`" (A22, as written in session N+12) | **WRONG, and corrected — the growth is linear** | Frankl–Wang p. 2 rendered. Eq. (1.3) is `\|G(n,k)\| = (k²−k+1)·C(n−3,k−3) + O(C(n−4,k−4))`, so at `k=4` the leading binomial is `C(n−3,1) = n−3` and the growth is `13(n−3) + O(1)` — **linear**. The cubic reading came from taking `C(n−1,k−1)`, the first term of the exact eq. (1.4), as the leading term; but the four `C(·,k−1)` terms carry coefficients `+1 −1 −1 +1`, which sum to zero, so the `n³/6` cancels. Exactly: **`\|G(n,4)\| = 13n − 69` for `n ≥ 8`**, checked for `n = 8…400` in `rust/tests/support_bounds.rs`, and `13·11 − 69 = 74` reproduces A22a's rebuilt value. **A22's conclusion survives**: `35 > 32` at `n = 8`, so the refutation of §37.5 never depended on the rate. Recorded because the wrong rate was committed, not because it changed an outcome. |
| A24b | The `τ=3` negative at `k=4` rests only on Example 1.3 being a construction, since Frankl–Wang's Theorem 1.4 needs `k ≥ 7` | **The `k ≥ 7` restriction is real, but the negative is stronger than a construction: the value is *known*** | Frankl–Wang p. 2 rendered. Theorem 1.4 does require `k ≥ 7, n ≥ 2k`, so it does not cover `k=4`. But eq. (1.5) on the same page reads `f(n,k,3) = \|G(n,k)\|` for **`k ≥ 4`, `n > n₀(k)`**, proved by Frankl, *On intersecting families of finite sets*, Bull. Austral. Math. Soc. **21** (1980), 363–372 (their ref. [4]) — so the `k=4` τ=3 maximum is an equality for large `n`, not merely bounded below by a construction. And their ref. **[1] is S. Chiba, M. Furuya, R. Matsubara, M. Takatou, *Covers in 4-uniform intersecting families with covering number three*, Tokyo J. Math. 35(1) (2012), 241–251** — read off the rendered reference list on p. 30, which settles a title the report could not retrieve and which the prose on p. 2 makes ambiguous. That paper is the exact `k=4` case. **Not retrieved** (Tokyo J. Math., not on arXiv); it is owed only if someone wants the small-`n` cases, since the refutation is already unconditional via the construction. |
| A24c | Erdős–Lovász's `N(k)` — the largest number of points in a maximal intersecting family of `k`-sets — bounds the support of this repository's extremal families | **`N(4) = 16` exactly, and it *does* apply to `Product.iota4`, which is such a family. But it does not close the ladder.** | **Majumder, arXiv:1402.7158v1 p. 3** rendered, verbatim: *"In [3], Hanson and Toft proved that, actually, `N(k) = 2k − 2 + ½C(2k−2,k−1)` for `2 ≤ k ≤ 4`"* — ref. [3] being **D. Hanson and B. Toft, *On the maximum number of vertices in n-uniform cliques*, Ars Combinatoria 16 (1983), No. A, 205–216**, which the report listed as unretrieved and could not confirm. So `N(4) = 16` and `N(3) = 7` (the Fano plane) are **equalities**, and 16 is a genuine upper bound. The bracket on the way there, for the record: Erdős–Lovász lower `16` (eq. (1), a construction), Tuza upper `42` (eq. (6)), Majumder upper `32` (eq. (9)). **The definition is the catch** (Definition 1.1, p. 1): a maximal intersecting family is one with `tr(F) < ∞` and `F = F^⊤` — it equals its own family of transversals. `rust/tests/support_bounds.rs` proves `Product.iota4` **is** one: `τ(iota4) = 4 = k`, and no 4-set outside it blocks it, checked over the whole universe of sets rather than just `[9]` (a blocking 4-set using a point outside `[9]` would restrict to a blocking 3-set inside `[9]`, and `τ = 4` says there is none). So `iota4`'s nine points sit inside `N(4) = 16`. **Why the ladder is still open:** a *maximum-size* intersecting sunflower-free family need not be maximal *as an intersecting family*, because the set one would add may complete a sunflower. The bound is real and applies to the family we have; it is not known to apply to the family we are looking for. |
| A24d | The Frankl–Pach–Pálvölgyi tree family is **intersecting** | **CONFIRMED, and this one is genuinely new here — because the family this repository already had is not intersecting** | The report's one new mathematical observation, and it survives. FPP p. 7 gives `g_v(k) ≥ 2^k − 1` via *"the `k`-uniform family whose sets are the root-to-leaf paths in a rooted binary tree of depth `k`"*. **Two readings of that sentence, and they are different families.** `rust/src/construction.rs`'s `tree_paths` takes the paths as **edge** sets: `2^k` members, `k`-uniform, sunflower-free, on `2^(k+1) − 2` points, checked to `k=6` in `rust/tests/ground_set.rs` since an earlier session. The **vertex** reading takes them as vertex sets: `2^(k−1)` members on `2^k − 1` points. The difference that matters: **the edge family is not intersecting and the vertex family is.** Two paths through different children of the root share no edge, but they do share the root vertex. Measured in `rust/tests/support_bounds.rs`: at `k=4` the edge family has **64 disjoint pairs out of 120**, while the vertex family has none. So the witness this repository has had since the `GroundBounded` work says nothing about `ι`, and the vertex one does: at `k=4` it is **8 members, 4-uniform, intersecting, sunflower-free, on 15 points**. Checked for `k = 2…6`. Two further notes. **The vertex reading is the paper's**: it reproduces `2^k − 1` exactly, where the edge reading gives `2^(k+1) − 2` and overshoots the figure FPP state — so `ground_set.rs`'s family is a stronger support witness than the paper's but is not the paper's construction, and neither test should be cited for the other's claim. And `2^k − 1` counts the **support**, not the members; reading 15 as a member count is the natural misreading. FPP add the family *"is not optimal, in fact, not even maximal"*. **Consequence:** the support of an *intersecting* sunflower-free 4-uniform family is at least 15, so nine was never the ceiling; `docs/roadmap.md` §41. |
| A24e | `Product.iota4` — this repository's `ι(4,9) = 27` witness — is an object with a name in the literature | **YES, two of them, and both were found by reading pages rather than by searching** | **(i) It is a wreath product.** FPP p. 4 defines `F ≀ G` on `n` disjoint copies of `G`'s ground set, with `\|F ≀ G\| = \|F\|·\|G\|^k` for `k`-uniform `F`, and Lemma 7: if `F` and `G` are odd-sunflower-free and `G` is an antichain, so is `F ≀ G`. Taking both factors to be `C₃`, the three 2-subsets of a 3-set, gives `3·3² = 27` members, 4-uniform, on `3·3 = 9` points — and `rust/tests/support_bounds.rs` finds an explicit relabelling showing **`C₃ ≀ C₃ ≅ Product.iota4`**. Since `C₃` is an antichain and odd-sunflower-free, and odd-sunflower-free implies sunflower-free (FPP p. 1), **Lemma 7 is an independent published proof that `Product.iota4` is sunflower-free** — a second route to `Product.iota_four_at_least_27`'s content. FPP attribute the wreath product to Frankl's 1977 thesis (their [12], *Extremalis halmazrendszerek*, kandidátusi értekezés, MTA Budapest), and the *direct-sum* idea separately to Abbott–Hanson–Sauer 1972 (their [2], p. 2). **These are two different operations**, and the one behind `ι(4,9) = 27` is the wreath product — which is indirect evidence bearing on rows A10/A20, whose open question is what exactly AHS 1972 contains. It does not settle A10: it is a 2024 paper's attribution, not a rendered page of AHS 1972, and rule 4 still applies. **(ii) It is a maximal intersecting family.** See A24c. |
| A24f | Shifting the family first might bring the covering-number maximum under 32, closing the `ι(4,11)` rung after all | **NO — and the number is 35, which is the closest the literature has come** | The one loophole A22 left, and Frankl–Wang closes it with the only theorem in the paper that reaches `k = 4`. Theorem 1.6 (p. 3, rendered) gives, for **every** `k` and `n > 2k`, the exact maximum over intersecting **initial** (shifted) families with `τ ≥ s`, as `g(n,k,s) = \|K(n,k,s)\|` where `K(n,k,s) = {K : 1 ∈ K, \|K ∩ [2,k+s−1]\| ≥ s−1} ∪ C([2,k+s−1],k)`. Computed at `k=4` in `rust/tests/support_bounds.rs`: **`τ ≥ 4` gives exactly 35, independent of `n`** (`= C(6,3)+C(6,4)`), and `τ ≥ 3` gives `10n − 45`, so 65 at `n=11`. **35 > 32**, so the rung survives shifting by three — far tighter than A22's `42 ≤ r(4) ≤ 64` bracket, and the tightest literature number against 32 found in any of the three searches. Still not a bound on `ι(4,11)`: shifting does not preserve 3-sunflower-freeness, so an extremal sunflower-free family need not be initial. **The `τ ≥ 3` count is dual-verified**: the paper's own Lemma 5.1 (p. 23) gives `g(n,k,3) = C(n−1,k−1) − C(n−k−2,k−1) − (k+1)C(n−k−2,k−2) + k + 1` by a different route, and it agrees with the enumeration at every `n` from 9 to 30 — the construction checked against the paper's arithmetic, not against a restatement of it. Their eq. (5.1) `g(n,k,3) < \|G(n,k)\|` also holds at `k=4`, as it must, since `G(n,k)` is not initial. |
| A23 | Some published theorem bounds intersecting families with prescribed covering number **and** 3-sunflower-freeness | **NOT FOUND — and this is where the rung's difficulty actually lives** | The search found only generic sunflower-free bounds (Erdős–Rado, Kostochka, ALWZ, Hegedűs) with no intersecting or covering hypothesis, and Frankl's *Pseudo sunflowers* (Eur. J. Combin. **104** (2022), 103553) together with Frankl–Wang, *Intersecting k-graphs and pseudo sunflowers*, where pseudo-sunflowers are a **proof technique** for covering-number problems rather than an added hypothesis that lowers the maximum. A negative from one commissioned search over a well-identified literature; not exhaustive, and recorded as such. Its consequence is concrete: **the `ι(4,11)` computation is not replaceable by a citation.** |

**How the thread was retrieved, since four sessions failed to.** Not by
fetching the page. `gilkalai.wordpress.com/2015/12/11/polymath10-post-3-…`
— the slug every earlier attempt used, and the one the first report
printed — **does not exist**; the post is at `2015/12/08/polymath-10-post-3-…`,
with a hyphen after "polymath". A wrong slug on WordPress returns a
404 body of 80 KB, and rendered through a fetch tool that looks exactly
like a blocked page. The 403s recorded in the first version of this
section were real but incidental; the actual failure was that nobody
had the address.

The route that works needs no address at all. WordPress.com exposes
every hosted blog as a JSON API on a **different host**, and it answers
this container without complaint:

```
  https://public-api.wordpress.com/rest/v1.1/sites/gilkalai.wordpress.com/posts/?search=polymath10
  https://public-api.wordpress.com/rest/v1.1/sites/gilkalai.wordpress.com/posts/13400/replies/?number=100&order=ASC
  https://public-api.wordpress.com/rest/v1.1/sites/gilkalai.wordpress.com/comments/23193
```

That is how all 434 comments across the seven Polymath10 threads were
read, and how a comment could be fetched **by the ID a report quoted** —
which is a verification primitive: a report that gives a comment ID can
be checked in one request, and one that does not, cannot.

> **Rule 31. A blog is a database before it is a page.** When a page is
> unreachable, look for the platform's API rather than for another
> mirror of the HTML: WordPress.com, Blogger, Discourse, Substack, arXiv
> and MathOverflow all serve structured JSON from hosts that are not the
> one that is failing, and the JSON carries the formula source that the
> rendered page throws away. A search that reports content from such a
> platform should be asked for the record IDs, because IDs are checkable
> and prose is not.

> **Rule 32. A retraction is a claim, and gets the same audit as the
> claim it retracts.** Session N+13's commissioned report opened by
> refuting its own previous version: it had said `N(4) = 16` was an upper
> bound, and it withdrew that on the ground that the inequality in the
> source points the other way. Both halves needed checking and both were
> half right. The direction *is* inverted in the source — Majumder's
> eq. (1) is a lower bound from an Erdős–Lovász construction, so the
> retraction's stated reason is correct — but three pages later the same
> paper cites Hanson and Toft for `N(k) = 2k − 2 + ½C(2k−2,k−1)` **as an
> equality for `2 ≤ k ≤ 4`**, so `16` is an upper bound after all, and the
> retraction's conclusion is wrong. A report that corrects itself has
> earned no extra credit: the second version is a new claim from the same
> process that produced the first. Read the page. And when a source
> states an inequality, look for whether the matching equality is known
> before concluding the inequality is all there is — the direction of a
> bound and the existence of an exact value are separate questions.

**What this changes for the `ι(4,11)` rung.** It stops being *"nobody has
looked"*. The honest position is now sharper and better: the refereed
literature has no value for `ι(4)`; one 2015 comment proposed exactly
this search and Kalai said he would run it; a *randomised* intersecting
search was run in 2015 and reached 24, three short of the construction
this repository has proved; **and no exhaustive intersecting search has
ever been run by anyone.** The rung is still the first. Rule 30 was
minted last session for claiming a discovery without checking; this is
the check, it found three things, and one of them refuted a negative
this repository had been repeating since N+9.

### Rows added at abstract level, and labelled as such

Rule 4 forbids *quoting* from an abstract. These rows exist so the next
session does not re-find the papers; none of them is quoted, and none is
load-bearing for anything in `coq/`.

| # | Paper | What it is | Evidence |
|---|---|---|---|
| B20 | Ahmadi–Norouzi, arXiv:2606.30593 (29 Jun 2026), *A polynomial improvement of the Naslund–Sawin bound for sunflower-free families using triangular tensors* | `\|F\| = O(n^{1/6}(3/2^{2/3})^n)` for sunflower-free **subsets of `2^[n]`** — the ground-set object, not the uniform one. **The base is unchanged**: `3/2^{2/3}` is exactly `SliceRank.NaslundSawinBound`'s `C`, and the improvement is the polynomial factor `n^{1/6}` against `3(n+1)`. So `SliceRank.ns_bound_to_exponential` and everything downstream of it are unaffected, and `docs/roadmap.md` §7.5's verdict — that the polynomial method contributes a constant and `GroundBounded` is the load-bearing part — is unaffected too. | abstract only, arXiv listing page |
| B21 | Ihringer–Kupavskii, arXiv:2505.03671 (6 May 2025, rev. 18 Sep 2025), *The Erdős–Rado sunflower problem for vector spaces* | The `q`-analogue: `k`-dimensional subspaces over a finite field, constructions from maximum rank-distance codes. **A different object from the set problem**; nothing here transfers. | abstract only |
| B22 | Rao, *The Story of Sunflowers*, arXiv:2509.14790 — **already in this corpus as `pdf/story.pdf`, read in full, 12 pp** ([Rao25] in the register above) | Expository. **Citation warning, and it is the one that matters:** `docs/roadmap.md` attributes the `r = O(k)` question to `[Ra20, p. 2]`, and that attribution is correct and must not be moved here — row A2's quotation is from Rao's 2020 paper. This 2025 exposition is not where the question is posed. | read in full, session N+9 |

### Not done, and why

* **The `φ(k,s)` notation hazard in [Kup25].** The brief describes a
  specific defect — that the Abbott–Hanson–Sauer sentence writes
  `φ(k,3)` while describing a family with no `Δ(3)`-system, so the
  second argument changes meaning in that one sentence. Checking it
  needs pp. 5–6 re-rendered and compared against the definition, and
  that was not done this session. **Do not import any `φ` from [Kup25]
  without re-deriving it** is the operative instruction either way, and
  it is now written down; the row itself is owed.
* ~~**Füredi 1978.** See A14. Four routes tried: title search, author page,
  the Bolyai series, and the citing papers' own bibliographies. The
  volume appears to have no digitisation.~~ **Done in session N+12** —
  the fifth route found it in one request. See A15, A15a; the lesson is
  in A15a and it is about the report, not the paper.
* **Kostochka–Mubayi PAMS 2016 and Kupavskii–Noskov arXiv:2410.06156**
  (row B19f's other two targets). Not attempted.

## Session N+14: an outgoing prompt is a handoff, and this one was not
##                checked against the repository

A parallel literature session was commissioned from a prompt written in
this session. It came back with careful work, and roughly half of it was
spent on questions this repository had already answered — because the
prompt was assembled from the register's *questions* without re-reading
the register's *verdicts*.

### The two items it wasted, both of them the prompt's top priorities

**"M1: is there any literature on the ground-set size of extremal
sunflower-free families? A hit closes k = 3."** Everything it found is in
`docs/references.md` [FPPTZ24], recorded in more precise form. Frankl–
Pach–Pálvölgyi's Conjecture 14, the Hunter equivalence, `g_v(k) ≥ 2^k−1`
by the depth-k binary tree, and FPP's own "we could not find any papers
studying the quantity" are all there, and Hunter's MathOverflow answer is
marked **READ IN FULL** with the StackExchange-API route that got it.

The returned report concluded that the binary tree "refutes the literal
linear form". The entry already distinguishes what that refutation
reaches: the **universal** reading of `GroundBounded` is false and is
formalised false — `IotaGround.the_universal_ground_reading_is_false`,
checked to `k = 6` in `rust/tests/ground_set.rs` — while
`SliceRank.GroundBounded` is an **existential** over families of extremal
size, `∀ m j, LowerBound m 3 j → ∃ F U, … length U ≤ c * m`, which the
binary tree does not touch: it has `2^k` members against
`f(k,3) ≥ 10^{k/2} ≈ 3.16^k`, so it is nowhere near extremal.
`bounded_ground_set_settles_k3` is not vacuous, and the repository
already knew the route is a *linear strengthening of a known equivalent
formulation* rather than a shortcut.

**"Tier 1 item 1: Füredi 1978, named, located, never opened."** It was
opened in session N+12. **A15**: all 31 pages rendered at 140 dpi and
read; *Δ-system* and *sunflower* occur nowhere in it; REFUTED as a
target. **A15a**: the "no digitisation" claim was itself wrong, and
records the working URL on the Rényi host. The prompt sent a session to
re-attempt a documented dead end, and it failed by the same routes A15a
names as the ones that fail.

### What it did deliver, including one correction to this session

* **A23 held** under a second, independent search: no published theorem
  bounds intersecting **and** prescribed-`τ` **and** 3-sunflower-free
  families. Kostochka–Mubayi, Proc. AMS 145 (2017) 2311–2321, is the
  closest and is structural, not an exact bound. **The 85 123.9 s SAT
  computation is not replaceable by a citation**, now on two searches
  rather than one.
* **M4 was overstated by this session, and is corrected here.** Asked
  earlier whether the combinatorial `r`-spread condition connects to
  incoherence and RIP in sparse recovery, this session searched, found
  nothing, and reported the resemblance as "a word collision". That is
  too strong. **arXiv:2108.13578, *ℓp-Spread and Restricted Isometry
  Properties of Sparse Random Matrices*, ties an ℓp-spread property of
  sparse random matrices to RIP, null-space and ℓp-compressibility.** It
  is a matrix ℓp-spread notion rather than the ALWZ/FKNP combinatorial
  lemma, so the narrow negative — nobody has imported the sunflower
  spread lemma itself into sparse recovery — appears to stand. The broad
  one does not. Recorded as a qualified hit.
* Kostochka–Mubayi and Kupavskii–Noskov were correctly open: this file's
  own "Not attempted" line for them was accurate.

### The rule that would have caught this already existed, and this
###     session broke it

The instinct on finding a failure like this is to write a rule. That
would be wrong here, because **rule 30 is already that rule** and it is
four sections up this file:

> *"An idea generated in conversation is a hypothesis about the
> repository, and it is checked against the repository before it is
> reported — especially when it feels like a discovery. Rule 21 is the
> same rule for incoming handoffs. ... Grep first, and grep for the
> *object*, not for the phrasing the idea happened to arrive in."*

The prompt was a set of ideas generated in conversation and reported —
to a third party, which is the only new part. Rule 30 covers it; it was
not applied. So the entry here is not a new rule but the record of an old
one being broken, which is the more useful thing for the next session to
read: the rules in this file are not short of coverage, they are short of
being run.

**Rule 30 gains one clause rather than a successor**, because the
outgoing case has a cost the incoming case does not: *an idea reported as
a task for someone else is a handoff, and its author is the only person
positioned to check it — the recipient cannot.* The prompt's two top
priorities were both refuted by rows in the very tables it was assembled
from, in the verdict column, beside the questions it copied. **A register
is not a list of open questions. Read the row you are about to re-ask.**

The mechanical fix is one command. `grep -n "Füredi 1978" docs/reading.md`
returns A15 and A15a; `grep -n "FPP" docs/references.md` returns the entry
that contains all of M1. Neither was run.

## Session N+15: a commissioned rendered pass, and the part of it that
##                could be checked here

The second commissioned literature session came back with a corpus, not
a claim: **136 pages rendered at 150 dpi, 96 read as images, no text
extraction at any point, not even to locate a page.** That is rule 19 run
properly, and it is the first pass in this development's history to
satisfy rule 18 across more than one paper. Thirteen sources, nine of
them read: [Kup25] (repo copy, 16pp), [KM17] 11/11, [KN24] 8 of 61,
[Fü83] 4/4, [FF85] 17/17, [FT85] 5/5, [Fü80] 8/8, [FFnt] 2, [EL75] 19/19,
[Fr17] 4 of 30, [FK18] 2.

**What it bought.** Four negatives this file had been forced to mark
*unsupported* under rule 18 — B9, B10, B12, B13 — are now negatives on
rendered evidence. That does not make them exhaustive and the rows still
say so. It makes them the right *kind* of statement: previously they said
"we ran a search that could not have found this"; now they say "we looked
at the pages and it is not on them". Two of B19f's four named targets are
closed, and B19g's placement of Duke–Erdős is confirmed from the primary
source rather than from the survey. And B12's operation, which every
earlier pass called unfound, turns out to be published in 1975.

### What was checked in this container, and what was not

Rule 21 and rule 30 both say an incoming report is a hypothesis. The
report names a corpus that is **not** in `docs/papers/pdf/` — eight of its
thirteen sources were fetched in the other container and are gone with
it — so most of it cannot be re-verified here. What *can* be is every
claim it makes about `kupavskii_survey.pdf`, which is in the corpus. Those
were re-rendered here at 150 dpi and read:

| Checked | Result |
|---|---|
| `[39]` = Erdős–Lovász, *Problems and results on 3-chromatic hypergraphs…*, Colloq. Math. Soc. János Bolyai **10**, 609–627, 1975 | **Confirmed**, [Kup25] p. 63 |
| `[52]` = P. Frankl, *Antichains of fixed diameter*, Moscow J. Combin. Number Theory **7** (N3) (2017) | **Confirmed** — but on p. **64**, not p. 63 as the report states. See below. |
| `[54]` = Frankl–Füredi, *Forbidding just one intersection*, JCTA **39** (1985) 160–176 | **Confirmed**, p. 64 |
| `[63]` = Füredi, *On finite set-systems whose every intersection is a kernel of a star*, Disc. Math. **47** (1983) 129–132 | **Confirmed**, p. 64 |
| The list holds exactly **one** Frankl–Kupavskii entry, `[57]` *The Erdős Matching Conjecture and Concentration Inequalities*, JCTB 157 (2022) | **Confirmed**, p. 64 — so the survey cites **no** Frankl–Kupavskii diversity paper anywhere |

**Not checkable here, and recorded as reported:** everything quoted from
[EL75], [KM17], [KN24], [Fü83], [FF85], [FT85], [Fü80] and [Fr17] —
including [EL75] p. 620 construction (d), which is the session's most
load-bearing find and is now cited in row B12. It is a page quotation from
a rendered image, which is the strongest form this file accepts, but it
was rendered elsewhere. A session that re-obtains `1975-34.pdf` should
re-read p. 620 and p. 621 before B12's "FOUND" is treated as settled.

### One page number was wrong, and that is the useful part

The report cites the reference list as p. 63. It is p. 64: p. 63 carries
`[21]`–`[44]`, p. 64 carries `[45]`–`[73]`. This file's own B19f row had
p. 63/`[44]` and p. 64/`[62]` right all along, from the N+9 pass. A single
digit, no consequence for the claim — and exactly the kind of drift that
makes a report worth checking against the one source you hold rather than
accepted whole. The finding stands; the citation did not.

### The `[52]` mis-citation

[Kup25] p. 52 credits *"a recent paper of Frankl [52]"* with analysing
minimal covers *"in order to bound the maximal diversity of an
intersecting family"*. `[52]` resolves — confirmed here, p. 64 — to
*Antichains of fixed diameter*. The commissioned session rendered four
pages of that paper and reports it is about antichains and Kleitman's
diameter theorem, with no minimal-cover analysis, and proposes
Frankl–Kupavskii, *Diversity*, arXiv:1811.01111 as the intended source
(p. 1: *"its diversity is the number of sets not containing an element
with the highest degree"*).

Half of this is verified here and half is not. Verified: what `[52]`
resolves to, and that the survey's bibliography contains no
Frankl–Kupavskii diversity paper — so if the diversity line is theirs,
the survey does not cite it. Not verified: the contents of *Antichains of
fixed diameter*. The register's `[Fr17]` entry in `docs/references.md` now
carries the discrepancy as a flag rather than as a settled correction,
because a mis-citation in a published survey is a claim about someone
else's work and this container cannot read the paper.

> **Rule 33. The same word can name two objects in the same author's
> papers in the same year.** In [Fü83] a *`t`-star* is a `Δ`-system; in
> [FT85] — Füredi again, two years later, with Tuza — a *`t`-star* is
> `t` sets each having a point of its own, which is a completely
> different object. Rule 18 says the alphabet can change under you;
> rule 33 says the **vocabulary** can too, and it is worse, because a
> word that renders correctly gives no sign that it has been redefined.
> A vocabulary search is not done when the word is found. It is done when
> the *definition* on that page has been read and matched to the object
> being looked for. This is why B9's negative survives having three
> names for a sunflower: each name was checked at its definition.

### A number the repository carried on report, now confirmed from the page

The pass was commissioned to chase B9–B13 and B19f. It also, without
being asked, settled the provenance of a number in a different row.
Register row A22 and `docs/roadmap.md` §37.6 dispose of the `τ = 4` case
at the `ι(4,11)` rung by citing *"Erdős–Lovász `r(k)`"* for
`42 ≤ r(4) ≤ 64` and `k^k = 256`, on report from an earlier commissioned
search. [EL75] p. 612 Theorem 7, rendered in this pass, reads
`r!(e−1) ≤ M(r) ≤ r^r`. The arithmetic was done **here**, not taken from
the report: `4!(e−1) = 41.2388…` so `⌈4!(e−1)⌉ = 42`, and `4^4 = 256`.
Both numbers are the two ends of one displayed inequality on one page.

The `≤ 64` is **not** on that page and is uncited anywhere in this
repository — quoted twice, sourced nowhere. It is not load-bearing (64
and 256 are both above 32, so A22's conclusion survives on either), but
it is now flagged in the new row A22a rather than sitting unremarked.

**The transferable point:** a commissioned pass aimed at one set of rows
paid off in a row nobody asked about, because a *primary source* answers
questions the request did not contain and a *report* answers only the
ones it did. That is an argument for reading papers over commissioning
answers, and it is the second time this file has recorded it.

### What is still owed after this pass

1. **[AHS72] remains unreachable.** ScienceDirect returns HTTP 403 for
   both the article page and the `pdfft` route, with a browser
   user-agent. That is a fifth failed route. Rows A3, A20 and B10 still
   owe it, and rule 29 applies: this is a statement about the routes
   tried, not about the paper.
2. **Chung 1983 (`[17]`) and Chung–Frankl 1987 (`[19]`)** were not
   fetched, so B9 stays non-exhaustive on the vocabulary that started it.
3. **Frankl 1978 (`[44]`)** is the last of B19f's four targets still
   unread; Füredi 1978 (`[62]`) was closed at A15/A15a.
4. **[EL75] p. 620–621** should be re-rendered in a container that holds
   the file, per the caveat above.
5. **`r(4) ≤ 64` needs a source.** Row A22a: quoted in two places in this
   repository, cited in none, and not the upper bound of the theorem the
   surrounding numbers come from. Not load-bearing, and that is exactly
   why it will keep being copied forward unless someone sources it or
   drops it.
