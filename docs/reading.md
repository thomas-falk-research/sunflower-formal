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
| B9 | `ι(b)` (max *intersecting* sunflower-free family) is unnamed | **Not found** — but the search vocabulary was too narrow | Not in [Kup25] (now read in full, 66pp), [Ra20] (8pp), [ALWZ20] (19pp), [Lovett] (28pp), [Rao25] (12pp). **Caveat found this session:** [Kup25] fn. 6, p. 21, records that *"it is in this paper that `Δ(s)`-systems are called **`s`-stars**, a name that appears in the follow-up papers of Frankl and Füredi."* A third name for a sunflower, which every search here has missed. Empty is not absence, and this corpus is not vocabulary-complete. |
| B10 | The sandwich `2ι(b) ≤ g(b) ≤ 2b·ι(b)`, and the `k=3` equivalence | **Not found — and the negative is now suspect for a second reason; see rule 18.** The claim is an inequality, and no text-extraction search can locate one. | Same corpus. But see B10a — the *ingredients* are all published. |
| B10a | "the intersecting side has never been pointed at" | **REFUTED** | [ALWZ20] §4.2, titled *Intersecting set systems*, Theorem 4.2 p. 13: *"If F is an intersecting w-uniform set system, and for all T, \|F_T\| ≤ κ^{−\|T\|}\|F\|, then κ = O(log w)."* Different hypothesis from `ι` (spread, not sunflower-free), but the claim as written is false. Withdrawn in `coq/IotaRate.v`; the elementary version is now `IotaRate.intersecting_not_spread_above_uniformity`. |
| B10b | Theorem 4.2 is independent of the spread lemma, so it could give the modern bound at `k=3` without the axiom | **REFUTED, and the target it supported is closed** | The *proof* is on the same page as the statement, four lines below, and had never been read. [ALWZ20] p. 13 introduces it with *"We note the following corollary of Theorem 2.5:"* and proves it in full by *"If `F` is intersecting then it is not `(1/2, 1/2)`-satisfying (apply Lemma 1.6 for `r = 2`). Thus by the improvement of Theorem 2.5 from [19], it cannot be `(C log w)`-spread for a large enough constant `C`."* Theorem 2.5 **is** the spread lemma and [19] is Rao, i.e. `ALWZ.Rao20_lemma2`. Formalising 4.2 would consume the axiom, not demote it. Independently, the chain it was to feed is arithmetically worse than Erdős–Rado — see `docs/roadmap.md` §21.2 and `coq/IntersectingSpread.v`. Rule 6: page 1 is not the paper, and neither is the statement of a theorem on it.|
| B11 | The cone `g(b−1) ≤ ι(b)` is folklore | **Technique found; exact statement still not found** | Hunter's answer uses the same move — *"start with a maximal `t`-sunflower-free collection in uniformity `k−1`, and then add a unique 'dummy element' to each edge"* — in exactly this context. His dummies are *distinct per edge* (which grows the ground set); the repository adds *one shared* fresh point to every member (which makes the family intersecting). Same idea, different construction, different conclusion. No novelty was claimed and none is now. |
| B12 | `τ(substitute(G,H)) = τ(G)τ(H)`, and the maximality of the AHS families | **The earlier "not found" is WITHDRAWN. The surrounding literature is central to the survey; the specific identity is "still not found" — but see rule 18: it is an *identity*, so no extraction-based search could have found it, and that half of the verdict is unsupported.** | [Kup25] read in full. Its §1.7 *Approaches to constructing bases* is about exactly this material, under names this repository did not search for: **base**, **nucleus**, **generating set**, **crosscut**, **minimal cover**. p. 52: *"the produced sets ... give exactly the family of **minimal covers** for the sets in `F`. These are the bases of the type used by Frankl in [44]. In a recent paper of Frankl [52], the family of minimal covers is efficiently analyzed in order to bound the maximal diversity of an intersecting family."* — and the construction is *"essentially due to Erdős and Lovász [39]"*. p. 59: *"a `d`-simplex are the simplest examples of non-trivial intersecting families, that is, **intersecting families with covering number 2**."* So `τ` of intersecting families is a studied quantity with a named literature. The multiplicativity identity itself is still not found, but the search that said the area was untouched was wrong twice over — wrong vocabulary, and a broken extractor. |
| B13 | `ρ` multiplicativity, and the AHS spreadness profile `κ = b^{log₃2}` | **Not found — unsupported for the same reason as B10; see rule 18.** Both claims are formulas. | Not in [ALWZ20] §3 (read), not in [Kup25] (now read in full). But note [Kup25] §1.7, p. 49: spreadness is now a *tool* in this literature — *"r-spread families in many ways behave like sunflowers with r petals, albeit they are much easier to find"* — via the Kupavskii–Zakharov **peeling-simplification** and **spread approximation** methods, neither of which this repository knew about. Not exhaustive. |
| B14 | Zach Hunter's ground-set equivalence, credited to MathOverflow | **FOUND AND READ IN FULL** | `mathoverflow.net/a/463150`, 30 Jan 2024, answering domotorp's question 462924. Retrieved verbatim through the StackExchange API after `WebFetch` was blocked for the site. Quoted in full below; it confirms the equivalence *and* contains two further things this repository has. |
| B15 | Prescribed-symmetry / Kramer–Mesner applied to sunflower-free families | **Not found** | Nothing in the 2024–2026 arXiv sweep, nothing in [Kup25] pp. 5–6. Not exhaustive over design-theory venues. |
| B16 | `ι(3)=10` is the unique simple 2-(6,3,2) design | **VERIFIED — by exhaustion, not by citation** | The Handbook of Combinatorial Designs is not open access, so the uniqueness claim could not be read. It does not need to be: there are only `C(20,10) = 184756` ways to choose ten triples from the twenty on six points. Enumerated — exactly **12** are simple 2-(6,3,2) designs, and all 12 form a **single** isomorphism class under `Sym(6)`. `720/12 = 60` re-derives `\|Aut\|` independently of `structure::automorphisms`, and agrees with it. `rust/tests/iota_structure.rs::the_two_six_three_two_design_is_unique_and_that_is_checked_not_cited`. |
| B19 | `HM(m,r)` — the Hilton–Milner family thinned to a grid so that it is Rao(`r`)-spread — and `¬ StarExtremalAt m m` at every `m` | **WITHDRAWN as a negative. The search could not have found what it was looking for** — see the rule 2 box and rule 18. The claim is a *condition*, `deg T ≤ r^(m−|T|)`, and conditions do not survive text extraction. What survives is the positive half. | The *underlying object is classical, and that is now verified rather than assumed*. [FHHZ17] (Frankl–Han–Huang–Zhao, *A degree version of the Hilton–Milner theorem*, arXiv:1703.03896v2), **p. 1 rendered and read**, defines it verbatim: `HM_{n,k}` *"consists of a `k`-set `S` and all `k`-subsets of `[n]` containing a fixed element `x ∉ S` and at least one element of `S`."* `HM(m,r)` is exactly that family with the star part thinned to a transversal grid. What is not found is the thinning, or any extremal problem posed under a **level-wise** cap. See the search description below. |
| B19a | §24.13's claim that the neighbouring literature caps *one* degree statistic rather than every level | **Confirmed — from a rendered page rather than from assertion** | Same page. [FHHZ17] p. 1: *"Let `Δ(F) := max_x d_F(x)` and `δ(F) := min_x d_F(x)` denote the maximum and minimum degree of `F`, respectively. There were extremal problems in set theory that considered the maximum or minimum degree of families satisfying certain properties. For example, Frankl [7] extended the Hilton–Milner theorem by giving sharp upper bounds on the size of intersecting families with certain maximum degree."* One statistic, capped once. Rao's condition caps `deg T ≤ r^(m−|T|)` at every `|T|` simultaneously and geometrically, which is a different hypothesis — as §24.13 said and could not then cite. |
| B19b | The word "spread" in this literature means what it means here | **REFUTED twice over** | A web search for spread intersecting families returns the **fractional** notion — a family is `r`-spread when the maximum `s`-degree is at most `r^(−s)·|F|` — which is `Spread.Spread` in this development, *not* `Spread.RaoSpread`. `Spread.RaoSpread_Spread` relates them in one direction only, and the absolute form is the stronger hypothesis once a family exceeds `r^m`. A literature search on "spread" that does not disambiguate returns the wrong object. And the notion is *also* studied under a name containing neither word — see B19c. |
| B19c | A **level-wise, geometric** cap on the degrees of a family is not a studied notion | **REFUTED. It is studied, it is named, and the name contains neither "spread" nor "degree".** | [Kup25] p. 53, **rendered and read**: *"We say that a family `F ⊂ A` is `τ`-homogeneous with respect to `A`, if for any set `X` we have `|F(X)|/|F| ≤ τ^|X| · |A(X)|/|A|`. ... then it transforms into `μ(F(X)) ≤ τ^|X| μ(F)`."* Attributed to Zakharov and the author [98], alongside the *spread approximation* method, with a footnote recording a notation clash with Füredi's `τ`-homogeneous. This is a cap at **every** level, **geometric in `|X|`** — the shape of Rao's condition, generalised to an arbitrary ambient family `A`. With `A = binom([n],k)` it is the fractional condition (`Spread.Spread`) rather than the absolute one (`Spread.RaoSpread`), so it is not the same hypothesis; but §24.13's framing — that the neighbouring literature caps *one* statistic and a level-wise cap is a different kind of object — is **too strong as written**. What remains not found is the *absolute* form and the Hilton–Milner-shaped extremal question under it. |
| B19d | Where this development's hypothesis sits, now that the rendered pass has read the neighbours | **A 2×2, and only one corner is unoccupied** | Two axes: **relative** (`deg ≤ c·|F|`) vs **absolute** (`deg ≤ r^(m−|T|)`), and **one level** vs **every level**. [Kup25] p. 20, rendered: Frankl [44] *"studies the families in which no element is contained in more than a `c`-fraction of sets"* — relative, level 1. p. 53: `τ`-homogeneous — relative, every level. p. 46, Jiang–Longbrake's quantitative Füredi (Thm 52), rendered: the subfamily it produces satisfies *"for every `J = A ∩ B` ... and every `x ∈ [n] \ J` we have `|F*(J ∪ {x})| ≤ (1/s)|F*(J)|`"*, with a matching lower bound — relative, every level, **two-sided**, and phrased exactly as Rao's is, as a decay by a factor per added point. The unoccupied corner is **absolute at every level under an intersecting hypothesis**, which is `Spread.RaoSpread` and the setting of `I(m,r)`. §24.13's "the neighbouring literature caps one statistic" is right about Frankl and wrong as a general characterisation: the axis separating this work from the literature is relative-vs-absolute, not one-level-vs-all-levels. |
| B19e | `SpreadReduction.spread_reduction`'s recursion is peculiar to this development | **It has a published counterpart, one setting over** | [Kup25] p. 50, rendered, Observation 58: *"If `G ⊂ binom([n],ℓ)` is such that there is no `X` such that `G(X)` is `r`-spread, then `|G| ≤ r^ℓ`"* — proved by taking an inclusion-maximal `X` violating spreadness, so that `G(X)` is spread by maximality. That is the same argument as this repository's reduction (find a violating `T`, pass to the link, recurse, conclude `|F| ≤ r^m`), in the fractional setting rather than the absolute one. No novelty was ever claimed for `spread_reduction`; this records where its counterpart is. |
| B19f | §24.13 dates the degree-condition line to "Frankl 1987" | **Two earlier sources, both 1978, and one of them is titled the question** | [Kup25] reference list, rendered. p. 63, [44]: *P. Frankl, "On intersecting families of finite sets", J. Combin. Theory Ser. A 24 (1978), 146–161* — the paper p. 20 attributes the `c`-fraction max-degree condition to, so that condition is Frankl **1978**. p. 64, [62]: *Z. Füredi, "**Erdős–Ko–Rado type theorems with upper bounds on the maximum degree**", Colloquia Math. Soc. J. Bolyai 25, Szeged, 1978, pp. 177–207* — the closest-titled paper found anywhere, and nine years earlier than the attribution §24.13 carries. Neither is in this corpus. Both are the first targets of any continuation of the B19 search, together with p. 65's [89] *Kostochka–Mubayi, "The structure of large intersecting families", PAMS 145 (2016)* and [96] *Kupavskii–Noskov (2025), arXiv:2410.06156*, on the Duke–Erdős corner. |
| B19g | The absolute-one-level corner of B19d's 2×2 is empty | **REFUTED — it is the Duke–Erdős function, and the corpus already holds the paper** | [Kup25] p. 57, rendered, §1.9.3: `f(n,k,ℓ,s)` is the largest `k`-uniform family with no `Δ(s)`-system of kernel size `ℓ`, which the survey states for `k=3, ℓ=2` as *"no pair of elements is contained in `s` triples"* — that is `deg T < s` for every `\|T\| = ℓ`, an **absolute cap at one level**. Quoted values: `f(n,3,2,s) ~ (1/6)sn²`; `f(n,k,ℓ,s) = Θ_k(s^(ℓ+1)n^(k−ℓ−1))` for `k ≥ 2ℓ+2` (Bradač–Bucić–Sudakov). So Rao's condition is the **simultaneous, geometric** version of Duke–Erdős's single-level cap. `dukeerdos.pdf` has been in the corpus throughout and was never connected to `I(m,r)`. |

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

### The rendered pass, and what it immediately found

Redone the only way that counts: `pdftoppm` at 140–150 dpi, pages looked
at one at a time, asking whether the page poses or uses a **level-wise**
cap on the degrees of a family.

```
  FHHZ17                p. 1                    read
  vcdim2025.pdf         p. 3                    read
  kupavskii_survey.pdf  pp. 42, 52, 53, 59      read
```

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

**What is still not read.** 60 of the survey's 66 pages, all 15 other
corpus PDFs in full, and everything outside the corpus except [FHHZ17]
p. 1. On the evidence so far the honest position is: a level-wise
geometric cap **is** a studied notion; Rao's *absolute* form under an
*intersecting* hypothesis, with the Hilton–Milner-shaped extremal
question, has not been found — and that remaining negative is worth very
little until the pass above is finished.


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
| [AHS72], JCTA 12 (1972) 381–389 | Elsevier paywall; four routes tried (see above). No legitimate open copy. |
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
