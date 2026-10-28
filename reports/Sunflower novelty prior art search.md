# Prior art for B10, and a published D^{1/3} bound for B27

**B10 is not new. B27 is only partly new, and one of its framing claims is false.** Every piece of the B10 chain is already in print. The lower half `2ι(b) ≤ g(b)` is on MathOverflow from 2014 and is credited, second-hand, to Abbott–Hanson 1974. The cone `g(b−1) ≤ ι(b)` (row B11) appears word for word in a refereed 2025 paper and in a 2026 preprint. The upper half `g(b) ≤ 2b·ι(b)` is Gowers's 2015 "trivial argument" on Polymath10. The `k = 3` equivalence appears in Kalai's 2015 remark that an intersecting bound transfers to the general case by adding one point. No source we read prints the two-sided chain as a single display. That is a presentational gap, not a novelty.

B27 comes out PARTIAL. Its specific claims are still NOT FOUND, NOT EXHAUSTIVE: the c-independent floor of exactly 3 for `3 ≤ D ≤ 26` (Lemma 78.A) and the cap of 3 on free combinatorial degenerations (Lemma 78.B). However, I checked independently that every tester `q_c` is concise, and a refereed theorem then gives `D^{1/3} ≤ Q̰(q_c) ≤ SR̰(q_c)` for every `c`, over every field ([Briët–Christandl–Leigh–Shpilka–Zuiddam, Discrete Analysis 2025:15, Thm 1.8](https://arxiv.org/abs/2306.01718)). That has two consequences:

- Lemma 78.A follows from published work for `D ≥ 27`.
- Two sentences in `docs/roadmap.md` §78.3 are wrong as written: "Growth in `D` is still open" and "Positive characteristic is untouched".

By the repository's own criteria (§75.1, §77.1), a slice-rank lower bound that grows like a power of `D` closes the single-letter product-tester route. The register rows B9, B10, B11, B27, A17 and A19c all need edits, listed in the last table section below.

## Three notes, one search: where they agree and where they differ

This report combines three notes in `research_notes/Sunflower novelty prior art search/`:

- `b10_intersecting_sunflower.md` (B10/B11);
- `b27_slice_rank.md` (B27);
- `recent_sweep.md`, a forward-citation sweep for both candidates from 2016 to October 2026, run in parallel and mostly blind to the B10 note.

On B10 the two independent passes reach the same verdicts, with the same quotations. They differ in five places:

| Point of difference | Resolution |
|---|---|
| Pages of [AxBCDN26] viewed | The B10 note viewed **35/35**. The sweep viewed **12/35**, because an image-request limit dropped pp. 2, 5 and 7–27. The full read stands. The sweep's quotations come from pages that both notes viewed (pp. 3, 6, 29). |
| Polymath10 comments retrieved | The B10 note has **485 comments on 11 posts**. The sweep has **456 on 9 posts**. The difference of 29 matches the two extra posts (6970 and 65) in the B10 set. Neither total matches the repository's earlier **434 comments on 7 threads** (row A19c), which is a strict subset of both. |
| Abbott–Hanson 1974 attempts | The B10 note did only an OpenAlex lookup ("bronze" OA). The sweep made three ScienceDirect attempts (each HTTP 403) and an Unpaywall lookup, which returned the landing page only. Combined result: **unreachable**. |
| Overall B10 wording | B10 note: "FOUND in substance, not as a formal statement". Sweep: "PARTIAL, verging on FOUND". This report scores each component separately (next section), which removes the disagreement. |
| Kostochka's Δ-system survey | The sweep lists it as "not searched". The B10 note re-read [Kos00] 9/9 for this claim, and `docs/reading.md` (Session N+11) identifies [Kos00] as that survey. **Searched.** |

On B27 the notes disagree on substance:

- The B27 note says **NOT FOUND**. The sweep says **PARTIAL**.
- The B27 note viewed only p. 3 of arXiv:2306.01718, and it gives the wrong authors ("Christandl–Gesmundo–Zuiddam(-Lysikov et al.)"). The rendered title page lists **Jop Briët, Matthias Christandl, Itai Leigh, Amir Shpilka, Jeroen Zuiddam**, "Received 27 September 2023; Revised 17 February 2025; Published 10 September 2025", Discrete Analysis 2025:15, arXiv v4 (p. 1, viewed by me).
- The sweep read pp. 1–16, 19 and 20, and found Theorem 1.8.
- The two notes also differ on the Bürgisser and Tobler theses and on SDW26. The sweep says "not reached" for the theses and has 4/20 pages of SDW26. The B27 note read Bürgisser in full (26/26), Tobler in part, and SDW26 in full (20/20). The B27 note is authoritative on all three.
- One internal discrepancy: the B27 note says **36** CVZ18-citing papers were word-located, but its table lists **32** arXiv IDs.

## B10 and B11: every component is already in print

The repository's notation: `g(b)` is the largest b-uniform 3-sunflower-free family, and `ι(b)` the largest intersecting one. In [AxBCDN26] these are `f(w,3)` and `ψ(w,3,2)`. In [FW25] they are `m_k(2,…,2)` and `m_k(1,2,…,2)`.

| Claim / sub-claim | Verdict | Verbatim support (page) |
|---|---|---|
| `ι` is a named function (B9) | **FOUND** | [AxBCDN26] p. 3: *"This matching-constrained quantity was introduced by Abbott and Hanson [4]. In particular, ψ(w, k, 2) is the maximum over intersecting w-uniform families without a k-sunflower"* ([arXiv:2609.06175](https://arxiv.org/abs/2609.06175)). Mirko, 2014-04-21: *"How big could a k-uniform family G be if it contains no 3-sunflower and every two of its elements do intersect? … Make this a function g(k)"* ([MO 163689](https://mathoverflow.net/questions/163689)). Kalai, 2015-11-04: *"Let f(k) be the maximum number of k-sets in a family with no 3-delta system in which every two sets intersect"* ([comment 22224](https://gilkalai.wordpress.com/2015/11/03/polymath10-the-erdos-rado-delta-system-conjecture/#comment-22224)). |
| Lower half `2ι(b) ≤ g(b)` | **FOUND** | Mirko, 2014-04-21: *"Clearly g(k+1)≥2g(k) so g(4)≥20, f(k)≥2g(k)"* (MO 163689). [AxBCDN26] p. 6, (3.5): *"f(w, k) ≥ ψ(w, k, k − 1) + ψ(w, k, 2)"*, introduced as *"a case of the Abbott–Hanson disjoint-support split [4]"*. p. 23 cites AH74 for *"20 = f(3,3) ≥ 2ψ(3,3,2)"*. [FW25] p. 4: *"m_3(1, 2, 2) = 10 along with m_3(2, 2, 2) = 20 was proved by Abbott and Hanson [2]"* ([EJC](https://doi.org/10.37236/13277)). The AH74 origin is **second-hand** (rule 4). |
| Cone `g(b−1) ≤ ι(b)` (B11) | **FOUND, verbatim, three sources** | [FW25] p. 5, (12): *"m_{k+1}(s, r_0,…,r_{k−1}) ⩾ s m_k(r⃗)"*; at `s = 1` this is the cone (refereed). [AxBCDN26] p. 6, Lemma 3.3, (3.4): *"ψ(w,k,2) ≥ f(w−1,k)"*, with the proof *"add one new point to every member. The resulting family … is intersecting."* Kalai 22224: *"you get an intersecting family by adding a new element to your ground set and then adding it to all the sets."* |
| Upper half `g(b) ≤ 2b·ι(b)` | **PARTIAL** (argument printed; inequality not stated for `ι`) | Gowers, 2015-11-12: *"The simple upper bound is around 2km. This one proves by taking a maximal disjoint subfamily, which contains at most two sets, and using the pigeonhole principle to find at least m sets that all contain the same element"* ([comment 22417](https://gilkalai.wordpress.com/2015/11/11/polymath10-post-2-homological-approach/#comment-22417)). The same argument appears in [comment 22235](https://gilkalai.wordpress.com/2015/11/03/polymath10-the-erdos-rado-delta-system-conjecture/#comment-22235). [FW25] p. 5, (14): *"m_k(r⃗) ⩽ k r_0 · m_{k−1}(r_1,…,r_{k−1})"*. Combined with (12) this gives the stronger `g(b) ≤ 2b·g(b−1) ≤ 2b·ι(b)`. |
| `k = 3` equivalence (conjecture ⇔ `ι(b) ≤ C^b`) | **FOUND as a remark** (blog, not refereed) | Kalai 22224: *"an upper bound k! for the intersecting case gives you an upper (k+1)! for the general case"* via the cone. The converse direction, `ι ≤ g`, is trivial. [FW25] p. 18, Conj. 7.2, covers `ι` but does not state the equivalence. |
| The two-sided chain as one display | **NOT FOUND, NOT EXHAUSTIVE** | Not in [AxBCDN26] (35 pp.), [FW25] (20 pp.), [Kos00] (9 pp.), the 485 Polymath10 comments, or MO 163689, 115069, 488358, 489839 and 374016. |

Three inferences follow; all are PROVEN from the quoted lines. First, a star inside a sunflower-free family is intersecting and sunflower-free, so Gowers's sentence gives `g ≤ 2b·ι` in one step. That step is not written in any source read. Second, because `g(b−1) ≤ ι(b)`, the bound `2b·g(b−1)` is at least as strong as `2b·ι(b)`. The repository's `g_le_iota_scaled` therefore factors through the cone. Third, the cleaner citation for the equivalence is the cone (Kalai 22224; [FW25] (12)). It gives constant `C` rather than `2C`.

The search also turned up a result outside B10 that bears on the repository: [AxBCDN26] p. 28, Proposition 6.8, *"One has ψ(4,3,2) = 27"*. The upper bound is computer-assisted (*"105,917,089,577 search-tree nodes and finds no 28-member family"*), and the paper is unrefereed. `docs/reading.md` already holds this paper as [ABCDN26], and roadmap §60 replicates the search. Row A19c, which still says NOT FOUND, is therefore stale inside the repository itself.

## B27: the floor of 3 is unprinted, but a D^{1/3} floor is published

### What I verified directly

I downloaded arXiv:2306.01718v4 (sha256 `45510217…22ed641`) into a new scratch directory, rendered pp. 1–21 with `pdftoppm -png -r 150`, and viewed pp. 1, 3, 7–11 and 13–21 as images. All quotations below come from those images.

**Theorem 1.8.** p. 9: *"Theorem 1.8. Let T ∈ F^{n1} ⊗ F^{n2} ⊗ F^{n3} be concise. Then Q̰(T) ≥ (min_ℓ n_ℓ)^{1/3}."* Section 1.4 opens with *"Let F be any field."* (p. 13).

**Conciseness.** p. 13: *"We call T concise if R_ℓ(T) = n_ℓ for every ℓ ∈ [3]."* The flattening ranks are defined there as *"R_ℓ(T) … the matrix rank of T_ℓ"*.

**Asymptotic subrank.** p. 7: *"Q̰(T) = lim_{n→∞} Q(T^{⊠n})^{1/n} … The limit exists and equals the supremum by Fekete's lemma, since Q is super-multiplicative."*

**Asymptotic slice rank.** p. 8 defines it with a liminf: *"SR̰(T) = liminf_{n→∞} SR(T^{⊠n})^{1/n}. (Over the complex numbers, it is known that the liminf can be replaced by a limit. Over other fields, however this is generally not known.)"*

**Remarks on Theorem 1.8 (p. 10).**
- *"Theorem 1.8 does not rely on any special structure of the tensor T, unlike previous methods like the laser method that rely on T being tight."*
- *"Alternatively, Theorem 1.8 can be phrased without the conciseness condition … Let T be any tensor. Then Q̰(T) ≥ (min_ℓ R_ℓ(T))^{1/3}."*
- *"Theorem 1.9. Let T ∈ F^n ⊗ F^n ⊗ F^n be concise and symmetric. Then Q̰(T) ≥ n^{1/2}."*

**The proof (pp. 16–20).** p. 16 states the core ingredient: *"Theorem 2.1. Let T … be concise. Let ℓ1, ℓ2, ℓ3 ∈ [3] be distinct. Suppose that |F| > n_{ℓ3}. Then Q_{ℓ1}(T)Q_{ℓ2}(T) ≥ n_{ℓ3}."* Its proof is completed on p. 18. On p. 20, Theorem 2.11 restates the cube-root bound, and its proof reads: *"As in the proof of Theorem 2.10 we may assume that the base field F is infinite. We use Q̰(T^{⊠3}) ≥ min_{ℓ1,ℓ2} Q_{ℓ1}(T)Q_{ℓ2}(T) (Lemma 2.13) and … Q_{ℓ1}(T)Q_{ℓ2}(T) ≥ n_{ℓ3} (Theorem 2.1)"*.

**The field-extension step.** It is in the proof of Theorem 2.10 (p. 20): *"That theorem only holds over large enough fields however. Since the asymptotic subrank does not change under field extension [Str88, Theorem 3.10], we may assume that our base field F is infinite (by working over the algebraic closure of the original field)"*. Lemma 2.13 rests on *"Q̰(⟨a,b,c⟩) = min{ab, bc, ac} [Str88, Equation 4.6]"*. I did not read [Str88]. The proof is therefore complete as read, apart from two cited Strassen facts. Both are classical; the first is needed only for finite fields.

**Subrank ≤ slice rank.** This is standard and stated twice in the paper:
- p. 14: *"Subrank, slice rank, the flattening ranks and tensor rank satisfy Q(T) ≤ SR(T) ≤ R_ℓ(T) ≤ R(T) for every ℓ ∈ [3]."*
- p. 10: *"Slice rank was introduced by Tao [Tao16]. He proved that for every tensor T we have SR(T) ≥ Q(T)."*

The repository already uses the same step in roadmap §77 (Corollary 77.B, citing [ST16] Lemma 3 and [CVZ22] eq. (68)). The asymptotic form follows by taking `n`-th roots: `SR(T^{⊠n})^{1/n} ≥ Q(T^{⊠n})^{1/n}` for every `n`, and the right side converges to `Q̰(T)`. So `liminf_n SR(T^{⊠n})^{1/n} ≥ Q̰(T)`. **PROVEN.**

### Every q_c is concise (my check)

`docs/roadmap.md` §75.2 defines `q_c` as *"`q_c = 1` on monochromatic, `c` on rainbow, `0` elsewhere"*, with support `S_D`. §78.1 repeats the definition.

Take flattening 1 (rows `a`, columns `(b,c)`) and restrict to the `D` columns `(x,x)`. The entry is `q_c(a,x,x)`:
- if `a = x`, the triple is monochromatic and the entry is 1;
- if `a ≠ x`, the triple has exactly two equal letters, so it is neither monochromatic nor rainbow, and the entry is 0.

So these columns form the `D × D` identity, and `R_1 = D`. The same columns `(x,x)` in the other two positions give `R_2 = R_3 = D`.

The argument never uses `c`, so it holds for every `c`, including `c` with zeros and `c = 0`. The only entries involved are 0 and 1, so it holds over every field. **PROVEN.** **COMPUTED** as a cross-check: exact rank over `F_2`, `F_3`, `F_5` and `F_1000003`, at `D = 3, 4, 5, 6`, with random `c` and with `c = 0`, gives flattening ranks `[D, D, D]` in all 32 cases (scratch script `/tmp/claude-0/-home-user-sunflower-formal/1ebb4a50-96a0-5685-9f5c-ab90eb4993e3/scratchpad/dr_novelty/writer/scripts/concise.py`).

### Consequence

**`D^{1/3} ≤ Q̰(q_c) ≤ SR̰(q_c) ≤ D` for every `c` and every field. PROVEN, given [BCLSZ] Thm 1.8.** The proof of Thm 1.8 was read, apart from its two [Str88] inputs.

**Comparison with Lemma 78.A.**
- For `D ≥ 28`, `D^{1/3} > 3`, so the published bound is strictly stronger than 78.A.
- At `D = 27` the two bounds are equal.
- For `3 ≤ D ≤ 26`, 78.A's floor of 3 is not implied by the published bound and remains unprinted.

**Symmetric `c`.** When `c` is invariant under all permutations of the three positions, Thm 1.9 gives `√D`. This covers [NaSa17]'s `c ≡ −1/2`. BHL's `c` was not checked for symmetry.

**Effect on the route.** Lemma 75.B gives `dim P(c) ≥ SR(T_c)/2 ≥ D^{n/3 − o(n)}/2`. By §75.1, a tester bound of order `D^α` with `α > 0` "gives no bound at all" through [ASU12] Thm 2.6. §77.1's condition, "the route is dead if `σ_C(D) → ∞`", is therefore met.

That makes the single-letter product-tester slice-rank/`dim P` route closed in **every characteristic**. **PROVEN**, within this scope: testers `q_c^{⊗n}` with the same `c` in every coordinate. Before it enters the register it should go through the repository's usual fresh-context review.

**What this does not settle.**
- Testers whose `c` varies by coordinate, and non-product testers, are not covered. It is PLAUSIBLE that the same bound extends to them, but this was not checked.
- `Λ(D)` itself (the monomial subrank) is untouched.

### Verdicts for B27

| Claim / sub-claim | Verdict | Support |
|---|---|---|
| A c-independent, growing lower bound on `SR̰(q_c)` | **FOUND** (by composition: published theorem plus a one-line conciseness check) | [BCLSZ] p. 9, Thm 1.8; p. 13, definition of concise; p. 14, `Q ≤ SR` |
| 78.A for `D ≥ 27` | **FOUND** (implied by the row above) | same |
| 78.A's floor of exactly 3 for `3 ≤ D ≤ 26`, and equality at `D = 3` | **NOT FOUND, NOT EXHAUSTIVE** | No S_D tensor in SDW26 (20/20 pp.), Bürgisser (26/26), ST16 (complete), CVZ18 (57/57, read earlier); BCLSZ treats only the W-tensor and the cap-set tensor (p. 3) |
| 78.B (free combinatorial degenerations of `S_D` stop at 3) | **NOT FOUND, NOT EXHAUSTIVE** | The nearest published notion is Tobler's *"bequem"* support (Tobler 1991, printed p. 21), applied to generic tensors only. Corner-free sets, p. 5: combinatorial degenerations used *"to construct large induced matchings"*, not to cap slice-rank bounds ([arXiv:2111.08262](https://arxiv.org/abs/2111.08262)) |
| A new exact formula route | context only | SDW26 p. 3, Cor. I.2: *"SR̰(t) = min_{g∈GL} τ̃(H_{g·t})"* for every tensor ([arXiv:2601.21553](https://arxiv.org/abs/2601.21553)) |

Other verbatim context from the B27 note:
- Sawin–Tao Prop. 10 gives the Naslund–Sawin tensor *"slice rank (3/2^{2/3})^n e^{o(n)}"* ([ST16](https://terrytao.wordpress.com/2016/08/24/notes-on-the-slice-rank-of-tensors/)).
- [BCLSZ] p. 3, viewed by me: *"the asymptotic slice rank of the W-tensor (which appears in the study of sunflower-free sets) equals 2^{h(1/3)} ≈ 1.889 [Str91]"*.

Neither of these is the `S_D` tensor.

## Evidence classes and the pages nobody viewed

Rule-18 caveat: quotations from blogs and MathOverflow are verbatim API text (WordPress JSON, with LaTeX taken from `alt` attributes, or the StackExchange API), not rendered pages. All PDF quotations were read from rendered images, by me for [BCLSZ] and by the note authors for everything else.

| Source | Evidence class |
|---|---|
| [AxBCDN26] arXiv:2609.06175v1 | **Read in full**, 35/35 pages |
| [FW25] EJC 32(2) P2.43 | **Read in full**, 20/20 |
| [Kos00] Kostochka survey | **Read in full**, 9/9 (for this claim) |
| [SDW26] arXiv:2601.21553v2 | **Read in full**, 20/20 (B27 note) |
| Bürgisser thesis, 1990 | **Read in full**, 26/26 rendered |
| ST16 Sawin–Tao blog | **Read in full** (API text; remainder read this pass) |
| Polymath10 blog | **Read in full**, API text: 485 comments on 11 posts (B10 note) and 456 on 9 (sweep) |
| MO 163689, 115069, 488358, 489839, 374016 | **Read in full**, API text |
| [BCLSZ] arXiv:2306.01718v4 (51 pp.) | **Pages**: 1–21, the union of my 1, 3, 7–11, 13–21 and the sweep's 1–16, 19, 20 |
| Tobler thesis, 1991 (46 PDF pp.) | **Pages**: PDF 2–8, 19–20, 23–24, 46 |
| Wigderson–Zuiddam survey (133 pp.) | **Pages**: 1, 30–32, 95–97 |
| KMZ arXiv:2002.09472 | **Pages**: 6 |
| Corner-free sets, arXiv:2111.08262 | **Pages**: 5 |
| 32 listed CVZ18 citers; 2308.07101, 2606.30593, 2408.02328, 1702.02831, 1512.00525, 2604.19872; 1809.10318, 2301.04219, 2509.16355 | **Word-located only** (pdftotext; this is not evidence of absence) |
| [KL26]; 2604.18283, 2609.06633, 2510.08336 and others in the sweep | **Abstract only** ([KL26] was read in full earlier by the repository) |
| Abbott–Hanson–Sauer 1972, JCTA 12 | **Unreachable**. ScienceDirect: 403/Cloudflare on the article page and `/pdfft`. `api.elsevier.com`: 406. OpenAlex says bronze OA |
| Abbott–Hanson 1974, Discrete Math. 8 | **Unreachable**. ScienceDirect 403 ×3; Unpaywall gives the landing page only |
| Abbott–Hanson 1977, Discrete Math. 17 | **Unreachable** (same block) |
| Strassen 1991, Crelle 413 | **Unreachable**. De Gruyter returned HTTP 202 (challenge page); DigiZeitschriften 404; author page has no link; web search found no copy |
| Guo–Wang–Wu, Appl. Math. Comput. 535 (2027) 130313 | **Unreachable**. Unpaywall `is_oa:false`; ScienceDirect blocked; title only |
| Polymath10 wiki | **Unreachable**. michaelnielsen.org: 404 or connection reset; web.archive.org blocked by egress policy |
| ASU12 forward citations | **Unreachable**. Semantic Scholar 429; OpenAlex budget exhausted |
| [Str88] (Thm 3.10, eq. 4.6), Str87, Erdős–Szemerédi 1978, Deza–Frankl, Chung 1983, Chung–Frankl 1987, Pebody, Norin, Naslund's partition-rank paper, Fox–Sauermann, CLZ23 in full, arXiv 2609.17280, the WZ 2026 survey version, GitHub `bogdan27182/sunflower-paper`, Google Scholar, the blogs of Tao, Gowers, Lovett and Rao | **Not attempted** |

**Pages never viewed in a partly read source:**
- [BCLSZ] pp. 22–51. These include §5 (the alternative proof, from p. 35) and §6 (slice rank versus subrank).
- Tobler PDF pp. 1, 9–18, 21–22, 25–45.
- Wigderson–Zuiddam: every page except 1, 30–32 and 95–97. p. 29 was rendered but not viewed.
- KMZ: every page except 6. pp. 1, 2 and 7 failed at the request limit.
- Corner-free sets: every page except 5.

No pages were left unviewed in [AxBCDN26], [FW25], [Kos00], SDW26 or Bürgisser.

## Register and roadmap corrections

| Location | Current text | Correction |
|---|---|---|
| `docs/reading.md` B9 | "`ι(b)` is unnamed … Not found" | **REFUTED.** Named as `ψ(w,3,2)`, attributed to Abbott–Hanson 1974 (second-hand: [AxBCDN26] p. 3). Named first-hand by Mirko on MO 163689 (2014-04-21) and by Kalai in 22224 (2015-11-04). [FW25] writes it `m_k(1,2,…,2)`. |
| B10 | "Not found … NOT EXHAUSTIVE" | Split by component: lower half FOUND; upper half PARTIAL; equivalence FOUND as a remark; the single display NOT FOUND. Overall: **not a novelty — folklore assembly** (MO 2014; Kalai and Gowers 2015; [FW25] (12) and (14); [AxBCDN26] Lemma 3.3). Delete "Kostochka's survey" from "not searched", since it is [Kos00]. |
| B11 | "Technique found; exact statement still not found" | **FOUND verbatim**: [FW25] p. 5 eq. (12) (refereed), [AxBCDN26] p. 6 eq. (3.4), Kalai 22224. |
| B27 | "NOT FOUND in the 11 Tier 3c sources" | **PARTIAL.** [BCLSZ] Thm 1.8 plus the conciseness of `q_c` gives `SR̰(q_c) ≥ D^{1/3}`, c-independent and over every field, which implies 78.A for `D ≥ 27`. The floor of 3 for `D ≤ 26` and 78.B: NOT FOUND, NOT EXHAUSTIVE. Update "Not searched": Bürgisser read, Tobler partly read, CVZ18 citers word-located; [Str91] still unread. |
| A17 | Named 2015-12-23 by Pálvölgyi 23193 | Verdict stands; the attribution is too late. Earlier primaries: Mirko 2014-04-21 (also states `f ≥ 2g`) and Kalai 2015-11-04. Possible 1974 origin (AH74, second-hand). |
| A19c | "`ι(4)` … NOT FOUND" | **FOUND (claimed)**: [ABCDN26] Prop. 6.8, `ψ(4,3,2) = 27`. Unrefereed and computer-assisted; replicated in repository §60. Change "`[27, 71]`" accordingly. |
| `docs/roadmap.md` §78.3 | "Growth in `D` is still open" | Replace with `D^{1/3} ≤ SR̰(q_c) ≤ D` for every `c` and every field ([BCLSZ] Thm 1.8, p. 9; `q_c` is concise). Add `√D` for symmetric `c` (Thm 1.9). 78.A remains the better bound only for `D ≤ 26`. |
| §78.3 | "Positive characteristic is untouched" | The `D^{1/3}` bound holds in every characteristic (finite fields via [Str88] Thm 3.10, cited by BCLSZ p. 20, unread here). What remains characteristic-0-only is the floor of 3 and the single-letter formula. |
| §78 "One line" and §78.4 ledger | "does it grow with D? … still open"; "growth open" | Answered: growth is at least `D^{1/3}`, so by §75.1 and §77.1 the single-letter product-tester route is closed in every characteristic. §75.2's verdict and §77.1 need the same addendum. `Λ(D)` stays open. |

## Conclusion

The rule-17 search changes the standing of both candidates in different ways. B10 shrinks from a novelty claim to a citation task. Its mathematics has been folklore since 2014–2015, and the repository's real contribution is the machine-checked statement. B27's lemmas still have no printed counterpart at small `D`. But the question they were meant to frame, whether the barrier grows with `D`, already had a published answer: a 2025 subrank theorem applied to a tensor whose conciseness takes one line to check. That bound is cruder than 78.A at small `D`, but it holds in every characteristic and closes the route that §78 described as open.

The general lesson is about search scope. The decisive source sat in a neighbouring literature, general asymptotic subrank, not in sunflower or slice-rank papers. An earlier pass had read only page 3 of that source, and its author names were wrong.

The most valuable open acquisitions remain the following. Abbott–Hanson 1974 would settle the first-hand origin of `ψ` and of the doubling. Guo–Wang–Wu 2027 is the only recent paper on intersecting 3-uniform sunflower problems that could not be screened. Strassen 1991 is the home of support functionals. Any one of them could still move a verdict above.
