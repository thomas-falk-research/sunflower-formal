# Recent and forward-citation sweep (2016 – Oct 2026) for B10 and B27

Session date: 2026-10-27, all queries run 09:49–10:40 UTC. This is an independent second pass, done in parallel with `b10_intersecting_sunflower.md`. I did not read that file before running the sweeps. I opened it once afterwards, and only to check overlap. Downloads are in `/tmp/claude-0/-home-user-sunflower-formal/1ebb4a50-96a0-5685-9f5c-ab90eb4993e3/scratchpad/dr_novelty/sweep/<shortname>/`. Every page was rendered with `pdftoppm -png -r 150`. "Viewed" means the page image itself was read. `pdftotext` was used only to find pages. Page lists are exact. Note on [AxBCDN26]: an image-request limit dropped pp. 2, 5 and 7–27 during a first batch. Those pages were not retried, so they count as **not viewed**, and nothing from them is quoted below.

## B10 — `2ι(b) ≤ g(b) ≤ 2b·ι(b)` and "k=3 Erdős–Rado ⇔ ι exponential"

### Takeaway
**PARTIAL, verging on FOUND.** Every ingredient is in print. Both halves appear side by side in 2015 blog comments, in a Ramsey framing (Gowers). The operative direction of the equivalence appears as a remark (Kalai, by the cone `g(k) ≤ ι(k+1)`; the converse is trivial). The lower half and the cone also appear in a 2026 preprint as a named lemma, and the cone appears in a refereed 2025 paper. What is still **NOT FOUND** is the two-sided chain written as one statement, with the upper half stated for sunflower-free `ι` rather than for the Ramsey function. Verdict by component:

| Component | Status |
|---|---|
| Lower half `2ι ≤ g` | FOUND |
| Cone `g(b−1) ≤ ι(b)` | FOUND |
| Upper half `g ≤ 2b·ι` | PARTIAL (argument found; not stated for `ι`) |
| Equivalence | FOUND as a remark (via the cone) |
| Displayed sandwich | NOT FOUND |

My findings agree with `b10_intersecting_sunflower.md`, which reached them independently.

### Cited Findings
- **[AxBCDN26] arXiv:2609.06175v1** (viewed pp. 1, 3, 4, 6, 28–35 of 35).
  - p. 3 defines `ψ(w,k,m)` (max size of a w-uniform family with no k-sunflower and `ν(F) ≤ m−1`) and says: *"This matching-constrained quantity was introduced by Abbott and Hanson [4]. In particular, ψ(w, k, 2) is the maximum over intersecting w-uniform families without a k-sunflower, while ψ(w, k, k) = f(w, k)."* So `ι(b) = ψ(b,3,2)` is a **named function, attributed to Abbott–Hanson, Discrete Math. 8 (1974) 1–12**. This bears on row B9 ("ι is unnamed"): it is named.
  - p. 6, Lemma 3.3 (Star and split): *"For every k ≥ 3 and w ≥ 2, ψ(w, k, 2) ≥ f(w − 1, k), (3.4) f(w, k) ≥ ψ(w, k, k − 1) + ψ(w, k, 2). (3.5)"*. The proof of (3.4) reads: *"take an extremal (w − 1)-uniform family … and add one new point to every member. The resulting family … is intersecting."* (3.5) is introduced as *"a case of the Abbott–Hanson disjoint-support split [4]"*.
  - At k = 3, (3.5) is exactly `g ≥ 2ι`, and (3.4) is the cone.
  - p. 29, Theorem 6.9 proof: *"If two members of D_F(R) were disjoint, those two members and R would form a sunflower with empty core. Hence D_F(R) is intersecting."* Then `|F| = |N_F[R]| + |D_F(R)| ≤ 56 + 27 = 83`. This is an upper bound with an intersecting piece, by a different decomposition from the star.
  - No `2b·ι` upper bound and no equivalence statement on the viewed pages. pp. 2, 5, 7–27 were **not viewed**, so this supports no negative.
  - — [arXiv:2609.06175](https://arxiv.org/abs/2609.06175)
- **[FW25] Frankl–Wang, *New bounds on families without large sunflowers*, EJC 32(2) (2025) #P2.43** (viewed 20/20).
  - p. 5, (12): `m_{k+1}(s, r_0,…,r_{k−1}) ⩾ s·m_k(r⃗)`. With s = 1 this is the cone `ι(k+1) ≥ g(k)`, in refereed print.
  - p. 5, (13)–(14): *"If F_1,…,F_s ∈ F are pairwise disjoint and ν(F) = s, then F_1 ∪…∪ F_s is a transversal of F. Thus, m_k(r⃗) ⩽ kr_0 · m_{k−1}(r_1,…,r_{k−1})."* This is the Erdős–Rado step routed through links (`g ≤ 2k·g(k−1)`), **not** through the intersecting function.
  - p. 15, Theorem 6.1 and p. 4, Theorem 1.15: `m_3(1,r,r) = m_2(r,r)` for r ≥ 3, the intersecting/general comparison at uniformity 3.
  - p. 4 Remark: *"m_3(1, 2, 2) = 10 along with m_3(2, 2, 2) = 20 was proved by Abbott and Hanson [2]"* ([2] = Abbott–Hanson 1974).
  - p. 18, (42): *"the conjecture m_k(2,2,…,2) < c^k"*.
  - No sandwich and no equivalence statement.
  - — [EJC v32i2p43](https://doi.org/10.37236/13277)
- **Polymath10, Kalai's blog.** All 456 comments on 9 posts were retrieved through the WordPress API, and the text used here is the API's verbatim HTML.
  - **Kalai, comment 22224 (2015-11-04):** *"an upper bound k! for the intersecting case gives you an upper (k+1)! for the general case since for any collection without delta system of size r you get an intersecting family by adding a new element to your ground set and then adding it to all the sets. This last 'cheap' argument … But surprisingly it is useful to think about the problem for intersecting families and this allow to improve for r=3, the 2^k k! bound to (√2)^k k! . (Noga Alon observed this argument as a student and it was observed earlier too, perhaps by Abbot.)"* — [22224](https://gilkalai.wordpress.com/2015/11/03/polymath10-the-erdos-rado-delta-system-conjecture/#comment-22224)
  - **Gowers, comment 22235 (2015-11-04):** *"If there are no r disjoint sets, then there is a set of size at most 3(r-1) that intersects all the sets in the system, so there is an intersecting family of size at least n/3(r-1), so we get an upper bound of 3(r-1)m. One can also get a lower bound of (r-1)(m-1) just by taking r-1 disjoint intersecting families of size m-1. … Suppose you have a family of sets of size k and you would like either three disjoint sets or an intersecting subfamily of size m. … The simple argument gives a bound proportional to mk."* — [22235](https://gilkalai.wordpress.com/2015/11/03/polymath10-the-erdos-rado-delta-system-conjecture/#comment-22235)
  - **Gowers, comment 22236:** the k = 2 improvement *"The sets disjoint from A form an intersecting family"*. This is the same decomposition as [AxBCDN26] Thm 6.9.
  - **Gowers, comment 22214:** *"is it the case that if you insist that your family of sets is an intersecting family, then you can't do much better than f(k-1,r)?"*
  - **Pálvölgyi, comment 23193:** *"(r-1)·f^{int}(k,r) ≤ f(k,r)"* (already in the repository).
- **MathOverflow 163689** (domotorp, 2014). All comments and answers were retrieved through the StackExchange API.
  - **Mirko, 2014-04-21:** *"How big could a k-uniform family G be if it contains no 3-sunflower and every two of its elements do intersect? … Make this a function g(k) … Clearly g(k+1)≥2g(k) so g(4)≥20, f(k)≥2g(k)"*. This is the lower half in 2014, before Polymath10.
  - **Mirko, 2014-04-20:** *"there must be two disjoint sets A,B … every C∈F meets A or B … For every i≤k at most f(k−1) many members of F contain i … Hence f(k)≤2(1+k(f(k−1)−1))"*. This is the star step, but bounded by `f(k−1)` rather than by `g`.
  - The question itself: *"Denoting by f′ the version where the set family is required to be intersecting, f′(ab)≥f′(a)(f′(b))^a"*.
  - Naslund's answer (420288): *"This intersection property is critical, as it allows us to recursively utilize this construction"*.
  - — [MO 163689](https://mathoverflow.net/questions/163689)

### Inferences
- The upper half follows from Gowers 22235 in one line: a sunflower-free family has no 3 disjoint members, and a star in it is intersecting and sunflower-free. That line is not written anywhere I looked.
- The equivalence follows from Kalai 22224 plus the trivial `ι ≤ g`.
- So B10 should be cited as a **folklore assembly**: Kalai/Gowers 2015, MO 2014, [FW25] (12), [AxBCDN26] Lemma 3.3. It is not new.
- **Correction for B9:** `ι = ψ(·,3,2)` is named, by Abbott–Hanson 1974 via [AxBCDN26] p. 3. This is second-hand, because AH74 was not reached.

### Gaps
- **Abbott–Hanson 1974** (doi 10.1016/0012-365X(74)90103-4) is **unreachable**. ScienceDirect returned 403 on three URLs, and Unpaywall gives only the publisher landing page, with no PDF. It is the most likely refereed source for both ψ and an intersecting reduction, and per [AxBCDN26] p. 1 it raised *"the problem of proving recurrences for ψ"* on p. 11.
- **Guo–Wang–Wu, *Sunflower problems in 3-uniform intersecting hypergraphs*, Appl. Math. Comput. 535 (2027) 130313**, doi 10.1016/j.amc.2026.130313. Found as a forward citation of [FW25]; Crossref gives no abstract.
  - Unreachable: Unpaywall `is_oa:false`; the DOI resolves to linkinghub PII S0096300326003644, and ScienceDirect was blocked; WebSearch found nothing.
  - **Title only — supports no negative.** It is the top-priority target.
- Not searched: blogs by Tao, Gowers (own blog), Lovett and Rao; theses; Kostochka's Δ-system survey.

## B27 — Lemma 78.A (`c`-independent floor 3 on `SR̰_C(q_c)`) and Lemma 78.B (free combinatorial degenerations capped at 3)

### Takeaway
- **78.A: PARTIAL, and a correction to §78.3.** A *published, c-independent and field-independent* lower bound exists by a different route. [BCLSZ] Theorem 1.8 says that the asymptotic subrank of any concise tensor is at least (min dim)^{1/3}. Every `q_c` is concise; this is my inference, checked below. So `SR̰(q_c) ≥ Q̰(q_c) ≥ D^{1/3}` for every admissible `c`, over **any field**.
  - For D < 27 this is weaker than 78.A's 3, so the specific floor of 3 remains **NOT FOUND**.
  - But §78.3's "Growth in `D` is still open" is wrong as written: growth at least `D^{1/3}` follows from a published theorem.
  - The statement "positive characteristic is untouched" is also wrong as written: the `D^{1/3}` bound holds in every characteristic.
- **78.B: NOT FOUND.** No source caps free combinatorial degenerations of `S_D`.

### Cited Findings
- **[BCLSZ] Briët–Christandl–Leigh–Shpilka–Zuiddam, *Discreteness of asymptotic tensor ranks*, Discrete Analysis 2025:15, arXiv:2306.01718v4** (viewed pp. 1–16, 19, 20 of 51). It is not in the repository: grep for "concise", "Briët" and "cube root" found nothing.
  - p. 9: *"Theorem 1.8. Let T ∈ F^{n1} ⊗ F^{n2} ⊗ F^{n3} be concise. Then Q̰(T) ≥ (min_ℓ n_ℓ)^{1/3}."*
  - p. 10: *"Theorem 1.8 does not rely on any special structure of the tensor T, unlike previous methods like the laser method that rely on T being tight."*
  - p. 10: *"Theorem 1.9. Let T ∈ F^n ⊗ F^n ⊗ F^n be concise and symmetric. Then Q̰(T) ≥ n^{1/2}."*
  - p. 13: *"We call T concise if R_ℓ(T) = n_ℓ for every ℓ ∈ [3]."*
  - p. 14: *"Q(T) ≤ SR(T) ≤ R_ℓ(T) ≤ R(T)"*.
  - p. 20, proof of Thm 2.10/2.11: *"Since the asymptotic subrank does not change under field extension [Str88, Theorem 3.10], we may assume that our base field F is infinite"*. So the bound holds over any field.
  - p. 11: *"Theorem 1.12. Suppose the limit SR̰(T) … exists. Then Q̰(T) ≥ SR̰(T)^{2/3}."*
  - p. 3: it names the W-tensor *"(which appears in the study of sunflower-free sets)"*. It never treats `S_D`.
  - — [arXiv:2306.01718](https://arxiv.org/abs/2306.01718)
- **[SDW26] Sakabe–Doğan–Walter, arXiv:2601.21553v2** (viewed pp. 1, 3, 5, 15 of 20).
  - p. 3, Corollary I.2: *"For every tensor t, the asymptotic slice rank can be computed as SR̰(t) = min_{g∈GL} τ̃(H_{g·t})."*
  - p. 1: *"We derive a novel formula for the asymptotic slice rank … as a minimum, over all basis choices, of the asymptotic vertex cover number"*.
  - This is a tool, not a competitor. The cited [ASU13] appears only generically on p. 2.
  - — [arXiv:2601.21553](https://arxiv.org/abs/2601.21553)
- **Not in [KL26]'s scope:** its abstract restricts to k ≥ 4 (abstract only).
- **Abstract-only screens, no claim found** (these support no negative): 2604.18283, 2609.06633, 2510.08336, 2012.14412, 2111.08262, 2609.13972, 2604.19872, 2503.22650, 2606.30593, 2308.07101.

### Inferences
- **Why `q_c` is concise (my check — verify before relying on it).**
  - In flattening 1, column `(x,x)` has entry `q_c(a,x,x)`. This is 1 if `a = x` (monochromatic). If `a ≠ x`, the triple has two equal letters, so it is neither monochromatic nor rainbow, and the entry is 0.
  - So the columns `(x,x)` form a `D×D` identity, and `R_1 = D`. The same holds for the other two flattenings by symmetry of `S_D`.
  - Hence `Q̰(q_c) ≥ D^{1/3}` for every `c`, including `c = 0`. When `c` is permutation-symmetric (e.g. NaSa's `c ≡ −1/2`), Thm 1.9 gives `≥ √D`.
- **What this does not do.** It does not give 3 for D ≤ 26, so it does not supersede 78.A at small D. Nor does it touch 78.B: conciseness / max-rank is not a combinatorial-degeneration argument, and it is exactly the kind of "other method" that §78.3(a) says could go further.
- **Recommended edits:**
  - Row B27 → PARTIAL, citing [BCLSZ] Thm 1.8.
  - §78.3: replace "growth in D is still open" with `D^{1/3} ≤ SR̰(q_c) ≤ D` for all `c` and all fields.

### Gaps
- **[BCLSZ]** pp. 17–18 and 21–51 were not viewed. In particular §5 (alternative proof) and §6 (slice rank vs. subrank) were not viewed.
- **[SDW26]** pp. 2, 4, 6–14 and 16–20 were not viewed.
- **Not reached:**
  - the 2026 survey *"Asymptotic spectra: Theory, applications, and extensions"*, which cites both CVZ18 and BCLSZ (S2 listing; no arXiv id);
  - 2609.17280 *Concise tensors with maximal symmetries* (cites BCLSZ);
  - Bürgisser's and Tobler's theses;
  - Strassen 1991.
- **ASU12 forward citations: FAILED** (Semantic Scholar 429 after 8 retries; OpenAlex daily budget exhausted).

## Audit trail (queries, date 2026-10-27, hit counts)

**arXiv API**, `sortBy=submittedDate`, hits filtered to ≥ 2016 for screening:

| Query | Hits |
|---|---|
| `all:sunflower AND all:intersecting` | 40 |
| `all:"sunflower-free"` | 13 |
| `all:"sunflower free"` | 13 |
| `all:"delta-system"` | 35 |
| `all:"Erdos-Rado"` | 10 |
| `all:"Erdős-Rado"` | 28 |
| `all:sunflower AND ("slice rank" OR subrank OR "asymptotic spectrum" OR "quantum functional")` | 7 |
| `all:"multicolored sunflower"` | 1 |
| `all:"vector sunflower"` | **0** |
| `all:sunflower AND (cat:math.CO OR cs.CC OR cs.DM OR math.AG OR quant-ph)` | 117 |
| `all:sunflowers` | 191 |
| `all:"quantum functionals"` | 177 |
| `"slice rank" AND (sunflower OR multicolored OR tricolored)` | 8 |
| `all:"asymptotic slice rank"` | 9 |
| `all:"combinatorial degeneration"` | 4 |
| `sunflower AND "matrix multiplication"` | 4 |
| `3-uniform AND intersecting AND sunflower` | 3 |

All titles since 2016 were screened. Already covered by the repository, so not re-read: 2610.26686, 2609.27044, 2609.18995, 2609.30263, 2606.02667, 2606.30593 (p. 1), 2510.19037, 2509.14790, 2508.20132.

**Semantic Scholar forward citations** (since 2016, titles screened):

| Paper | Citations |
|---|---|
| CVZ18 | 65 |
| ALWZ20 | 180 |
| NaSa17 | 69 |
| AHS72 | 442 total, 224 since 2016 |
| FPP odd-sunflowers | 2 |
| BCLSZ | 10 |
| FW25 | 3 — this listing surfaced Guo–Wang–Wu |
| ASU12 | failed |

Google Scholar was not attempted, because automated access is blocked.

**StackExchange API:**

| Site and query | Hits |
|---|---|
| MO "sunflower" | 16 |
| MO "delta-system" | 100+, mostly set-theory noise |
| MO "sunflower intersecting" | 1 (163689) |
| MO "slice rank sunflower" | 0 |
| MO "sunflower-free" | 2 |
| MSE "sunflower" | 31 |

Threads read in full with comments: MO 163689. Bodies and answers checked: MO 374016, 115069, 488358; MSE 248737, 3905334, 2991118, 4999838, 3829206. None of the others mention an intersecting reduction.

**Polymath10:** all 456 comments of posts 13306, 13347, 13400, 13447, 13932, 13405, 14293, 14329 and 13455. A regex for intersecting / star / maximal disjoint matched 40 of them, and all 40 were read in extracted HTML. The wiki was not fetched.

**Full or partial PDF reads (page images):**

| Paper | Pages viewed |
|---|---|
| [FW25] | 20/20 |
| [AxBCDN26] | 12/35 |
| [BCLSZ] | 18/51 |
| [SDW26] | 4/20 |

**Text-located only, no images, so no claims are made from them:** 1809.10318, 2301.04219, 2509.16355, 2610.30054, 2503.22650. A text search for "intersecting" returned 0 lines in each. That is a page locator, not evidence of absence.
