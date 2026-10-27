# B10 / B11 prior-art search: intersecting 3-sunflower-free families (ι) against the Erdős–Rado function (g)

Scope searched (session of 2026-10-27). Notation used throughout: `g(b)` is the maximum size of a b-uniform 3-sunflower-free family, and `ι(b)` is the maximum size of an *intersecting* one. Translations to other notations: in [AxBCDN26], `f(w,3)` is `g(w)` and `ψ(w,3,2)` is `ι(w)`. In [FW25], `m_k(2,…,2)` is `g(k)` and `m_k(1,2,…,2)` is `ι(k)`. In Polymath10, `f(k,3)` is the threshold, i.e. `g(k)+1`. Pálvölgyi's `f^{int}(k,3)` is `ι(k)`. On MathOverflow 163689, Mirko's `f(k)` is `g(k)` and his `g(k)` is `ι(k)`.

Sources newly read in this session:

- **[AxBCDN26]**: Axante, Budala, Chitic, Dumitru, Nacu, *Sunflower-Free Uniform Families: Recursive Constructions and Explicit Bounds*, arXiv:2609.06175v1 (5 Sep 2026). Downloaded, rendered at 150 dpi, and every page (35 of 35) viewed as an image. **Read in full.** Unrefereed preprint; its acknowledgments say it was produced in an AI-assisted workflow.
- **[FW25]**: P. Frankl, J. Wang, *New Bounds on Families Without Large Sunflowers*, Electron. J. Combin. 32(2) (2025) #P2.43. Open access PDF, 20 pages, rendered, and all 20 pages viewed as images. **Read in full.**
- **[Kos00]**: Kostochka, *Extremal problems on Δ-systems*, 9 pp. Same sha256 as the repository copy. Re-rendered, and all 9 of 9 pages viewed **for this claim**.
- **Polymath10 blog**: all comment threads of posts 13306, 13347, 13400, 13447, 13932, 13405 and 14293, plus 14329 (the ALWZ post), 6970, 65 and 13455. That is 485 comments, retrieved through `public-api.wordpress.com`. For every thread the API's `found` count equals the number of comments retrieved. Post bodies were also retrieved. Evidence class: **read through the API as text, with formula LaTeX taken from the `alt` attributes of the images.** These are blog comments, not PDFs, so rule 1 does not apply as written. The quotes below are verbatim from the API JSON.
- **MathOverflow**: questions 163689, 115069, 488358, 489839 and 374016, each with all its answers and comments, via the StackExchange API.

---

## Q1. Is the UPPER half `g(b) ≤ 2b·ι(b)` (or any `g ≤ poly(b)·ι(b)`) in print?

### Takeaway
**PARTIAL.** The inequality is not printed in exactly this form, `g ≤ 2b·ι`, under any of the vocabularies searched. However:

- (a) The argument is printed word for word on the Polymath10 blog in 2015, by Gowers, in a slightly different (Ramsey) framing.
- (b) The bound follows in two lines from two inequalities that are both in a refereed 2025 paper. Composing them gives the *stronger* chain `g(b) ≤ 2b·g(b−1) ≤ 2b·ι(b)`.

So no novelty can be claimed for the upper half. It is an immediate corollary of printed results.

### Cited Findings

- **The argument, word for word: Gowers, Polymath10 Post 2, comment 22417 (2015-11-12T21:16:27+03:00).** The question is *"if you have a collection of k-sets, how many do you need in order to guarantee that either three of them are disjoint or m of them form an intersecting family?"* His answer: *"The simple upper bound is around 2km. This one proves by taking a maximal disjoint subfamily, which contains at most two sets, and using the pigeonhole principle to find at least m sets that all contain the same element from the union of this subfamily. A simple lower bound is obtained by picking two disjoint intersecting families of size m−1."* — [gilkalai.wordpress.com, comment 22417](https://gilkalai.wordpress.com/2015/11/11/polymath10-post-2-homological-approach/#comment-22417).
  - A 3-sunflower-free family has no three disjoint members. A sub-star (the members through one point) of a sunflower-free family is itself intersecting and sunflower-free, so it has at most `ι(b)` members. Gowers's sentence therefore gives `g(b) ≤ 2b·ι(b)` immediately.
  - His lower-bound sentence is the doubling construction, i.e. the lower half.
  - He gave the same argument earlier, for k = 3 and general r, in Post 1 comment 22235 (2015-11-04): *"If there are no r disjoint sets, then there is a set of size at most 3(r-1) that intersects all the sets in the system, so there is an intersecting family of size at least n/3(r-1), so we get an upper bound of 3(r-1)m. One can also get a lower bound of (r-1)(m-1) just by taking r-1 disjoint intersecting families of size m-1."* — [comment 22235](https://gilkalai.wordpress.com/2015/11/03/polymath10-the-erdos-rado-delta-system-conjecture/#comment-22235).
  - In comment 22236 he calls it *"the trivial argument … pick a maximal disjoint collection of sets and take its union, and then use pigeonhole to get a family of sets that intersect in one point."*
  - **Caveat:** Gowers's object is the Ramsey function "three disjoint, or m intersecting". He never restricts to sunflower-free families and never writes `ι`. The step "star ⊂ sunflower-free ⇒ star ≤ ι" is not written in his comments.

- **The two ingredients, both printed and refereed: [FW25] p. 5, eqs. (13)–(14), rendered.** The text: *"If T is a transversal then |F| ⩽ Σ_{x∈T} |F(x)|. (13) If F_1,…,F_s ∈ F are pairwise disjoint and ν(F) = s, then F_1 ∪ … ∪ F_s is a transversal of F. Thus, m_k(r⃗) ⩽ k r_0 · m_{k−1}(r_1,…,r_{k−1}). (14)"*
  - At `r⃗ = (2,…,2)` this is `g(b) ≤ 2b·g(b−1)`, the Erdős–Rado step.
  - [FW25] p. 5, eq. (12): *"m_{k+1}(s, r_0,…,r_{k−1}) ⩾ s m_k(r⃗)"*. At `s = 1` this is the cone, `ι(b) ≥ g(b−1)` (see Q3).
  - Composing (14) with (12) at s = 1 gives `g(b) ≤ 2b·g(b−1) ≤ 2b·ι(b)`.
  - [FW25] does not write the composition. It uses (14) only to derive `m_k ≤ k! r_0⋯r_{k−1}` (eq. (15)). — [FW25, EJC](https://doi.org/10.37236/13277)

- **The same Erdős–Rado step at r = 3, explicitly: MathOverflow, comment 417972 by "Mirko" (2014-04-20) on question 163689.** The comment: *"If F is a k-uniform family with f(k)=|F| then there must be two disjoint sets A,B∈F … Then every C∈F meets A or B. … For every i≤k at most f(k−1) many members of F contain i, and one of these is A. Hence f(k)≤2(1+k(f(k−1)−1))"*. Mirko's `f` is `g`. — [MO 163689](https://mathoverflow.net/questions/163689)

- **A different upper bound with ι as a summand: [AxBCDN26] p. 29, Theorem 6.9, rendered.** The proof reads: *"If two members of D_F(R) were disjoint, those two members and R would form a sunflower with empty core. Hence D_F(R) is intersecting. By propositions 6.5 and 6.8, |F| = |N_F[R]| + |D_F(R)| ≤ 56 + 27 = 83."*
  - Here `D_F(R)` is the set of members disjoint from R.
  - The general principle is `g(b) ≤ max_R |N_F[R]| + ι(b)`. This is an additive bound, not a `2b·ι` bound.
  - p. 22 states the plan as: *"The members disjoint from R pairwise intersect, so their number is at most ψ(4,3,2)."* — [arXiv:2609.06175](https://arxiv.org/abs/2609.06175)

- **No printed `g ≤ c·b·ι` was found in any other source checked:**
  - [Kos00] pp. 1–9: no intersecting-side extremal function at all, only the intersecting AHS construction on pp. 2–3.
  - [FW25] pp. 1–20.
  - [AxBCDN26] pp. 1–35.
  - All 485 Polymath10 comments.
  - MO 163689, 115069, 488358, 489839 and 374016.

### Inferences
- The upper half carries no novelty. It is "trivial argument" folklore (Gowers 2015). Its decomposition `g(b) ≤ 2b·g(b−1)` together with `g(b−1) ≤ ι(b)` is printed in a refereed journal ([FW25] eqs. (12) and (14)).
- The repository's own route (the star at the most popular point is intersecting and sunflower-free) is exactly Gowers's pigeonhole route.
- The intermediate `g(b−1)` is never larger than `ι(b)`. That means `2b·g(b−1)` is a bound at least as good as `2b·ι(b)`. The repository may want to record that `g_le_iota_scaled` factors through the cone.

### Gaps
- **[AHS72]: still unreachable** (attempts below). [Kos00] p. 2, rendered, says AHS improved the upper bound to *"(k+1)!((r−1+√(r²+6r−7))/4)^k"*. The factor `(k+1)!` is the signature of a cone reduction to intersecting families. Kalai (comment 22224, below) attributes an intersecting-family improvement for r = 3 to *"Noga Alon … as a student and it was observed earlier too, perhaps by Abbot"*. **[AHS72] is therefore the single most likely place where an intersecting reduction is printed in a refereed source.** It could not be read.
- **Abbott–Hanson 1974 (Discrete Math. 8, 1–12; the source of ψ per [AxBCDN26]) and 1977: unreachable** (attempts below).
- **Polymath10 wiki: unreachable.** The correct page is `michaelnielsen.org/polymath1/index.php?title=The_Erdos-Rado_sunflower_lemma` (the URL is in a Polymath10 comment). The host returns 404 or a connection reset. The Wayback Machine has a snapshot from 2020-02-27, but `web.archive.org` is "Blocked by egress policy" in this container.

---

## Q2. Is the two-sided chain, or the k = 3 equivalence "sunflower conjecture ⟺ ι(b) ≤ C^b", in print?

### Takeaway
**FOUND in substance, not as a formal statement.**

- Gil Kalai stated the operative direction in 2015 on the Polymath10 blog: a bound for the intersecting case transfers to the general case by the cone. The reverse direction is trivial. The equivalence is therefore in print as a remark.
- Kalai also says intersecting families are "surprisingly … useful" for the general r = 3 problem.
- The full two-sided chain `2ι ≤ g ≤ 2bι` does not appear as one display. Both halves do appear side by side, in Gowers's Ramsey framing (22235 and 22417).

### Cited Findings
- **Kalai, Polymath10 Post 1, comment 22224 (2015-11-04T08:36:51+03:00), replying to Pálvölgyi:** *"Also an upper bound k! for the intersecting case gives you an upper (k+1)! for the general case since for any collection without delta system of size r you get an intersecting family by adding a new element to your ground set and then adding it to all the sets. This last "cheap" argument of moving to intersecting families suggests it might be not be useful at all. But surprisingly it is useful to think about the problem for intersecting families and this allow to improve for r=3, the 2^k k! bound to (√2)^k k!. (Noga Alon observed this argument as a student and it was observed earlier too, perhaps by Abbot.)"* — [comment 22224](https://gilkalai.wordpress.com/2015/11/03/polymath10-the-erdos-rado-delta-system-conjecture/#comment-22224)
  - The same comment gives the recursion for the intersecting function: *"Let f(k) be the maximum number of k-sets in a family with no 3-delta system in which every two sets intersect. Then f(2)=3. … f(k) ≤ 1+Σ_{i=1}^{k−1} C(k,i) f(k−i)"*.
  - So `ι` was *named* in this comment, 2015-11-04. That is seven weeks before Pálvölgyi's 23193 (2015-12-23).
- **Gowers, Post 1, comment 22214 (2015-11-03):** *"If we know, for example, that there is some element that belongs to all the sets, then the problem reduces from estimating f(k,r) to estimating f(k-1,r). … is it the case that if you insist that your family of sets is an intersecting family, then you can't do much better than f(k-1,r)?"* This poses whether `ι(k) ≈ g(k−1)`. — [comment 22214](https://gilkalai.wordpress.com/2015/11/03/polymath10-the-erdos-rado-delta-system-conjecture/#comment-22214)
- **Kalai, comment 22216 (2015-11-04):** *"looking at intersecting collections is indeed a trick to get some improvement on the original upper bound (for all collections)."*
- **[FW25] p. 18, Conjecture 7.2, rendered.** It covers vectors `r⃗ ∈ {1,2}^{p+1}` with *"r_i = 2 for exactly k values of i where k > p/10 … m_p(r⃗) < c^k"*. Taking `r_0 = 1, r_1..r_{p−1} = 2` gives an exponential bound on `ι(p)` (k = p−1 twos). [FW25] calls this a generalisation of (42), the Erdős–Rado conjecture `m_k(2,…,2) < c^k`. They do **not** state the converse or the equivalence. — [FW25](https://doi.org/10.37236/13277)

### Inferences
- `ι(b) ≤ C^b ⇒ g(b) ≤ ι(b+1) ≤ C^{b+1}` is Kalai's 22224 sentence with "k!" replaced by "C^k". `g ≤ c^b ⇒ ι ≤ c^b` is trivial.
- The equivalence `conjecture_k_3_iff_iota_exponential` is therefore folklore since at least November 2015. What the repository adds is the machine-checked statement, not the mathematics.
- It is cleaner to cite the cone route (Kalai 22224; [FW25] (12)) than the `2b·ι` route, because the cone gives the equivalence with constant `C` rather than `2C`.

### Gaps
- No refereed paper states the equivalence in so many words, in any source read. [AHS72], AH74 and AH77 could not be read (see Q1).

---

## Q3 (B11). Is the cone `g(b−1) ≤ ι(b)` in print?

### Takeaway
**FOUND, verbatim, in three independent sources:** a 2015 blog comment by Kalai, a refereed 2025 paper (in vector form), and a 2026 arXiv preprint (as a named lemma). This upgrades B11 from "technique found; exact statement not found" to **FOUND**.

### Cited Findings
- **Kalai, Polymath10 comment 22224 (2015-11-04):** *"for any collection without delta system of size r you get an intersecting family by adding a new element to your ground set and then adding it to all the sets."* — [comment 22224](https://gilkalai.wordpress.com/2015/11/03/polymath10-the-erdos-rado-delta-system-conjecture/#comment-22224)
- **[FW25] p. 5, eq. (12), rendered:** *"Applying (11) with ℓ = 1, m_1(s) = s yields m_{k+1}(s, r_0,…,r_{k−1}) ⩾ s m_k(r⃗). (12)"*. At `s = 1` and `r⃗ = (2,…,2)` this is `ι(k+1) ≥ g(k)`. — [FW25](https://doi.org/10.37236/13277)
- **[AxBCDN26] p. 6, Lemma 3.3 ("Star and split"), eq. (3.4), rendered:** *"ψ(w,k,2) ≥ f(w−1,k)"*. The proof: *"take an extremal (w−1)-uniform family with f(w−1,k) members and add one new point to every member. The resulting family has the same size and is intersecting. Deleting the new point from a sunflower would give a sunflower in the original family, so the resulting family is counted by ψ(w,k,2)."*
  - p. 6 also says: *"For k ≥ 4, Frankl and Wang proved ψ(3,k,2) = f(2,k) [13, Theorem 1.15]. Thus the star bound equation (3.4) is tight when w = 3."* — [arXiv:2609.06175](https://arxiv.org/abs/2609.06175)
- **Related, MO 374016, domotorp (Pálvölgyi) comment:** *"take two disjoint copies of it, F1 and F2, and add a new point x, such that you append x to every set from F1 and F2."* This is the cone applied to a doubled family, in the diverse-family setting. — [MO 374016](https://mathoverflow.net/questions/374016)
- **MO 163689, Mirko comment 418082 (2014-04-21):** *"Clearly g(k+1)≥2g(k)"*. In his notation this is `ι(k+1) ≥ 2ι(k)`, i.e. cone composed with doubling.

---

## Q4. The lower half, `2ι(b) ≤ g(b)`, is older than Pálvölgyi 2015 (recorded because it changes an attribution)

### Takeaway
**FOUND earlier, on secondary evidence for 1974 and primary evidence for 2014.**

### Cited Findings
- **[AxBCDN26] p. 23, Proposition 6.1(i), rendered:** *"Every intersecting, 3-uniform family without a 3-sunflower has at most 10 members … Part (i), due to Abbott and Hanson [4, p. 9], follows directly from equations (3.5) and (6.1), which give 20 = f(3,3) ≥ 2ψ(3,3,2)."*
  - p. 6: *"The second [inequality, (3.5) `f(w,k) ≥ ψ(w,k,k−1)+ψ(w,k,2)`] is a case of the Abbott–Hanson disjoint-support split [4]."*
  - p. 3: *"This matching-constrained quantity [ψ(w,k,m)] was introduced by Abbott and Hanson [4]. In particular, ψ(w,k,2) is the maximum over intersecting w-uniform families without a k-sunflower."*
  - [4] = Abbott–Hanson, *On finite Delta-systems*, Discrete Math. 8 (1974) 1–12 (p. 34, rendered).
  - **Rule 4: this is a 2026 preprint's description of a 1974 paper. It is not first-hand.**
- **[FW25] p. 4, Remark, rendered:** *"Let us mention that m_3(1,2,2) = 10 along with m_3(2,2,2) = 20 was proved by Abbott and Hanson [2]."* Here [2] = AH74, per p. 19. This is a second, independent secondary attribution: `ι(3) = 10` and `g(3) = 20` are both credited to AH74.
- **MO 163689, Mirko comment 418082 (2014-04-21), primary via API:** *"How big could a k-uniform family G be if it contains no 3-sunflower and every two of its elements do intersect? … Make this a function g(k) … f(k)≥2g(k)"*. This names `ι` and states the lower half 19 months before Polymath10.
- **Polymath10, GFP comment 22690 (2015-11-25):** *"I also require that the family is intersecting. One could obtain a usual sunflower-free family by 'duplicating the family'."*

### Inferences
- The repository's attribution of `ι`'s naming and of `2ι ≤ g` to Pálvölgyi 23193 (row A17) is too late. Two earlier primaries: Kalai 22224 (2015-11-04) named the intersecting function, and Mirko on MO 163689 (2014-04-21) named it and stated `f ≥ 2g`. Two independent secondaries trace `ψ`, `ι(3) = 10` and the doubling to Abbott–Hanson 1974.

---

## Side finding the caller must see (outside B10, directly on the repository's ι(4) search)

- **[AxBCDN26] p. 28, Proposition 6.8, rendered:** *"One has ψ(4,3,2) = 27."*
  - Proposition 6.7: *"Every intersecting, 4-uniform family without a 3-sunflower has at most 27 members."* The proof is computer-assisted: nauty canonical augmentation, *"11,720 depth-6 roots … 105,917,089,577 search-tree nodes and finds no 28-member family"*.
  - The lower bound is attributed to *"the construction of Abbott and Hanson [4, p. 9]"*, which is the `C₃ ≀ C₃` / `Product.iota4` family.
  - **That is `ι(4) = 27`, claimed as settled in Sept 2026.** It contradicts the repository's row A19c ("ι(4) not known … `[27, 71]`").
  - The claim is unrefereed and computer-assisted. Section 8 (p. 32) says these exhaustive computations *"are checked separately"* from the Lean development.
- **Same paper, p. 29, Theorem 6.9:** `54 ≤ f(4,3) ≤ 83`. In the repository's convention that is `54 ≤ g(4) ≤ 83`. It also gives `f(3,4) ≤ 49`. p. 2, Table 1 lists the previously published `f(4,3) ≤ 142 [3]`.
- [AxBCDN26] p. 2 links code, data and a Lean development at `github.com/bogdan27182/sunflower-paper`. **Not fetched.**

---

## Sources: evidence class and attempts

| Source | Class | Notes |
|---|---|---|
| [AxBCDN26] arXiv:2609.06175v1 | **read in full, 35/35 pages rendered and viewed** | `pdftotext` was used only to locate section pages |
| [FW25] EJC 32(2) P2.43 | **read in full, 20/20 pages rendered and viewed** | downloaded from combinatorics.org (open access) |
| [Kos00] | **read in full for this claim, 9/9 pages viewed** | sha256 `ab75a3f3…94d9d`, the same as the repository copy |
| Polymath10 blog, 11 posts and 485 comments | **read in full as API text** | `found` counts matched retrieval (143, 127, 104, 12, 37, 6, 5, 11, 10, 19, 11). Grepped for `intersecting`, and the ±1-day neighbourhood of 22224 was read |
| MO 163689, 115069, 488358, 489839, 374016 | **read in full via API** | question bodies, all answers, all comments |
| Polymath10 wiki (`The_Erdos-Rado_sunflower_lemma`) | **unreachable** | michaelnielsen.org gave 404 and a connection reset (proxy log: `ws_closed_mid_exchange`). The Wayback snapshot of 2020-02-27 exists per `archive.org/wayback/available`, but `web.archive.org` is blocked by egress policy and WebFetch is refused there too |
| [AHS72] JCTA 12, 381–389 | **unreachable** | **New:** OpenAlex and Semantic Scholar now report `is_oa: true, oa_status: "bronze"` (the Elsevier open archive). That contradicts the repository's earlier "closed". However, sciencedirect.com returns 403 with a Cloudflare block on both the article page and the `/pdfft` endpoint, and `api.elsevier.com` returns 406 without an API key. A browser outside this container might reach the open-archive PDF |
| Abbott–Hanson 1974, Discrete Math. 8 (`10.1016/0012-365X(74)90103-4`) | **unreachable** | OpenAlex says bronze OA. Same ScienceDirect/Cloudflare block (not separately attempted beyond the OA lookup). **This is the paper both secondaries credit with ψ, ι(3) = 10 and the doubling.** It is the top acquisition priority |
| Abbott–Hanson 1977, Discrete Math. 17 | **unreachable** | OpenAlex says bronze OA; same block |
| Erdős–Szemerédi 1978, Deza–Frankl, Füredi 1978 | **not attempted this session** | Füredi 1978 was already read by the repository (row A15). The time went to the three new primaries above |
| GitHub `bogdan27182/sunflower-paper` | **not attempted** | — |

Vocabulary covered across the sources read: sunflower, Δ-system / delta system, star, kernel, intersecting, pairwise intersecting, matching number ν, transversal / cover τ, ψ(w,k,m), m_k(r⃗), f^{int}, "dummy"/"new element", "duplicating". Not separately searched this session: "weak sunflower", "clique", "s-star". These were covered for [Kup25], [Fü83] and [FF85] by earlier rows.

Pages not viewed: **none** in the three PDFs read this session.
