# B27 prior-art search: slice rank of the vector-sunflower tester (Lemmas 78.A and 78.B)

Claim checked (`docs/reading.md` row B27, `docs/roadmap.md` §78.2):
- **Lemma 78.A.** For every D ≥ 3 and every c that is nonzero on rainbow tuples, the asymptotic slice rank over C of BHL's single-letter tester q_c (support S_D) is at least 3, with equality at D = 3. This is the "c-independent floor of 3".
- **Lemma 78.B.** Every free combinatorial degeneration Φ of a sub-box of S_D has at most 3 letters per coordinate and at most 9 elements, so max_P min_j H(P_j) ≤ log₂ 3. This is "the technique stops at 3".

Method: downloads went into separate directories under `/tmp/claude-0/-home-user-sunflower-formal/1ebb4a50-96a0-5685-9f5c-ab90eb4993e3/scratchpad/dr_novelty/b27/`, and every Python call that read them used `python3 -I`. PDFs were rendered with `pdftoppm -png -r 150`. pdftotext was used only to find which pages carry prose words ("sunflower", "Naslund", "cap set", "slice rank", "subrank", "Trägerfunktional" and similar). Every quotation below was copied from a rendered page image. The one exception is ST16, a blog post; its text comes from the WordPress JSON, with formulas taken from the LaTeX `alt` text, which is the same method the repository used before.

## Q1. Is Lemma 78.A, or an equivalent lower bound for the sunflower / vector-sunflower / multicolored-sunflower tensor, in print?

### Takeaway
**NOT FOUND.** No source examined states a lower bound on the slice rank, subrank, quantum functional or support functional of a tensor supported on S_D (the vector-sunflower / multicolored-sunflower support). No source states a coefficient-independent floor of 3 in characteristic 0. The closest published items are:
- (a) the general machinery: CVZ18 (already in the repository) and its 2026 strengthening SDW26;
- (b) asymptotic slice-rank values for *other* sunflower-related tensors: the W-tensor (set sunflowers, value 2^{h(1/3)}) and the Naslund–Sawin {0,1} tensor (value 3/2^{2/3}). These are PARTIAL analogues, not the claim.

### Cited Findings
- **ST16 is now finished.** Remainder read, from the statement of Prop. 6 to the end: Props. 6–11, Remark 8, and the closing remark on rotations. ST16 Prop. 6 gives a lower bound valid over **any** field, using the maximal elements of the support under chosen total orders. Verbatim: *"Now suppose that the coefficients ${c_{s_1,\dots,s_k}}$ are all non-zero and that each of the ${S_j}$ are equipped with a total ordering ${\leq_j}$. Let ${\Gamma'}$ be the set of maximal elements of ${\Gamma}$ in the product ordering … Then $\hbox{rank}(v^{\otimes n}) \geq \exp( (H' + o(1)) n )$"*. [Sawin–Tao, "Notes on the slice rank of tensors", What's New, 24 Aug 2016](https://terrytao.wordpress.com/2016/08/24/notes-on-the-slice-rank-of-tensors/)
  - The worked examples are the cap-set tensor over F_3 (Prop. 9, H* ≈ 1.013445) and the Naslund–Sawin tensor over C. Verbatim, Prop. 10: *"the function ${(x,y,z) \mapsto \prod_{i=1}^n (x_i+y_i+z_i)-1}$ from ${\{0,1\}^n \times \{0,1\}^n \times \{0,1\}^n \rightarrow \mathbb C}$ … has slice rank ${(3/2^{2/3})^n e^{o(n)}}$"*.
  - Prop. 11 covers k ≥ 8 arithmetic-progression tensors: *"Then the slice rank of ${F}$ is ${|G|}$."*
  - No vector-sunflower / S_D tensor appears anywhere in the post. Same source as above.
- **SDW26 (read in full, 20/20 pages, arXiv:2601.21553v2, 2 Oct 2026).** It proves Strassen's upper support functionals equal the quantum functionals for every complex tensor.
  - p. 3, Theorem I.1: *"For every tensor t and every θ ∈ Θ, F_θ(t) = ζ^θ(t). In particular, Strassen's support functional is a universal spectral point in the asymptotic spectrum of tensors."*
  - p. 3, Corollary I.2: *"For every tensor t, the asymptotic slice rank can be computed as SR̃(t) = min_{g∈GL} τ̃(H_{g·t})."*
  - p. 3: *"Previously, such a formula was only known for free tensors [CVZ18], [CLZ23]."*
  - Its only sunflower content is a bibliography entry for ASU13 (p. 19), cited on p. 2 as an application area (*"additive combinatorics [ASU13], [Tao16], [TS16], [BCC+17], [KSS18]"*).
  - No sunflower tensor or S_D is evaluated.
  - [Sakabe–Doğan–Walter, "Strassen's support functionals coincide with the quantum functionals"](https://arxiv.org/abs/2601.21553)
- **CVZ discreteness paper (Discrete Analysis 2025:15; rendered p. 3 only).** It records the published asymptotic slice rank of the *set*-sunflower W-tensor. Verbatim: *"the asymptotic slice rank of the W-tensor (which appears in the study of sunflower-free sets) equals 2^{h(1/3)} ≈ 1.889 [Str91], where h is the binary entropy function, and the asymptotic slice rank of the cap set tensor … is known to be the non-integral value ≈ 2.755 over the finite field F_3 [EG17, Tao16, KSS18, Str91]."* This tensor is not S_D, and the statement is not a c-independent floor. [Christandl–Gesmundo–Zuiddam(-Lysikov et al.), "Discreteness of asymptotic tensor ranks", arXiv:2306.01718](https://arxiv.org/abs/2306.01718)
- **KMZ (Geometric rank), p. 6, rendered.** The sunflower problem is mentioned only as an upper-bound application. Verbatim: *"The Erdős–Szemerédi sunflower problem for three petals was resolved by Naslund and Sawin [NS17] by similarly considering the strong powers of the hypergraph consisting of the edge (1,1,2) and permutations. In both cases slice rank was used to obtain the upper bound."* [Kopparty–Moshkovitz–Zuiddam, "Geometric rank of tensors and subrank of matrix multiplication", arXiv:2002.09472](https://arxiv.org/abs/2002.09472)
- **Wigderson–Zuiddam survey (2025 Bulletin version; rendered pp. 1, 30–32, 95–97).**
  - pp. 30–31 mention the sunflower problem only as motivation for the k-graph semiring, with the cap set as the worked example.
  - p. 96: *"for every tensor T the minimum min_θ ζ^θ(T) is equal to the asymptotic slice rank of T"*. The survey also states that the support functionals are spectral points *"of oblique tensors"*.
  - No sunflower tensor is evaluated on those pages.
  - [Wigderson–Zuiddam, "Asymptotic spectra: theory, applications and extensions"](https://www.math.ias.edu/~avi/PUBLICATIONS/Wigderson_Zuiddam_Final_2025.pdf)
- **Bürgisser's thesis (read in full, 26/26 rendered pages).** "Degenerationsordnung und Trägerfunktional bilinearer Abbildungen", Konstanz 1990, 24 numbered pages. Contents:
  - the typical value of the lower support functional for generic tensors (p. 9, Satz 2.8: *"Der typische Wert des logarithmischen unteren Trägerfunktionals ρ_θ verhält sich asymptotisch wie (1 − min_i θ_i) log n für n → ∞."*);
  - the lower support functional is not additive (p. 10, Satz 3.1);
  - the degeneration order does not extend to the ring (p. 13, Satz 4.4);
  - rationality of degeneration (§5).
  - No sunflower, cap-set or S_D tensor appears.
  - [KOPS urn:nbn:de:bsz:352-opus-20311](http://nbn-resolving.de/urn:nbn:de:bsz:352-opus-20311)
- **Tobler's thesis.** "Spezialisierung und Degeneration (von Tensoren)", Dissertation Konstanz, June 1991, 44 numbered pages, 46 PDF pages. The title page, p. 2 (PDF), says *"Dissertation, Universität Konstanz, Juni 1991"*. Read: PDF pp. 2–8 (title, contents, §1–2), 19–20, 23–24 (§3.3–3.4) and 46 (bibliography).
  - p. 4 (printed) defines the upper support functional ζ^θ as min over bases and the lower support functional ζ_θ via *"max supp_C t … maximalen Punkte"*.
  - p. 4: *"Gibt es für eine Menge Φ ⊆ m×n×p ganzzahlige injektive Abbildungen α, β, γ … so dass α(i)+β(j)+γ(ℓ) auf Φ Null ist, so ist Φ offensichtlich bis auf Koordinatenpermutationen eine Antikette. Tensoren, deren Träger bezüglich einer Basis diese Eigenschaft haben, heissen straff"* (tight).
  - p. 21, Satz 3.3.6: *"ζ^θ(c) ≤ ζ^θ(a)"* under specialisation.
  - p. 22, Satz 3.4.1: generic tensors with θ-good supports.
  - The rest is two-slice tensors (Kronecker normal form).
  - No sunflower or S_D tensor in the pages read.
  - [KOPS handle 123456789/6235, urn:nbn:de:bsz:352-opus-20324](http://kops.uni-konstanz.de/handle/123456789/6235)
- **Corner-free sets paper, p. 5, rendered.** Combinatorial degenerations are used to build induced matchings for the multicolored sunflower problem, not to bound slice rank. Verbatim: *"Combinatorial degeneration was used more broadly to construct large induced matchings in the setting of important combinatorial problems, namely the Sunflower problem by Alon, Shpilka and Umans [4, Lemma 3.9] and the Cap Set problem by Kleinberg, Sawin and Speyer [31]."* [Christandl–Fawzi–Ta–Zuiddam, "Larger corner-free sets from combinatorial degenerations", arXiv:2111.08262](https://arxiv.org/abs/2111.08262)

### Inferences
- Lemma 78.A at D = 3 says: every complex tensor whose support is {(a,b,c) : a+b+c ≡ 0 mod 3} (S_3 relabelled) has asymptotic slice rank 3. Over F_3 the cap-set tensor has this support and value ≈ 2.755 (quoted above). So the floor cannot be a support-only statement over all fields, and that is consistent with it not appearing in the field-independent ST16 Prop. 6 machinery.
  - The ingredients are CVZ18's characteristic-0 lower bound for free supports, which the repository has already read, and now SDW26's equality F_θ = ζ^θ.
  - The specific consequence, a floor of 3 for every c on S_D, was not found anywhere.
- SDW26 (Oct 2026) gives a new published route to the same quantity: SR̃(q_c) = min_g τ̃(H_{g·q_c}), where τ̃ is the asymptotic vertex cover of the support hypergraph. If the repository cites a formula for SR̃_C, this is the current statement, and it holds for all tensors, not only free ones. It does not by itself give Lemma 78.A, because a lower bound still has to control every basis g. CVZ18 Thm. 4.20, as already used, is the step that does this for free supports.

### Gaps
- **Strassen 1991** (Crelle 413:127–180, doi:10.1515/crll.1991.413.127) could not be obtained.
  - doi.org resolves to degruyterbrill.com, which returned HTTP 202 (an HTML challenge, no PDF).
  - DigiZeitschriften `id/243919689_0413` returned 404.
  - Strassen's Konstanz home page links only to an obituary, Jo60_long.pdf and the 2012 Grenoble slides.
  - A web search found no open copy.
  - Its content is known here only through the quotations above (W-tensor value 2^{h(1/3)} attributed to it; support functionals defined on oblique tensors). That is second-hand and is not evidence about its text.
- **Tobler's thesis pp. 9–18 and 25–45 (PDF pages) were not viewed.** They contain §3.1–3.2 (specialisation and degeneration) and §4 (two-slice tensors). Their topics are listed on the rendered contents page and do not concern combinatorial supports.
- **Not viewed:**
  - KMZ pp. 1, 2, 7 (the image request limit failed);
  - Corner-free sets pp. 1, 7–9 (same failure);
  - Corner-free sets pp. 2–4 and 10–26 (not rendered).
  - pdftotext places "sunflower" in those papers only at KMZ pp. 1, 2, 6 and 24 (bibliography) and corner-free pp. 5, 7, 24 and 26 (bibliography). pp. 5 and 6 were read.
- **Not viewed: the remaining ~30 CVZ18-citing arXiv papers.** They were downloaded and word-located only, and "sunflower" occurs in them only in introductions or bibliographies (list in Q3). A word-location negative is the weak kind under rule 2; it says nothing about formulas.
- **Semantic Scholar citations of ASU12 could not be listed.** The DOI lookup returned 0 rows, and a later query was rate-limited (HTTP 429). Citations of NaSa17 and CVZ18 *were* listed.

## Q2. Is Lemma 78.B, or a cap on combinatorial-degeneration / free-support lower bounds for the sunflower support, in print?

### Takeaway
**NOT FOUND.** No source bounds how far free combinatorial degenerations of S_D, or of any sunflower support, can push the CVZ18/Strassen lower bound. The published uses of combinatorial degeneration on sunflower supports build *induced matchings* (ASU12 Lemma 3.9, which the repository has read). They are not used to cap slice-rank lower bounds.

### Cited Findings
- Combinatorial degeneration is defined, and is used for induced matchings in the multicolored sunflower problem (ASU) and in KSS, rather than for slice-rank lower bounds. Corner-free sets paper p. 5, verbatim: *"for sets Φ ⊆ Ψ ⊆ I_1 × ··· × I_k we say that Φ is a combinatorial degeneration of Ψ, and write Ψ ⊵ Φ, if there are maps u_i : I_i → Z such that for every x … if x ∈ Ψ∖Φ, then Σ u_i(x_i) > 0, and if x ∈ Φ, then Σ u_i(x_i) = 0."* [arXiv:2111.08262](https://arxiv.org/abs/2111.08262)
- Tobler (p. 21) defines "θ-gut" and "bequem" supports: those containing an antichain Φ with H_θ(Φ) = H_θ(Ψ), or carrying a uniform-marginal distribution. Verbatim: *"Wir nennen Ψ bequem, wenn ein Φ ⊂ Ψ und eine Wahrscheinlichkeitsverteilung P auf Φ existieren, so dass Φ wie oben eine Antikette ist und P gleichverteilte Marginalverteilungen hat."* This is the nearest published notion to Lemma 78.B's object. It is applied to generic tensors only, and no cap for any specific support is stated. [Tobler 1991, KOPS](http://kops.uni-konstanz.de/handle/123456789/6235)
- In ST16 (finished), the closing remark concerns which binary sequences appear for k-term progressions. No statement limits ordering or degeneration bounds on sunflower supports. [ST16](https://terrytao.wordpress.com/2016/08/24/notes-on-the-slice-rank-of-tensors/)

### Inferences
- Lemma 78.B is a statement about one support (S_D) and one technique, so its absence from general-theory papers is expected. The repository's "new to this repository" label stays appropriate.
- The repository's §78.3 note that the maximal-element bound (ST16 Prop. 6) is "capped at 9" is not contradicted by anything found.

### Gaps
- Strassen 1991 §§ on support functionals and M-degeneration (Strassen's "[46, Section 6]" in the corner-free paper is a different Strassen paper, 1987) could not be read. See Q1 Gaps.
- No source names "vector sunflower" together with "free" or "tight" support.

## Q3. Coverage ledger (evidence class per source, this pass)

### Takeaway
Read in full: SDW26 (20/20), Bürgisser's thesis (26/26), the remainder of ST16. The other sources were read on the page ranges listed. Strassen 1991 was unreachable. In addition, 36 CVZ18-citing arXiv PDFs and 8 sunflower/slice-rank PDFs were word-located only.

### Cited Findings
| Source | Evidence class |
|---|---|
| ST16, Sawin–Tao blog post 9271 | **Remainder read**: from the statement of Prop. 6 through the end (my conversion lines 170–430; the repository's earlier pass read the post's opening through Prop. 6). [link](https://terrytao.wordpress.com/2016/08/24/notes-on-the-slice-rank-of-tensors/) |
| SDW26, arXiv:2601.21553v2 | **Read in full, 20/20 rendered pages.** |
| Bürgisser thesis, 1990 | **Read in full, 26/26 rendered pages.** |
| Tobler thesis, 1991 (46 PDF pp.) | **Read PDF pp. 2–8, 19–20, 23–24, 46.** Not viewed: PDF pp. 1, 9–18, 21–22, 25–45. |
| Wigderson–Zuiddam survey (133 pp.) | **Read pp. 1, 30–32, 95–97**, located by word search for sunflower / slice rank / support functional / tight / free. Not viewed: p. 29 (rendered but not viewed), and all other pages. |
| KMZ, arXiv:2002.09472 | **Read p. 6.** pp. 1, 2, 7 rendered but not viewed (image request limit); others not rendered. |
| Corner-free sets, arXiv:2111.08262 | **Read p. 5.** pp. 1, 7, 8, 9 not viewed (request limit); pp. 2–4, 6, 10–12 rendered but not viewed; 13–26 not rendered. |
| Discreteness, arXiv:2306.01718 | **Read p. 3.** |
| Strassen 1991, Crelle 413 | **Unreachable.** Attempts: doi.org → De Gruyter (HTTP 202 challenge page); DigiZeitschriften (404); Strassen's Konstanz page (no link); web search. |
| CVZ18-citing arXiv papers (36), from the [Semantic Scholar](https://api.semanticscholar.org/graph/v1/paper/arXiv:1709.07851/citations) citation list | **Word-located only** (pdftotext, per page): 1807.05130, 1811.05511, 1812.06952, 1812.08731, 1905.03148, 1905.07355, 1909.09518, 2002.08435, 2003.03019, 2004.01492, 2008.11108, 2012.04679, 2012.14412, 2104.01130, 2110.01684, 2201.03615, 2205.15168, 2212.01668, 2212.12219, 2307.06115, 2307.07394, 2311.02190, 2404.06427, 2409.01130, 2411.15789, 2503.22633, 2503.22650, 2507.13778, 2511.12064, 2604.18283, 2605.21738, 2610.30054. In every one, "sunflower" occurs only in introduction or bibliography lines (contexts printed for 1905.07355, 2012.14412, 2104.01130, 2205.15168, 2212.01668, 2306.01718, 2604.18283). |
| Sunflower / slice-rank papers from the NaSa17 citation list and arXiv API searches | **Word-located only**: 2308.07101 (Karam, "Small sunflowers and the structure of slice rank decompositions": sunflowers of subspaces in decompositions, not the sunflower tensor), 2606.30593 (Ahmadi, triangular tensors, set sunflowers, upper bound), 2408.02328 (Croot–Lev–Pach survey), 1702.02831 (Hegedüs), 1512.00525 (Mubayi–Wang), 2604.19872 (Chang–Gesmundo–Zuiddam border subrank; p. 3 says *"higher order analogs k[t]/(t^k) arise in the sunflower problem [NS17]"*, per extracted text only). |
| BHL26 (2610.26686), KL26 (2609.27044) | **Already read in full by the repository** (`docs/references.md`). Re-surfaced by the citation search; not re-read. |

arXiv API searches returned no hits for `abs:"multicolored sunflower"` or for `abs:sunflower AND abs:"asymptotic spectrum"`. The hits for `abs:sunflower AND abs:tensor` / `abs:rank` are those listed in the table.

### Inferences
- Of the sources the brief named as priorities, Bürgisser and Tobler are now covered (Bürgisser in full, Tobler partially), and ST16 is finished. Strassen 1991 remains the one unread primary source. It is the original home of support functionals and of the W-tensor value. A W-tensor computation would be the nearest published analogue, but the W-tensor is the set-sunflower tensor, not S_D.
- Recommended register wording for B27: "NOT FOUND (NOT EXHAUSTIVE)". Additional sources: ST16 in full, SDW26 in full, Bürgisser's thesis in full, Tobler's thesis partial, WZ survey partial, and CVZ18 citers word-located. Still unread: Str91.

### Gaps
- Not attempted:
  - Pebody ("Proof of a conjecture of Kleinberg–Sawin–Speyer");
  - Norin;
  - Lovett (analytic rank);
  - Naslund's partition-rank / k-right-corners paper;
  - Fox–Sauermann;
  - CLZ23 / weighted slice rank (2012.14412), which was word-located only: "sunflower" appears on pp. 1–2 (introduction) and p. 27 (bibliography).
  None of these turned up a sunflower-tensor *lower bound* in the citation lists searched. They are not read.
