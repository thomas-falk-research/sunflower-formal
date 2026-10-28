# One-shot lower bounds on slice rank / subrank: [BCLSZ25] pp. 13–51 and [Str88]

Task: `docs/roadmap.md` §87.4 (context §75.1–75.2, §78.7, §87; `docs/reading.md`
rules 1–5, 18). Session of 2026-10-28. Notes only; no repository file other
than this one was written.

Labels: **PROVEN (in print)** = statement on a rendered page quoted below;
**DERIVED** = a short argument written here, not found in print in the pages
read (rule 17: "new to this repository", no novelty claimed);
**CONJECTURED**; **NOT FOUND** (in the pages read; not exhaustive).

## 1. Sources and evidence class

### [BCLSZ25] Briët–Christandl–Leigh–Shpilka–Zuiddam, *Discreteness of asymptotic tensor ranks*, Discrete Analysis 2025:15, arXiv:2306.01718v4

* File (pre-existing, not re-downloaded):
  `/tmp/claude-0/-home-user-sunflower-formal/1ebb4a50-96a0-5685-9f5c-ab90eb4993e3/scratchpad/dr_novelty/writer/bclsz/pdf/bclsz.pdf`,
  SHA-256 `45510217ca0d3ab426ae008ee6293ce74745ca99470a47be5491403dc22ed641`,
  51 pages. Version check: rendered/extracted p. 1 header reads
  *"arXiv:2306.01718v4 [cs.CC] 9 Sep 2025"* and *"DISCRETE ANALYSIS, 2025:15, 51 pp."*; pdfinfo title
  "Discreteness of asymptotic tensor ranks". It is v4.
* Rendered at 150 dpi (`pdftoppm -png -r 150`) into a new directory
  `/tmp/claude-0/-home-user-sunflower-formal/1ebb4a50-96a0-5685-9f5c-ab90eb4993e3/scratchpad/oneshot/bclsz_render/`.
* **Viewed as images this session: pp. 14–51 (38 pages), every one.**
  pp. 22–51 (the task's range) all viewed; pp. 14–21 re-viewed for the
  one-shot statements of §2. p. 13 rendered, not viewed. No failures.
* Together with the earlier passes (pp. 1, 3, 7–11, 13–21), the only pages of
  [BCLSZ25] never viewed in any pass are **pp. 2, 4, 5, 6, 12**.

### [Str88] Strassen, *The asymptotic spectrum of tensors*, J. reine angew. Math. 384 (1988) 102–152

Acquisition attempts (all on 2026-10-28, through the session proxy):

| Route | Result |
|---|---|
| `https://doi.org/10.1515/crll.1988.384.102` | 202, empty body, redirect to `degruyterbrill.com/.../html` (bot challenge) |
| De Gruyter `/document/doi/10.1515/crll.1988.384.102/html` and `/pdf` | 202, empty body (challenge) |
| Crossref API `works/10.1515/crll.1988.384.102` | 200; metadata only (title, pp. 102–152, De Gruyter links) |
| EuDML search (two queries) | 200, no matching record (unrelated hits) |
| DigiZeitschriften `/id/243919689_0384`, search | 404; home page states the service *"wurde zum 31.12.2025 eingestellt"* / *"was discontinued on 31 December 2025"*, content to move to SUB Göttingen |
| **GDZ Göttingen** `gdz.sub.uni-goettingen.de/id/PPN243919689_0384` | 200; IIIF manifest lists range `LOG_0008` *"The asymptotic spectrum of tensors."*, Strassen, V., 1988 |
| **GDZ article PDF** `gdz.sub.uni-goettingen.de/download/pdf/PPN243919689_0384/LOG_0008.pdf` | **200, application/pdf, 3,941,658 bytes, 52 pages** |

* Saved (untrusted, own new directory):
  `/tmp/claude-0/-home-user-sunflower-formal/1ebb4a50-96a0-5685-9f5c-ab90eb4993e3/scratchpad/oneshot/str88_pdf/str88.pdf`,
  SHA-256 `872b87403807a6f045d773e3367e86960300af121fc6ed58b634ebd98ef6927e`.
  Scanned images, no text layer on pp. 2–52 (pdftotext empty): every
  statement below is from viewed images. PDF page `k` = printed page `100 + k`
  (PDF p. 1 is the GDZ cover).
* Rendered all 52 pages at 150 dpi into
  `/tmp/claude-0/-home-user-sunflower-formal/1ebb4a50-96a0-5685-9f5c-ab90eb4993e3/scratchpad/oneshot/str88_render/`.
* **Viewed: printed pp. 102, 112, 116–128, 130–134 (21 pages).** Not viewed:
  pp. 103–111, 113–115, 129, 135–152. So [Str88] is **read in part**; the two
  statements asked for (Thm. 3.10, eq. (4.6)) are read with their proofs.

## 2. What [Str88] says (closes §78.7's "CONDITIONAL on [Str88]")

* **Theorem 3.10, p. 126:** *"Let k ⊂ K be a field extension and let
  (X, u) ∈ Pop k. Then Δ(u) = Δ(u^K)."* Proof on the same page, via scalar
  extension and [15] Prop. 5.3 (i). Combined with **Theorem 3.8, p. 124:**
  *"R̰(a) = max_{Δ(u)} a, Q̰(a) = min_{Δ(u)} a."*, the asymptotic subrank is
  unchanged by any field extension. No restriction to infinite or
  perfect fields appears in the statement. **PROVEN (in print).** So the
  step of [BCLSZ25] p. 20 (*"Since the asymptotic subrank does not change
  under field extension [Str88, Theorem 3.10], we may assume that our base
  field F is infinite"*) is supported as stated, and Lemma 78.C's caveat
  "CONDITIONAL on it for finite fields" can be discharged. p. 132 uses it the
  same way: *"Since by Theorem 3.10 Δ_c depends on k only through its
  characteristic, the same is true for ω."*
* **Eq. (4.6), p. 134:** *"Q̰(⟨e, h, l⟩) = min{eh, hl, le}."* with the
  proof sketch *"(We have Q̰(⟨e, h, l⟩) = min_{Δ_m} x_1^{log e} x_2^{log h}
  x_3^{log l}, therefore log Q̰(⟨e, h, l⟩) = min_{log Δ_m}(w_1 log e + …))"*,
  resting on (4.3) and (4.4), p. 133. **PROVEN (in print).** It is an
  *asymptotic* statement.
* **One-shot content in [Str88] (pages read):** Lemma 3.5, p. 121 is the 1988
  form of [BCLSZ25] Lemma 2.12: with `e, h, l` the maximal ranks of 2-, 3-,
  1-slices of a concise `t`, *"⟨e^α, h^β, l^γ⟩ ≤ a^{α+β+γ} ≤ ⟨m^α p^γ,
  m^β n^γ, n^α p^β⟩"* — a restriction of the **power** `a^{α+β+γ}`, not of `a`.
  p. 123: *"Theorem 6.6 of [15] gives ⌈3n^{2N}/4⌉ ⊴ ⟨n^N, n^N, n^N⟩"* — a
  **degeneration** (border), not a restriction. p. 122: *"the zero algebra
  N_n ([15], section 4) is not balanced for n > 2. (R(zf) ≤ 2 for any
  z ∈ N_n^*, …)"*. No one-shot lower bound on the subrank or slice rank of a
  single tensor `a` (as opposed to its powers) was found on the pages read.
  **NOT FOUND** (pages listed above only).

## 3. One-shot statements in [BCLSZ25], and what each gives

Notation (p. 16): `Q_ℓ(T) = max-rank(A_ℓ)`, the maximal rank in the
`ℓ`-slice span. p. 14: *"Subrank, slice rank, the flattening ranks and tensor
rank satisfy Q(T) ≤ SR(T) ≤ R_ℓ(T) ≤ R(T) for every ℓ ∈ [3]."*

| Statement (page) | One-shot for | Gives |
|---|---|---|
| **Thm. 2.1** (p. 16): *"Let T ∈ F^{n1} ⊗ F^{n2} ⊗ F^{n3} be concise. Let ℓ1, ℓ2, ℓ3 ∈ [3] be distinct. Suppose that \|F\| > n_{ℓ3}. Then Q_{ℓ1}(T) Q_{ℓ2}(T) ≥ n_{ℓ3}."* | `T` | max-ranks of slice spans, **not** `Q` or `SR` |
| **Cor. 2.2** (p. 16): two directions with `Q_{ℓ1}(T) ≥ √n3`, `Q_{ℓ2}(T) ≥ √n1` (`n1 ≤ n2 ≤ n3`, `\|F\| > n3`) | `T` | same |
| **Lemma 2.9** (p. 20): *"If there are distinct ℓ1, ℓ2 such that Q_{ℓ1}(T), Q_{ℓ2}(T) ≥ r, then Q(T^{⊠2}) ≥ r."* | `T^{⊠2}` | **subrank of the square** |
| **Lemma 2.12** (p. 20): *"T^{⊠3} ≥ ⟨Q2(T), Q3(T), Q1(T)⟩."* | `T^{⊠3}` | restriction of the cube to a matrix-multiplication tensor |
| **Lemma 2.13** (p. 20): *"Q̰(T^{⊠3}) ≥ min_{ℓ1,ℓ2} Q_{ℓ1}(T) Q_{ℓ2}(T)."* (proof cites [Str88] eq. 4.6) | asymptotic | — |
| **Lemma 3.3** (p. 22): *"Let T … be a tensor and A1,…,Ac … be c 3-slices of it. If A1,…,Ac are linearly independent and min-rank(A1,…,Ac) ≥ 2c(c−1), then Q(T) ≥ c."* | **`T`** | **subrank of `T` itself**, under a min-rank hypothesis |
| **Thm. 3.19** (p. 30): *"Let n1, n2 > 2 and let T ∈ F^{n1} ⊗ F^{n2} ⊗ F^2 be a concise tensor. Then Q(T) = 2."* | **`T`** | format `n1 × n2 × 2` only |
| **Thm. 5.10** (p. 37): *"Let T … be concise. For every distinct ℓ1, ℓ2, ℓ3 we have ρ_{ℓ1,ℓ2}(T) max{Q_{ℓ1}(T), Q_{ℓ2}(T)} ≥ n_{ℓ3}."* (no field-size hypothesis) | `T` | pivot cover number × max-rank |
| **Thm. 5.13** (p. 38): *"For any tensor T and any ℓ1 ≠ ℓ2 we have ρ_{ℓ1,ℓ2}(T) ≤ Q(T)."* — here `Q` is the **border subrank** (Def. 5.11, p. 37) | **`T`** | **border subrank of `T`** |
| **Lemma 5.12** (p. 38): *"For any tensor T we have Q(T) ≤ Q̰(T)."* (border ≤ asymptotic; [Str88] Prop. 5.10, [BCS97] Prop. 15.26) | — | — |
| **Thm. 5.15** (pp. 38–39), `\|F\| = ∞`: border `Q(T) ≤ Q_ℓ(T)`; p. 39: *"ρ_{ℓ1,ℓ2}(T) ≤ Q(T) ≤ Q_{ℓ3}(T)"* | `T` | upper bound |
| **Lemma 6.2** (p. 43) `Q_ℓ(T) ≤ SR_ℓ(T)`; **6.3** `Q(T) ≤ Q_ℓ(T)`; **6.4** `SR(T) ≤ SR_ℓ(T)`; **6.7** (p. 44) `SR_ℓ(T) ≤ 2Q_ℓ(T)` if `\|F\| > Q_ℓ(T)`; **6.8** `SR_ℓ(T) ≤ 4Q_ℓ(T)` | `T` | all **upper** bounds on `SR(T)` or relations among relaxations |
| **Lemma 6.9** (p. 45): *"Let T ∈ F^{n1} ⊗ F^{n2} ⊗ F^{n3}. Then Q(T^{⊠3}) ≥ 3/64 SR(T)^2."* (border subrank) | `T^{⊠3}` vs `SR(T)` | **upper bound on `SR(T)`** in terms of the cube |

Also p. 45, verbatim: *"Unlike rank and subrank, slice rank is not sub- or
super-multiplicative under Kronecker product, so Fekete's lemma cannot be
used to guarantee its asymptotic version's existence."* And p. 45, inside
Lemma 6.9's proof: *"Strassen [Str87, Theorem 6.6] proved for any e ≤ h ≤ ℓ
that Q(⟨e, h, ℓ⟩) ≥ eh − ⌊(e+h−ℓ)²/4⌋ [if] e + h ≥ ℓ, eh otherwise. In both
cases we have Q(⟨e, h, ℓ⟩) ≥ 3/4 eh"* (border subrank; [Str87] itself not read).

§5.3 (pp. 39–42), Theorem 1.9's proof: Thm. 5.16 (p. 39) *"Let T ∈ F^n ⊗ F^n
⊗ F^n be symmetric and concise. Then Q̰(T) ≥ √n."* follows from Thm. 5.19
(p. 40, pivot-matched), whose proof (p. 42) is *"By Lemma 5.21, T^{⊠2}
restricts to the upper-triangular form … which in turn states that it
degenerates to a diagonal tensor of size n. By Lemma 5.12 … Q̰(T^{⊠2}) ≥
Q(T^{⊠2}) ≥ n."* So Theorem 1.9 is again a one-shot statement about the
**square**: border-`Q(T^{⊠2}) ≥ n` for concise pivot-matched (e.g. symmetric)
`T`. No field-size hypothesis appears in Thm. 5.16/5.19, Lemmas 5.21–5.22
(pp. 39–42) — so §78.7's "field scope unverified" for Thm. 1.9 reads, from
these pages: stated for every field. (Def. 5.17 needs pivot-matching; p. 39 says only
*"In fact, we will prove a stronger theorem which implies Theorem 5.16"*; no
separate proof that symmetric ⇒ pivot-matched appears on pp. 39–42. DERIVED:
for symmetric `T` take `T_A = T_B = T`; then `B_i = A_i` as matrices, so
`p_A = p_B` and the condition holds.)

## 4. Verdicts

### (a) Is there a one-shot lower bound on SR or Q of a single concise tensor?

1. **In terms of dimensions alone: NOT FOUND in print, and FALSE (PROVEN from
   print + one line).** [BCLSZ25] Example 2.5, p. 18: *"For every n ∈ N,
   there is a concise tensor T ∈ F^n ⊗ F^n ⊗ F^n such that Q1(T) = Q3(T) = n
   and Q2(T) = 2"*, `T := e1⊗e1⊗e1 + Σ_{i=2}^n e1⊗e_i⊗e_i + Σ_{i=2}^n
   e_i⊗e_i⊗e1`. **DERIVED (one line):** the first two sums are
   `e1 ⊗ (Σ_{i≥1} e_i⊗e_i)` (leg-1 slice) and the third is
   `(Σ_{i≥2} e_i⊗e_i) ⊗ e1` (leg-3 slice), so **`SR(T) ≤ 2`** for every `n`,
   while p. 34 (Remark 4.3) says *"a concise tensor T ∈ F^n ⊗ F^n ⊗ F^n such
   that the asymptotic subrank and asymptotic slice rank of T equal
   2√(n − 1)"* (`n ≥ 5`). [Str88] p. 122 makes the same point for the zero
   algebra `N_n`. So conciseness gives no one-shot lower bound beyond a
   constant, and `SR(T)^m ≥ SR(T^{⊠m})` fails (`2^m` against
   `(2√(n−1))^{m−o(m)}`).
2. **Within the tester class (support ⊆ `S_D^{(n)}`, nonzero diagonal, zero on
   exactly-two-equal triples): one-shot dimension bounds also FAIL — DERIVED,
   checked by exact script.** The BHL tester `q_c` on `[D]` (`n = 1`) with
   `c ≡ −1/2` (char ≠ 2) satisfies
   `−2·q = (J − I)_{12} ⊗ 1_3 − Σ_a e_a ⊗ 1 ⊗ e_a − Σ_b 1 ⊗ e_b ⊗ e_b`
   (`J` all-ones, `1` the all-ones vector): a leg-3, a leg-2 and a leg-1 slice.
   Hence **`SR(q_{−1/2}) ≤ 3` for every `D`**, although `q` is concise and
   `Q̰(q) ≥ D^{1/3}` (Lemma 78.C). Checked entrywise in exact rationals for
   `D = 2, …, 8` (`scratchpad/oneshot/scripts/q_half.py`, all `True`). With
   (3b) below, `SR(q ⊠ q) ≥ √D`: so `SR(q)² ≤ 9 < SR(q⊠q)` for `D ≥ 100` —
   **slice rank is not submultiplicative even on BHL testers**.
3. **One-shot bounds that do exist (all need more than conciseness):**
   * induced matchings in the support: `SR(T) ≥ M` (Lemma 75.A; in print,
     [BCCGNSU17] Prop. 4.8, [ST16] Lemma 3 + Ex. 5, register B23);
   * Sawin–Tao [ST16] Prop. 4 (maximal elements of the support under total
     orders, any basis) — in print per this repository's reading log
     (`docs/reading.md` [ST16], lines 1–180 read in an earlier session; **not
     re-read here**);
   * [BCLSZ25] Lemma 3.3 (p. 22): `Q(T) ≥ c` from `c` independent slices of
     min-rank `≥ 2c(c−1)`; Thm. 3.19 (p. 30) for format `n1 × n2 × 2`;
   * [BCLSZ25] Thm. 5.13 (p. 38): **border** subrank `≥ ρ_{ℓ1,ℓ2}(T)`. To turn
     it into a slice-rank bound one needs border-`Q(T) ≤ SR(T)`. **NOT FOUND
     in print in the pages read; DERIVED here:** over `F̄`, for each
     `(a1,a2,a3)` the set `{T : T ∈ U1⊗V2⊗V3 + V1⊗U2⊗V3 + V1⊗V2⊗U3, dim U_i =
     a_i}` is the projection of a closed subset of
     `Gr(a1)×Gr(a2)×Gr(a3)×V` (vanishing of `T` in `⊗(V_i/U_i)`), hence closed
     (Grassmannians are complete); so `{SR ≤ r}` is Zariski-closed, slice rank
     is lower semicontinuous, and a degeneration `T ⊵ ⟨r⟩` forces
     `SR_{F̄}(T) ≥ r`; and `SR_F ≥ SR_{F̄}`. With Thm. 5.10 this gives, for a
     concise `T` with `n_ℓ = N`: `SR(T) ≥ ρ_{2,3}(T) ≥ N / max(Q2(T), Q3(T))`
     (**DERIVED**, conditional on the semicontinuity sketch being checked by
     a reviewer). It is one-shot and computable, but it is large only when
     two slice spans have small max-rank; it gives nothing for testers in
     general (cf. item 2: `q_{−1/2}` has `SR ≤ 3`, so for it two of the
     `Q_ℓ` must be `≥ D/3`).

   **Verdict (a): NO** — no published one-shot lower bound on `SR` or `Q` of a
   single concise tensor that grows with the dimensions (NOT FOUND, and false
   by Example 2.5); and **no** such bound can exist for the tester class from
   conciseness/dimension alone (false at `n = 1` by `q_{−1/2}`, DERIVED).
   Any one-shot bound for non-power testers must use the support `S_D^{(n)}`
   (induced matchings, Sawin–Tao, pivots), which is §87.3 question 2's
   territory (`M(D,n)`, `Λ(D)`).

### (b) What Theorem 2.1 / Lemma 2.12 give for a non-power tester `T` on `[D]^n`

Let `N = D^n`; `T` is concise with `n1 = n2 = n3 = N` (78.C's argument applies
verbatim to any tensor with nonzero diagonal and zeros on exactly-two-equal
triples). Work over `F̄` (`|F̄| = ∞`), and use `SR_F(·) ≥ SR_{F̄}(·) ≥ Q_{F̄}(·)`.

* **Square, PROVEN from print** (Cor. 2.2 + Lemma 2.9 + p. 14): two `Q_ℓ(T)
  ≥ √N`, so `Q_{F̄}(T^{⊠2}) ≥ ⌈√N⌉` and **`SR(T^{⊠2}) ≥ D^{n/2}`**. `T^{⊠2}`
  is itself a tester on `[D]^{2n}` (support is coordinatewise), i.e.
  `SR ≥ (alphabet size)^{1/4}` for every tester that is a square.
* **Cube**: Lemma 2.12 + Thm. 2.1 + [Str87] Thm. 6.6 as quoted on p. 45 give
  border-`Q_{F̄}(T^{⊠3}) ≥ (3/4) e h ≥ (3/4) N` (`e ≤ h` the two smallest
  `Q_ℓ`, `eh ≥ N` by Thm. 2.1). **PROVEN (in print) for border subrank**;
  `SR(T^{⊠3}) ≥ 3N/4` is **DERIVED** via the semicontinuity sketch above.
  Plain (non-border) one-shot subrank of `⟨e,h,l⟩`: NOT FOUND in the pages
  read. Asymptotically, Lemma 2.13 gives `Q̰(T^{⊠3}) ≥ N`.
* **`T` itself: nothing.** The needed transfer `SR(T)^k ≥ SR(T^{⊠k})` is
  **false in general** ((a)1, (a)2), and [BCLSZ25] p. 45 says slice rank is
  *"not sub- or super-multiplicative"*. The direction that *is* elementary
  (**DERIVED**, one line: tensor each slice-rank-one term of `A` with the
  leg-`ℓ` decomposition of `B` into `n_ℓ(B)` terms) is
  `SR(A ⊠ B) ≤ SR(A) · max_ℓ n_ℓ(B)`; for `A = B = T` it yields
  `SR(T) ≥ SR(T^{⊠2})/N ≥ N^{−1/2}` — vacuous. Lemma 6.9 relates `SR(T)` and
  the cube in the **other** direction (`SR(T)² ≤ (64/3)·border-Q(T^{⊠3})`).

**Consequence for the route (§87.3 question 1).** [BCLSZ25] closes the
square and cube of every tester (one-shot, `D^{n/2}` and `~D^n`), and every
tensor power asymptotically (78.C), but says nothing about a tester that is
not a power, and conciseness cannot say anything: `q_{−1/2}` on `[D]` is
concise with `SR ≤ 3`. The only one-shot handles on a non-power tester are
support-based; the open quantity is `min SR(T)` over testers on `[D]^n` at
`D = s·m`, `n = s`. **Status: NOT FOUND** (a lower bound), **CONJECTURED** by
nobody in the pages read.

## 5. Proposal (not run): exact experiments at `n = 2, D = 4`

Testers: `T ∈ F^{16×16×16}`, support ⊆ `S_4^{(2)}` (`|S_4| = 4 + 24 = 28`,
so `28² = 784` support cells, 16 of them diagonal), diagonal nonzero. Work
over `Q` (exact) and `F_p` for a few small primes. Families: products
`q_c ⊠ q_{c′}` (controls), random rational values on the 768 off-diagonal
support cells, sparse random, and structured non-products (e.g. the
`q_{−1/2}`-type identity of (a)2 written on the 16-letter alphabet but
masked to `S_4^{(2)}`).

What is exactly computable, with cost (all single-core, seconds unless said):

1. **Upper bounds on SR (certificates).** An explicit decomposition is checked
   exactly by reconstructing `T` (4096 entries). Sources: tensoring slice
   decompositions (`SR(A⊠B) ≤ SR(A)·4`, e.g. `≤ 12` for `q_{−1/2}^{⊠2}`);
   min-cov of a slice span via Lemma 6.7 (`SR ≤ SR_ℓ ≤ 2 Q_ℓ`, `Q_ℓ` = generic
   rank of a random combination of the 16 slices, certified by one explicit
   combination); local search over `(a1,a2,a3)` and subspaces (solve
   `T ∈ Σ U_i-terms` as a linear system once `U_i` are fixed: 4096 equations,
   ≤ 16·256·3 unknowns — milliseconds per candidate; random `U_i` from the
   slice spans).
2. **Lower bounds on SR, exact and one-shot:**
   * induced matching in `supp T` (MILP/SAT over 784 cells; seconds) —
     support-only, so identical for all testers with full support;
   * Sawin–Tao Prop. 4 with **arbitrary** total orders on the 16 letters of
     each leg (not product orders, outside F7's scope): for given orders,
     maximal elements of `supp T` in O(784²) and a 3-partite vertex cover ILP
     on 48 binaries (ms); local search over orders (`16!³` space; ~10⁴
     evaluations, minutes). Basis changes: only heuristically (random
     unimodular `GL_16(Z)` maps, then re-run; support becomes dense, so
     cost rises to O(4096²) per evaluation — still seconds);
   * **pivot bound** `ρ_{ℓ1,ℓ2}(T)` ([BCLSZ25] Defs. 5.1–5.8, Lemma 5.7): row
     echelon form of a `16 × 256` matrix (exact rationals) + bipartite
     matching (König); microseconds per ordering. It bounds **border**
     subrank (Thm. 5.13), hence SR via the semicontinuity sketch of (a)3 —
     have that sketch reviewed before quoting the number as a slice-rank
     bound. Maximise over the 6 ordered pairs, row/column permutations and
     random `GL` changes;
   * subrank witnesses: search for `A, B, C` with `(A⊗B⊗C)T = ⟨r⟩` (numerical
     least squares in `≤ 3·r·16` unknowns, then rationalise and verify
     exactly). `r ≤ 16`; each attempt seconds; a witness is a certificate,
     failure is not;
   * Lemma 3.3 (`Q(T) ≥ c` from min-rank `≥ 2c(c−1)`): at `N = 16` only
     `c ≤ 3` is possible (`2·3·2 = 12 ≤ 16`); certifying min-rank needs all
     nonzero combinations — feasible over `F_p` for tiny `p` by enumeration
     (`p^c` combinations), not over `Q`.
3. **What is not computable exactly at this size:** `SR(T)` itself when
   upper and lower bounds disagree. Deciding `SR(T) ≤ r` is an existential
   question over Grassmannians (dimension up to ~`r·16`); Gröbner bases are
   out of reach at `16³`. So the table should report `[best lower, best
   upper]` per tester, with each end certified, and an exact value only
   where they meet.
4. **Expected scale.** `N = 16`, so everything lies in `[2, 16]`; the
   asymptotic floor `D^{n/3} = 4^{2/3} ≈ 2.5` is below trivial bounds, so
   this size can only detect **non-product testers whose SR is below the
   products'** (e.g. a non-product with SR ≤ 6 against products' lower
   bounds), not growth. Total cost: well under an hour of CPU for ~100
   testers with all methods; no long runs needed.

## 6. Changes this suggests to the repository (not made)

* §78.7 / Lemma 78.C: the "CONDITIONAL on [Str88] Thm. 3.10 for finite
  fields" caveat can be removed — Thm. 3.10 (p. 126) + Thm. 3.8 (p. 124) read.
  Eq. (4.6) (p. 134) read.
* §78.7: Theorem 1.9's proof (§5.3, pp. 39–42) read; no field-size
  hypothesis on those pages.
* §87.3 question 1: record that conciseness cannot give a one-shot bound,
  with `q_{−1/2}` (`SR ≤ 3`, every `D`) and Example 2.5 (`SR ≤ 2`) as the
  witnesses, and that slice rank is not submultiplicative on BHL testers.
* `docs/reading.md`: [BCLSZ25] now read pp. 1, 3, 7–11, 13–51 (missing 2,
  4–6, 12); [Str88] read in part (pp. 102, 112, 116–128, 130–134), source GDZ
  `LOG_0008`.
