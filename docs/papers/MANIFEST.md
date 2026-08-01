# Paper archive

The corpus behind `docs/reading.md`, pinned so no future session has to
re-find it.

Every row records the **exact bytes that were read**: a SHA-256 over the
PDF as downloaded, its page count, the URL it came from, and the date it
was retrieved. `fetch.sh` rebuilds the corpus from those records and
fails loudly if a byte has changed — a paper that is silently revised
upstream will not pass unnoticed.

## Why some PDFs are here and most are not

`manifest.json` has a `redistributable` flag, set from the licence the
publisher actually states, not from convenience:

* **CC BY 4.0 / CC BY-SA 4.0** — redistributable with attribution. Stored
  in `pdf/`, unmodified, attributed in `ATTRIBUTION.md`.
* **BSD** (the AFP entry) — same.
* **arXiv non-exclusive distribution licence** — grants arXiv the right to
  distribute, **not** third parties. Not stored. `fetch.sh` gets it.
* **In copyright** (the 1960/1961/1969 journal scans, the PCMI notes) —
  not stored. `fetch.sh` gets it from the source that made it public.

Storing a paper we have no licence to store would be the same class of
error this reading session exists to correct, so the flag is derived
mechanically and the fetch script covers the gap.

## Rebuilding the corpus

```
  cd docs/papers && ./fetch.sh          # download all 29, verify SHA-256
  cd docs/papers && ./fetch.sh --render # also render every page to PNG
```

`fetch.sh` skips anything already present in `pdf/`, so it only reaches
the network for what is not stored.

## The corpus

`read` states how much of each was actually read, per the evidence classes
in `docs/reading.md`. "not read" means downloaded and rendered and no
more; it is not a claim about the contents.

| key | authors | title | id | pp | licence | stored | read |
|---|---|---|---|---|---|---|---|
| `ALWZ20` | Ryan Alweiss et al. | Improved bounds for the sunflower lemma | arXiv:1908.08483v3 | 19 | arXiv non-exclusive | not stored | read in full (19 of 19 pages) |
| `ASU12` | Noga Alon, Amir Shpilka, Christopher Umans | On Sunflowers and Matrix Multiplication | — | 16 | no licence stated (ECCC report) | not stored | read pp. 1-5 and 8 of 16 |
| `AhNo26` | Omran Ahmadi, Hassan Norouzi | A Polynomial Improvement of Naslund--Sawin Bound for Sunflower-Free Families Using Triangular Tensors | arXiv:2606.30593v1 | 12 | CC BY 4.0 | `pdf/naslund_improved.pdf` | read p. 1 of 12 |
| `AlHo20` | Noga Alon, Ron Holzman | Near-sunflowers and focal families | arXiv:2010.05992v1 | 11 | CC BY 4.0 | `pdf/near_sunflowers.pdf` | not read (11 pages rendered) |
| `BCCGNSU17` | Jonah Blasiak et al. | On cap sets and the group-theoretic approach to matrix multiplication | arXiv:1605.06702v4 | 27 | CC BY 4.0 | `pdf/blasiak_capset.pdf` | not read (27 pages rendered) |
| `BCW21` | Tolson Bell, Suchakree Chueluecha, Lutz Warnke | Note on Sunflowers | arXiv:2009.09327v2 | 3 | arXiv non-exclusive | not stored | read in full (3 of 3 pages) |
| `DE25` | Andrey Kupavskii, Fedor Noskov | Exact results and the structure of extremal families for the Duke--Erdős forbidden sunflower problem | arXiv:2511.17142v1 | 30 | CC BY 4.0 | `pdf/dukeerdos.pdf` | not read (30 pages rendered) |
| `EKR61` | P. Erdős, C. Ko and R. Rado | Intersection theorems for systems of finite sets | doi:10.1093/qmath/12.1.313 | 8 | in copyright (OUP); Erdos memorial archive scan | not stored | not read (8 pages rendered) |
| `ErRa60` | P. Erdős and R. Rado | Intersection theorems for systems of sets | doi:10.1112/jlms/s1-35.1.85 | 6 | in copyright (LMS/Wiley); Erdos memorial archive scan | not stored | read in full (6 of 6 pages) |
| `ErRa69` | P. Erdős and R. Rado | Intersection theorems for systems of sets (II) | doi:10.1112/jlms/s1-44.1.467 | 13 | in copyright (LMS/Wiley); Erdos memorial archive scan | not stored | not read (13 pages rendered) |
| `FKNP21` | Keith Frankston et al. | Thresholds versus fractional expectation-thresholds | arXiv:1910.13433v2 | 16 | arXiv non-exclusive | not stored | read pp. 1-4 of 16 |
| `FPPTZ24` | Peter Frankl, János Pach, Dömötör Pálvölgyi | Odd-Sunflowers | arXiv:2310.16701v2 | 10 | CC BY 4.0 | `pdf/odd_sunflowers.pdf` | read in an earlier session (10 pages) |
| `FPS21` | Jacob Fox, Janos Pach, Andrew Suk | Sunflowers in set systems of bounded dimension | arXiv:2103.10497v2 | 14 | CC BY 4.0 | `pdf/fox_pach_suk.pdf` | not read (14 pages rendered) |
| `Fuk25` | Junichiro Fukuyama | Sunflower Bound with a Sub-Logarithmic Base | arXiv:2510.19037v2 | 8 | CC BY-SA 4.0 | `pdf/sublog.pdf` | read in full (8 of 8 pages) |
| `GMR12` | Parikshit Gopalan, Raghu Meka, Omer Reingold | DNF Sparsification and a Faster Deterministic Counting Algorithm | arXiv:1205.3534v1 | 27 | arXiv non-exclusive | not stored | not read (27 pages rendered) |
| `Gal26` | Cheng Liao | On the sunflower property and the galah property | arXiv:2606.13656v1 | 21 | arXiv non-exclusive | not stored | not read (21 pages rendered) |
| `HLC25` | Quanyu Tang, Shengtong Zhang | Harmonic LCM patterns and sunflower-free capacity | arXiv:2512.20055v1 | 19 | arXiv non-exclusive | not stored | not read (19 pages rendered) |
| `JMR25` | Ting-Wei Chao et al. | Uniform set systems with small VC-dimension | arXiv:2501.13850v2 | 25 | CC BY 4.0 | `pdf/vcdim2025.pdf` | not read (25 pages rendered) |
| `Ku23` | Andrey Kupavskii | Erdos-Ko-Rado type results for partitions via spread approximations | arXiv:2309.00097v3 | 22 | CC BY 4.0 | `pdf/ku_partitions.pdf` | read pp. 1-2 and 5-8 of 22 |
| `KuZa22` | Andrey Kupavskii, Dmitriy Zakharov | Spread approximations for forbidden intersections problems | arXiv:2203.13379v3 | 27 | arXiv non-exclusive | not stored | read in full (27 of 27 pages) |
| `Kup25` | Andrey Kupavskii | Delta-system method: a survey | arXiv:2508.20132v1 | 66 | CC BY 4.0 | `pdf/kupavskii_survey.pdf` | read in full (66 of 66 pages) |
| `Lovett25` | S. Lovett | From sunflowers to thresholds (PCMI lecture notes) | — | 28 | no licence stated on the source page; author's lecture notes | not stored | read in full (28 of 28 pages) |
| `MNSZ22` | Elchanan Mossel et al. | A second moment proof of the spread lemma | arXiv:2209.11347v2 | 8 | arXiv non-exclusive | not stored | read in full (8 of 8 pages) |
| `Mis26` | Tapas Kumar Mishra | Erdős Rado Sunflower Theorem for Shifted Families | arXiv:2606.02667v2 | 12 | CC BY 4.0 | `pdf/mis26_shifted.pdf` | read in full (12 of 12 pages) |
| `Moon26` | Shachar Lovett, Raghu Meka, Yimeng Wang | Moonflowers and efficient code sparsification | arXiv:2605.08676v2 | 26 | CC BY 4.0 | `pdf/moonflowers.pdf` | not read (26 pages rendered) |
| `NaSa17` | Eric Naslund, William F. Sawin | Upper bounds for sunflower-free sets | arXiv:1606.09575v1 | 5 | arXiv non-exclusive | not stored | read p. 1 of 5 |
| `Ra20` | Anup Rao | Coding for Sunflowers | arXiv:1909.04774v2 | 8 | arXiv non-exclusive | not stored | read in full (8 of 8 pages) |
| `Rao25` | Anup Rao | The Story of Sunflowers | arXiv:2509.14790v1 | 12 | CC BY 4.0 | `pdf/story.pdf` | read in full (12 of 12 pages) |
| `SC26` | Rob Sullivan, Jeroen Winkel | Structured sunflowers and canonical Ramsey properties | arXiv:2602.04610v2 | 16 | arXiv non-exclusive | not stored | not read (16 pages rendered) |
| `SFP25` | Patrick Bennett, Amanda Priestley | The Sunflower-Free Process | arXiv:2509.16355v1 | 37 | CC BY 4.0 | `pdf/sfprocess.pdf` | not read (37 pages rendered) |
| `SFS26` | Kamil Otal | On set-like sunflower-free families of subspaces over finite fields | arXiv:2605.12232v1 | 8 | CC BY 4.0 | `pdf/sfsubspaces.pdf` | not read (8 pages rendered) |
| `Schrijver05` | Alexander Schrijver | New code upper bounds from the Terwilliger algebra and semidefinite programming | doi:10.1109/tit.2005.851748 | 8 | green OA (CWI institutional repository) | not stored | read pp. 1-2 of 8 |
| `Smooth21` | Sam Spiro | A Smoother Notion of Spread Hypergraphs | arXiv:2106.11882v2 | 12 | arXiv non-exclusive | not stored | not read (12 pages rendered) |
| `Thi21` | R. Thiemann | The Sunflower Lemma of Erdős and Rado | — | 14 | BSD License (AFP entry licence) | `pdf/afp_sunflowers.pdf` | read pp. 1-4 and 13-14 of 14 |
| `VS25` | Ferdinand Ihringer, Andrey Kupavskii | The Erdős-Rado Sunflower Problem for Vector Spaces | arXiv:2505.03671v2 | 9 | arXiv non-exclusive | not stored | not read (9 pages rendered) |

35 records, 16 PDFs stored,
11 read in full.

## What bears on what

| key | bears on this repository |
|---|---|
| `ALWZ20` | Definition 1.10 = Spread.Spread; Lemma 3.1 tightness; Thm 4.2 intersecting. |
| `ASU12` | Thm 2.3 links the uniform and Erdos-Szemeredi conjectures; Thm 2.6 the Z_D^n equivalence. |
| `AhNo26` | Polynomial improvement of NaSa17; base unchanged. |
| `AlHo20` | Alon-Holzman, near-sunflowers and focal families. |
| `BCCGNSU17` | The cap-set obstruction to the group-theoretic approach. |
| `BCW21` | Current peer-reviewed record (Cp log k)^k. |
| `DE25` | Duke-Erdos forbidden sunflower, extremal structure. |
| `EKR61` | The intersecting side. |
| `ErRa60` | The origin paper. Both branches of the dichotomy are on p. 90. |
| `ErRa69` | Sequel to the origin paper. |
| `FKNP21` | Spread def (4); Thm 1.6 fixed-size covering. |
| `FPPTZ24` | Ground-set framing; credits Hunter's equivalence. |
| `FPS21` | Sunflowers in set systems of bounded dimension. |
| `Fuk25` | Unrefereed claim of a sub-logarithmic base. |
| `GMR12` | DNF sparsification; a named Tier 4 application. |
| `Gal26` | The sunflower property and the galah property. |
| `HLC25` | Harmonic LCM patterns and sunflower-free capacity. |
| `JMR25` | Sunflowers in set systems with small VC-dimension. |
| `Ku23` | Self-contained presentation; Obs 11 = rao_witness+link, Obs 12 = spread_reduction. |
| `KuZa22` | Spread as a general method; Lemma 14 consumes the sunflower bound; tau is a tool. |
| `Kup25` | AHS72 corroboration; base/nucleus/generating-set literature. |
| `Lovett25` | Def 2.5 = Spread.Spread; Lemma 2.6 = spread_reduction; Sec 3 = the formalisation target. |
| `MNSZ22` | The four proofs; fn.2 p.6 records the gap in Tao's proof. |
| `Mis26` | coq/Compression.v f'(k,s)=C(k+s-2,k). |
| `Moon26` | Moonflowers and efficient code sparsification. |
| `NaSa17` | coq/SliceRank.v NaslundSawinBound. |
| `Ra20` | The axiom. coq/ALWZ.v Rao20_lemma2 is its Lemma 2. |
| `Rao25` | Sec 3 elementary robust-sunflower proof; log open in original form. |
| `SC26` | Structured sunflowers and canonical Ramsey properties. |
| `SFP25` | The sunflower-free process. |
| `SFS26` | Set-like sunflower-free families of subspaces. |
| `Schrijver05` | Roadmap M2's machinery; C*-algebra + SDP, hence M2 is not viable here. |
| `Smooth21` | A smoother notion of spread. |
| `Thi21` | Refutes the 'only machine-checked formalisation' claim. |
| `VS25` | Erdos-Rado sunflower problem for vector spaces. |

## Provenance rules

1. A record is added only after the PDF has been downloaded and its page
   count verified with `pdfinfo`. No record is created from a search
   result.
2. `sha256` is over the bytes that were rendered and read. If a later
   session re-fetches and the hash differs, the paper was revised —
   re-read before relying on any quotation.
3. `read` is updated only by a session that actually rendered the pages.
4. Nothing is stored under `pdf/` whose licence does not permit it.
