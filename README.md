# Sunflower-Formal

A stdlib-only Coq development around the **Erdős–Rado sunflower
problem**, with a Rust search companion and a testing layer aimed at
the errors a proof kernel cannot catch. It holds the classical bounds,
exact small values, the deterministic half of the 2020 spread argument,
one case of the conjecture itself (bounded VC-dimension), and a
machine-checked account of the sharpest open exact value, `g(4)`.
Everything compiles with stock **Coq 8.18**; the only axiom in the
library is the published 2020 spread lemma, quarantined in
`coq/ALWZ.v` and used by exactly one theorem.

## The problem

Let $f(n,k)$ be the least $m$ such that every family of $m$ distinct
$n$-sets contains a $k$-sunflower ($k$ distinct sets whose pairwise
intersections are all one common core). **Open (Erdős–Rado 1960;
Erdős's \$1000 prize for $k=3$):** is $f(n,k) \le c_k^{\,n}$ for a
constant $c_k$? Write $g(b) = f(b,3)-1$ for the largest 3-sunflower-free
$b$-uniform family, and $\iota(b)$ for the largest such family that is
also intersecting.

## Status at a glance

The conjecture is **open** and nothing here is progress on it in
general. Every result below carries its trust level; the levels are
distinct and the difference is the point of this repository.

| Trust level | What it means | Headline results | Where |
|---|---|---|---|
| **Kernel-proved** | Coq, zero admits, no axiom (`Print Assumptions` closed, `coqchk` clean) | Erdős–Rado $f(n,k)\le(k-1)^n n!+1$; the product lower bound; $f(2,3)=7$; $f(n,3)\ge 20^{n/3}+1$ by supermultiplicativity; $2\iota(b)\le g(b)\le 2b\,\iota(b)$ (the lower half is Abbott–Hanson–Sauer 1972, Lemma 4, [`docs/reading.md`](docs/reading.md) A17; the upper half composes two inequalities printed in the same paper, B10; only the single two-sided display and the machine-checked statement are this repository's), so the conjecture at $k=3$ is equivalent to an exponential bound on intersecting families; the Abbott–Hanson–Sauer substitution $g(ab)\ge g(a)\,\iota(b)^a$ and their Lemma 6 $\iota(ab)\ge\iota(a)\iota(b)^a$, with a gap in the printed proof repaired (roadmap §88), iterated to their rate $\iota(n),\,g(n)/2\ge 10^{(n-s_3(n))/2}$, $s_3$ the base-3 digit sum (roadmap §89), and with their Lemma 5 $\iota(a+b)\ge\iota(a)\,g(b)$ in general, the key inequality of their Theorem 3's proof, $\iota(n)\ge 10^{(n-s_3(n))/2}\,2^{s_3(n)-1}$ (display (23)), and Theorem 3 itself in integer form (roadmap §90); the spread reduction and an axiom-free $f(n,k)\le(n(k-1)+1)^n+1$; **the conjecture for families of bounded VC-dimension** (Ge–Wang–Xu–Zhao 2026; formalised by an elementary route that departs from theirs at four places — prior art PLAUSIBLE-not-novel, no novelty claimed, roadmap §59.1); $I(3,3)=10$; Hall and Kőnig from scratch. Checkers and the census method: a generic checker for integer-programming bounds (`LPCert`, [`docs/lpcert.md`](docs/lpcert.md)), a checker for LRAT unsatisfiability proofs ([`docs/lrat.md`](docs/lrat.md)), and the completeness of an isomorph-free search that prunes only on checked witnesses from an untrusted oracle, giving a census theorem from a search ([`docs/census_certification.md`](docs/census_certification.md), stage 2) | `coq/ErdosRado.v`, `ProductLowerBound.v`, `F23.v`, `DirectSum.v`, `IotaRate.v`, `SubstitutionFree.v`, `SubstitutionRate.v`, `SpreadReduction.v`, `VCSunflower.v`, `TauThreeTen.v`, `KoenigHall.v`, `LPCert.v`, `LRAT.v`, `CensusGen.v`, `CensusSearch.v`, `CensusDemo.v` |
| **Kernel-proved, given named hypotheses** | A Coq theorem whose premises are stated facts that are not themselves in the kernel | The link descent at uniformity 4 (§64–§73): a 4-uniform 3-sunflower-free family with a link of ≥ 21 members has ≤ 54 members, given the link census (which implies $\iota(4)\le 27$, `CensusIota.iota_of_census`, §74); with the published meeting bound, $g(4)\le 76$ (`CensusIota.g_four_at_most_76_of_census`, from those two premises alone). Weak duality, label-independence and the per-class transport are theorems; every one of the 491,536 link classes at sizes 21–27 carries a certificate checked by one generic checker, `LPCert.check` (through `Link23.lpclass`), by `vm_compute`, re-checked by `coqchk`; §64's LP certificates for 23–27 remain as an independent cross-check | `coq/LPCert.v`, `Link23.v`, `LinkCombine.v`, `Link23s*.v`, `Link22s*.v`, `Link21s*.v`, `CensusIota.v`, `Stability4.v` (cross-check: `LinkLP.v`, `LinkCerts2*.v`) |
| **Proved on paper, Python-checked** | Hand argument plus exact-arithmetic or DRAT certificates outside the kernel | Nothing of the $b=4$ descent any more: the §65 Python model turned out to be over-constrained (a label confusion in its exclusions, §69.2) and was superseded by the kernel model; the record of what was Python-checked stays in `docs/roadmap.md` §60–§65 | `docs/roadmap.md` §65, §69 |
| **Validated by computation, not proved** | Two independent exhaustive searches agree to the unit; no certificate exists | $\iota(4)=27$ and the uniqueness of the 27-family ($10^{11}$ nodes, agreeing with arXiv:2609.06175); the census of link classes at sizes 21–27, now the one premise of $g(4)\le 76$ besides the cited meeting bound; a staged plan to certify it is [`docs/census_certification.md`](docs/census_certification.md) | `docs/ladder/iota4_replication/` |
| **Cited** | Taken from the literature, read on rendered pages, not re-proved | the 2020 spread lemma (the one axiom); $f(3,3)=20$ (Abbott–Gardner 1969); $\psi(3,3,2)=10$ and $|N[R]|\le 56$ (Axante et al. 2026) | `coq/ALWZ.v`, `docs/reading.md` |
| **Open** | | the conjecture; $g(4)\in[54,76]$ (Pálvölgyi's $g(4)=54$ holds whenever some link has ≥ 21 members); whether $r^*(3,3)$ is 3 or 4; whether slice rank with a vector tester can be made alphabet-uniform — it cannot reach $f(n,3)$ otherwise, since any $D^{\alpha}$ saving gives no bound (§75); for product testers it cannot (§78.7, via Briët–Christandl–Leigh–Shpilka–Zuiddam 2025), open for testers that are not tensor powers | `coq/Conjecture.v`, `docs/roadmap.md` §66–§75 |

The current bracket at uniformity 4 is therefore
$54 \le g(4) \le 76$, against the published $54 \le g(4) \le 83$; the 76
is in the kernel given $\iota(4)\le 27$, the validated census and the
published meeting bound, and the lower end is the doubled Abbott–Hanson
family. What would move it: a
certificate for $\iota(4)\le 27$ (no feasible route is known, §60.8), or a
constraint on members meeting both of a disjoint pair that the single-root
count does not imply (§67.2 shows the two-root count gives exactly
$56+\Delta$).

## Verifying

```bash
make verify        # builds all 66 Coq files of the theory, then runs the axiom audit
make coqchk        # Coq's separate kernel checker; exactly one axiom library-wide
make certs         # builds the 691 certificate modules of the link descent (hours; not in CI)
make certs-assumptions certs-statements certs-coqchk   # audit them
make mutants       # weaken each definition in turn; see what breaks
make testbed       # exhaustive falsification of the spread hypothesis
cd rust && cargo test --release
```

`make verify` reports every audited theorem (909 of them) as
`Closed under the global context`, then prints the full statement of
the one axiom under the modern bound. Of 196 mutations, 193 are killed outright;
the two survivors are proved redundant hypotheses and one is a control.
The certificate modules are listed in `_CoqProject.certs`, apart from
the theory: they need tens of CPU-hours, which no CI job allows, and no
theory module imports them. Their theorems are audited by
`make certs-assumptions` and `make certs-statements` against
`tools/audited_certs.txt`, and `make certs-coqchk` re-checks them one
module per process.
The LP certificate modules (`coq/LinkCerts2*.v`) take about 2.5 s per
link class under `vm_compute`, roughly ten core-hours in all, and
twice that under `coqchk`; `tools/iota4/linkcert_coq.py` regenerates
them from the census files. The modules of the census chain
(`coq/Link23s*.v`, `Link22s*.v`, `Link21s*.v`: 656 modules, from
`tools/iota4/link23_coq.py lpshards`) take about 0.26 s per class
under `vm_compute`, 35.7 core-hours in all, at most 5.7 GB per module.

Requirements: Coq 8.18 (`apt-get install coq` on Ubuntu 24.04), Rust,
Python 3 for the gates. The gates — statement baselines, quoted-number
checks, route ceilings, pull-request checks — are described in
[`docs/testing.md`](docs/testing.md).

## Where things are

- [`STATUS.md`](STATUS.md): per-theorem status, closed / cited / open,
  with what each depends on.
- [`docs/roadmap.md`](docs/roadmap.md): the running account, one
  section per session, what was tried, what failed, and what is owed.
- [`docs/reading.md`](docs/reading.md): the literature register, one
  entry per source actually read, every claim about the literature
  resolved to confirmed / refuted / not found / unreachable.
- [`docs/references.md`](docs/references.md), [`docs/papers/`](docs/papers/):
  bibliography with evidence class, and the rendered-page logs.
- [`docs/narrative.md`](docs/narrative.md): the long-form account that
  used to be this README.
- [`docs/testing.md`](docs/testing.md): what the kernel cannot check and
  the eight mechanisms that target it.
- [`docs/lpcert.md`](docs/lpcert.md), [`docs/lrat.md`](docs/lrat.md): the
  two generic certificate checkers, what they prove and how they are tested.
- [`docs/census_certification.md`](docs/census_certification.md): the
  staged plan for turning the census, the one remaining premise of
  $g(4)\le 76$, into a theorem; stages 1–2 done.

## Design notes

Finite sets are `NoDup` lists of `nat`, families are lists of sets,
set equality is mutual inclusion and family distinctness is "no two
members set-equal", which is the right notion for non-canonical list
representations. No Mathematical Components, no plugins beyond `lia`.

## Relation to prior formalizations

The Erdős–Rado lemma is in Isabelle/HOL (Thiemann, AFP 2021); Hall and
Kőnig are in Isabelle, Lean and MathComp. A targeted search found no
machine-checked exact sunflower number, lower bound above the product
construction, or part of the post-2020 spread argument in any system,
and no sunflower development in Coq; see [`docs/narrative.md`](docs/narrative.md)
for the search and [`docs/reading.md`](docs/reading.md) for the register.

## Methods note

The proofs were developed with substantial AI assistance (Anthropic's
Claude), directed and reviewed by the maintainer. Correctness does not
rest on how they were written: every theorem is checked by the Coq
kernel, the audits print what each headline theorem assumes, and the
gates attack the definitions and the prose.

## License

MIT, see [`LICENSE`](LICENSE).
