# The extremal 4-uniform sunflower-free families on nine points

**Abstract.** Write `g(m,n)` for the largest family of `m`-subsets of an
`n`-point set containing no three sets with pairwise equal intersections,
and `ι(m,n)` for the largest such family that is in addition
intersecting. We show that `g(4,9) = ι(4,9) = 27` and classify the
extremal families: up to relabelling there are exactly two, one
intersecting and one not. The intersecting one is the
Abbott–Hanson–Sauer substitution of the triangle into itself, so the
extremal family for `ι(4,9)` is unique while the extremal family for
`g(4,9)` is not — the two problems share an extremal *number* but not an
extremal *object*. The upper bound is a link argument resting on a single
finite computation, `g(3,8) = 12`, and is machine-checked in Coq
conditional on it. The classification is an exhaustive search whose counts
are confirmed against an independent orbit calculation.

| | |
|---|---|
| Repository | `thomas-falk-research/sunflower-formal` |
| Branch | `claude/sunflower-session-n11-mkonqv` |
| Bibliography | `docs/references.md` and `docs/papers/sunflower.bib`, cited below by key |
| Reproduction | §9 — every figure in this note is the output of a command given there |

---

## 1. Definitions and notation

Let `[n] = {0, 1, …, n−1}` and let `C([n],m)` denote the family of
`m`-subsets of `[n]`. Three distinct sets `A, B, C` form a
**3-sunflower** when

```
    A ∩ B  =  A ∩ C  =  B ∩ C .
```

The common value is the *core*. It may be empty, and the definition
imposes no condition that it be non-empty; three pairwise disjoint sets
are a 3-sunflower. A family is **sunflower-free** when no three of its
members form a 3-sunflower, and **intersecting** when no two of its
members are disjoint. Write

```
    g(m,n)  =  max { |F| : F ⊆ C([n],m),  F sunflower-free }
    ι(m,n)  =  max { |F| : F ⊆ C([n],m),  F sunflower-free and intersecting }
```

so that `ι(m,n) ≤ g(m,n)` for all `m` and `n`. These are the
bounded-ground-set forms of the quantities studied in [ErRa60] and
[AHS72]; the unbounded quantity `g(m) = max_n g(m,n)` is what that
literature usually writes as `f(m,3)`.

A family is a set of sets, so distinctness of members is automatic. The
Coq development represents families as lists and therefore carries
`Distinct` as an explicit hypothesis; the two notions agree.

---

## 2. The computational input

> **Proposition 1.** `g(3,8) = 12`.

This is a finite computation and it is the only input to everything that
follows, so it was carried out twice by unrelated methods.

| Method | Implementation | Result |
|---|---|---|
| Branch and bound | `rust/examples/g_small.rs` — depth-first search over the 56 candidate 3-sets, pruned by the remaining-candidates bound | `12`, in **14 294 037 nodes** |
| SAT | `tools/gsat.py` — one variable per 3-set, one clause per sunflower triple, cardinality by a sequential counter [Sinz05], solved with [CaDiCaL] | `≥ 12` satisfiable, `≥ 13` unsatisfiable |

Every satisfying assignment was decoded back into a family and re-checked
for uniformity, distinctness and sunflower-freeness before being accepted.
The two methods also agree on `g(3,6) = 10` and `g(2,6) = 6`.

A family attaining the bound, as printed by the branch-and-bound search:

```
    012  013  023  045  046  056  123  145  147  157  267  367
```

The first version of the SAT check was faulty and reported `≥ 13`
satisfiable, which would have contradicted the search and invalidated
everything below. It was caught by decoding the model. See §11.

---

## 3. The upper bound

> **Lemma 2 (link).** Let `F ⊆ C([n],4)` be sunflower-free and let
> `x ∈ [n]`. Then `L_x = { A ∖ {x} : A ∈ F, x ∈ A }` is a sunflower-free
> subfamily of `C([n] ∖ {x}, 3)`, and `|L_x| = deg_F(x)`.

*Proof.* Each `A ∖ {x}` has three elements and omits `x`. If
`A ∖ {x} = B ∖ {x}` with `x ∈ A ∩ B` then `A = B`, so the map is injective
on the members through `x` and `|L_x| = deg_F(x)`. Suppose `A ∖ {x}`,
`B ∖ {x}`, `C ∖ {x}` were distinct with common pairwise intersection `Y`.
Then `A`, `B`, `C` are distinct and their pairwise intersections are all
`Y ∪ {x}`, contradicting sunflower-freeness of `F`. ∎

In the development this is `PureLink.link_at_point_bounded`, which
predates the present note.

> **Theorem 3.** `g(4,9) = ι(4,9) = 27`.

*Proof.* Let `F ⊆ C([9],4)` be sunflower-free. For each `x ∈ [9]`,
Lemma 2 places the link `L_x` inside `C([9] ∖ {x}, 3)`, a ground set of
eight points, so Proposition 1 gives `deg_F(x) ≤ g(3,8) = 12`. Counting
the incidences `{(x, A) : x ∈ A ∈ F}` first by member and then by point,

```
    4·|F|  =  Σ_{x ∈ [9]} deg_F(x)  ≤  9 · 12  =  108 ,
```

hence `|F| ≤ 27`. The family `F₁` of §6 is a sunflower-free subfamily of
`C([9],4)` with 27 members, so `g(4,9) = 27`. Since `F₁` is also
intersecting, `ι(4,9) ≥ 27`, and with `ι ≤ g` this gives
`ι(4,9) = 27`. ∎

> **Corollary 4 (forced regularity).** Every sunflower-free
> `F ⊆ C([9],4)` with `|F| = 27` is exactly 12-regular.

*Proof.* `Σ_x deg_F(x) = 4·27 = 108 = 9·12`, and every summand is at most
12 by Lemma 2 and Proposition 1. Nine terms, each at most 12, summing to
108 forces every term to equal 12. ∎

Corollary 4 is what makes the classification of §5 tractable: once a point
reaches degree 12 it is closed to every later member, which prunes the
search decisively. Without the degree cap the Case 1 search was attempted
three times and completed none of them — 110 s unpruned, 300 s with only
the pair-degree bound, and a third run stopped by hand at about 330 s.
With the cap it completes in roughly 75 seconds.

---

## 4. Machine-checked status of §3

Theorem 3 and Corollary 4 are formalised in Coq 8.18. Proposition 1 enters
as a named hypothesis rather than an axiom:

```coq
Definition GThreeOnEight : Prop :=
  forall (V : list nat) (G : Family),
    NoDup V -> length V <= 8 ->
    Uniform 3 G -> Distinct G -> Grounded G V ->
    ~ ContainsKSunflower 3 G -> length G <= 12.

Theorem four_uniform_on_nine_at_most_27 :
  GThreeOnEight ->
  forall (U : list nat) (F : Family),
    NoDup U -> length U = 9 ->
    Uniform 4 F -> Distinct F -> Grounded F U ->
    ~ ContainsKSunflower 3 F -> length F <= 27.
```

Both `four_uniform_on_nine_at_most_27` and
`four_uniform_on_nine_is_exactly_27` report **`Closed under the global
context`** under `Print Assumptions`: no axioms and no `admit`. Carrying
computational inputs as hypotheses is this development's standing
convention, applied elsewhere to the value `g(3) = 20` of [AG69].

The double-counting step is `IotaGround.link_degree_ground_bound`, which
also predates this note.

---

## 5. Classification of the extremal families

> **Theorem 5.** Up to relabelling of the nine points there are exactly
> two sunflower-free families in `C([9],4)` of size 27: one intersecting,
> denoted `F₁`, and one not, denoted `F₂`. Consequently the extremal
> family for `ι(4,9)` is unique up to relabelling, and the extremal family
> for `g(4,9)` is not.

The proof is an exhaustive search in two cases, which are exhaustive
because a family either is or is not intersecting.

### 5.1 Case 1: `F` intersecting

Relabelling carries some member onto `A₀ = {0,1,2,3}`. Let `B ≠ A₀` be any
other member. Since `F` is intersecting and its members are distinct
4-sets, `j := |B ∩ A₀| ∈ {1,2,3}`. The setwise stabiliser of `A₀` in
`Sym([9])` is `Sym(A₀) × Sym([9] ∖ A₀)`, which for each `j` acts
transitively on `{B ∈ C([9],4) : |B ∩ A₀| = j}`; so a further relabelling
fixing `A₀` carries `B` onto the representative

```
    R₁ = {0,4,5,6}      R₂ = {0,1,4,5}      R₃ = {0,1,2,4} .
```

Every intersecting extremal family therefore has a relabelling containing
`A₀` together with some `R_j`. Searching all three sub-cases, with the
degree cap of Corollary 4:

```
    40 families found,  139 433 999 nodes,  ≈75 s
    orbits under Sym([9]): 1
```

### 5.2 Case 2: `F` not intersecting

Then `F` has two disjoint members `A, B`, and `|A ∪ B| = 8 ≤ 9`, so a
relabelling carries them onto `{0,1,2,3}` and `{4,5,6,7}`. Searching all
families containing that pair:

```
    144 families found,  15 640 126 124 nodes
    orbits under Sym([9]): 1
```

This case is not vacuous, and it is worth saying why. Three pairwise
disjoint 4-sets would need twelve points, so on nine points no three
members can have empty common pairwise intersection. Sunflower-freeness
therefore does not imply intersecting here, and disjoint pairs are
permitted.

### 5.3 Independent verification of both counts

Both searches were checked against a calculation that does not use them.
Orbits were generated by brute force over all `9! = 362 880` relabellings:

```
    |orbit(F₁)| = 280      |Aut(F₁)| = 362880 / 280  = 1296
    |orbit(F₂)| = 7560     |Aut(F₂)| = 362880 / 7560 =   48
```

From the orbit of `F₁` alone, the number of labelled copies containing
`A₀` together with `R_j` is

```
    j = 1 : 18       j = 2 : 10       j = 3 : 12       total 40
```

which is the Case 1 count. From the orbit of `F₂` alone, the number of
labelled copies containing a fixed disjoint pair is

```
    |orbit(F₂)| · (disjoint pairs in F₂) / (disjoint pairs of 4-sets in [9])
        =  7560 · 6 / 315  =  144
```

which is the Case 2 count.

Both predictions are computed from the orbits alone and make no reference
to the searches. Because each **matches** the observed count rather than
merely bounding it, they confirm the searches in both directions: nothing
in those two orbits was missed, and no third isomorphism class meets
either search space, since a third class intersecting the search space
would have pushed the observed counts above 40 and 144 respectively.

---

## 6. The two families

Points are `0,…,8`; each group of four digits is one member.

### `F₁` — intersecting, `|Aut(F₁)| = 1296`

This is the Abbott–Hanson–Sauer substitution [AHS72] of the triangle into
itself, `ι(2)·ι(2)² = 3·9 = 27`. In the development it is `Product.iota4`.

```
    0123  0124  0134  0235  1235  0245  1245  0345  1345
    0167  2367  2467  3467  0567  1567
    0168  2368  2468  3468  0568  1568
    0178  2378  2478  3478  0578  1578
```

### `F₂` — not intersecting, `|Aut(F₂)| = 48`, six disjoint pairs

```
    0123  4567  0124  0134  0234  1234  0156  0256  3456
    0157  0257  3457  1267  3467  3567
    1358  2358  1458  2458  1268  0368  0468
    1278  0378  0478  1678  2678
```

Verified for both families: 27 members, 4-uniform, distinct, no
3-sunflower, support exactly `[9]`, 12-regular as Corollary 4 requires,
and maximum pair-degree 6. The last figure is `g(2) = 6`, so the pair
bound is attained in both.

The two are non-isomorphic, and this does not depend on the canonical form
used in §5.3: their automorphism groups have different orders, 1296
against 48. The value `|Aut(F₁)| = 1296` was obtained independently with
`nauty` [MP14] in earlier work in this repository, so it serves as a check
against an outside tool rather than a restatement of our own computation.

---

## 7. Reach of the method

The link-and-count argument of §3 is sharp at nine points and does not
extend.

| `n` | Degree bound | Yields | Bearing on `ι(4,11) ≥ 32` |
|---|---|---|---|
| 9 | `g(3,8) = 12` | `\|F\| ≤ 27` | attained — sharp |
| 10 | `g(3,9) = 14` | `\|F\| ≤ 35` | above 32; decides nothing |
| 11 | `g(3,10) ≥ 16` | `\|F\| ≤ 44` | above 32; decides nothing |

`g(3,9) = 14` was computed by the same branch-and-bound search
(273 104 763 nodes). To settle the eleven-point question this way one
would need `g(3,10) ≤ 12`, whereas `g(3,10) ≥ 16` is already witnessed in
this repository. The limitation is stated here rather than left for a
reader to discover.

---

## 8. Verification status

| # | Claim | Status | Artefact |
|---|---|---|---|
| 1 | `g(3,8) = 12` | computation, two independent methods | `rust/examples/g_small.rs`, `tools/gsat.py` |
| 2 | Lemma 2 (link) | Coq, closed under the global context | `PureLink.link_at_point_bounded` |
| 3 | `g(4,9) = ι(4,9) = 27` | Coq, closed, conditional on claim 1 | `Support.four_uniform_on_nine_is_exactly_27` |
| 4 | 12-regularity forced | Coq, closed, conditional on claim 1 | same file |
| 5 | exactly two isomorphism classes | computation, cross-checked (§5.3) | `rust/examples/nine_point_census.rs`, `disjoint_seed.rs` |
| 6 | `\|Aut\|` = 1296 and 48 | computation; 1296 agrees with `nauty` [MP14] | `rust/tests/nine_points.rs` |
| 7 | both families are valid | Coq for `F₁`; Rust and Python for both | `Product.iota4_*`, `rust/tests/nine_points.rs` |

---

## 9. Reproduction

Environment: Coq 8.18.0, rustc 1.94.1, CaDiCaL 1.7.3, Intel Xeon @
2.80 GHz, four cores. Timings are single-core wall clock and vary by a
percent or two between runs; the **node counts are deterministic** and are
the figures to reproduce.

```bash
# Proposition 1, and the inputs for n = 9, 10
cd rust && cargo build --release --examples
./target/release/examples/g_small 3 8            # 12,  14 294 037 nodes
./target/release/examples/g_small 3 9            # 14, 273 104 763 nodes
python3 ../tools/gsat.py                         # independent SAT check

# Theorem 5
./target/release/examples/nine_point_census 27   # Case 1: 40 families, 1 orbit
./target/release/examples/disjoint_seed 27       # Case 2: 144 families, 1 orbit

# Coq
cd .. && make -j4 verify                         # all audited theorems closed
make coqchk                                      # independent kernel re-check

# The claims as falsifiable tests
cd rust && cargo test --release --test nine_points
```

`tools/gsat.py` validates its own cardinality encoding against brute force
on every `n ≤ 7` before using it, and re-verifies every satisfying
assignment as a family. Both guards exist because of the error recorded in
§11.

---

## 10. What is not established

1. **Proposition 1 is a computation, not a proof object.** The Coq
   theorems of §4 are explicitly conditional on `GThreeOnEight`. Two
   independent implementations agree and every SAT model was re-verified,
   but neither constitutes a formal proof.
2. **The searches of §5 are Rust programs.** Their correctness rests on
   the symmetry reductions proved in §5.1 and §5.2, on the degree cap of
   Corollary 4, which is machine-checked, and on the implementations. The
   orbit checks of §5.3 match exactly rather than merely bounding, which
   is strong evidence, but they are not a formal proof of the enumeration.
3. **The literature search is not exhaustive.** See §12.
4. Nothing here bears on `ι(4)` itself, on the Erdős–Rado conjecture
   [ErRa60], or on the open eleven-point question; §7 states the reason
   precisely.

---

## 11. Errata and methodological notes

Both are recorded because each is the kind of error that produces a wrong
result quietly.

**A faulty cross-check nearly produced a false refutation.** The first SAT
check of Proposition 1 reported `≥ 13` satisfiable, contradicting the
branch-and-bound result and, had it been believed, invalidating everything
downstream. The model was decoded before being accepted and contained only
twelve sets: the hand-written sequential counter was too weak, and the
search had never been wrong. The encoding was rewritten following
[Sinz05] and validated exhaustively against brute force on every `n ≤ 7`
and `k ≤ n+2` before being used again. The general lesson is narrow and
practical: a cross-check that disagrees with the thing it checks says
nothing about that thing until the check itself has been checked.

**A scratch script miscounted disjoint pairs.** Iterating pairs as
`for A in F for B in F if A < B` over Python `frozenset` objects uses `<`
as proper subset rather than as an order, and reported zero disjoint pairs
for both families. Recounted with `itertools.combinations`, `F₁` has none
and `F₂` has six, which is what the Rust test had asserted throughout. No
published figure was affected.

---

## 12. Relation to the literature

The outcome of the literature search is a negative, so its scope is given
rather than its conclusion alone.

Searched directly for this note: three targeted web searches on uniqueness
of extremal sunflower-free families and on exact values for small
parameters; and [Kup25], the most recent survey of the area, read
specifically for exact values and uniqueness statements. It contains
neither — only asymptotic bounds and structural theorems. Earlier
commissioned work in this repository, recorded in `docs/reading.md`
A17–A23, covered arXiv full-text, Google Scholar forward-citation chains
from [AHS72] and from Kostochka's survey, Springer, ScienceDirect,
zbMATH, Semantic Scholar, and all 434 comments of the seven Polymath10
threads, read first-hand.

The structural argument carries more weight than any single search. A
classification of the extremal families at `(4,9)` presupposes the value
`g(4,9) = 27`. No exact value of this kind for `m = 4` on a bounded ground
set was located anywhere; the only exact value in this area is
Abbott–Gardner's `g(3) = 20` [AG69], an unbounded-ground-set quantity. If
the value is unpublished then a classification of its extremal families is
unpublished too.

This is high confidence rather than certainty. No search proves a
negative, and the paragraph above describes what was examined, not what
exists.

Two related computational efforts should be named. [AE92] is the closest
prior computational work on sunflower-free families, but its published
results are for `r ≥ 4` and so do not bear on the `r = 3` question here.
A randomised search reported in the Polymath10 threads in 2015 reached 24
members at `m = 4`, against the 27 established above.

---

## 13. Scope

This is a small, self-contained finite result. It settles nine points
completely and, by §7, says nothing about ten or eleven. Its interest is
that the extremal number is the same for the general and the intersecting
problem while the extremal families are not: relaxing "intersecting"
admits exactly one further family and no larger one.

---

## References

Cited by key. Full entries with evidence classes are in
`docs/references.md`; the corpus of retrieved PDFs, pinned by SHA-256, is
in `docs/papers/MANIFEST.md`.

- **[AE92]** H. L. Abbott and G. Exoo, *On set systems not containing
  delta systems*. Graphs and Combinatorics **8** (1992), 1–9.
- **[AG69]** H. L. Abbott and B. Gardner, *On a combinatorial theorem of
  Erdős and Rado*. In W. T. Tutte (ed.), Recent Progress in
  Combinatorics, Academic Press, 1969, 211–215.
- **[AHS72]** H. L. Abbott, D. Hanson and N. Sauer, *Intersection
  theorems for systems of sets*. J. Combin. Theory Ser. A **12** (1972),
  381–389.
- **[CaDiCaL]** A. Biere et al., *CaDiCaL* SAT solver, version 1.7.3.
- **[ErRa60]** P. Erdős and R. Rado, *Intersection theorems for systems
  of sets*. J. London Math. Soc. **35** (1960), 85–90.
- **[Kup25]** A. Kupavskii, *Delta-system method: a survey*.
  arXiv:2508.20132 (2025).
- **[MP14]** B. D. McKay and A. Piperno, *Practical graph isomorphism,
  II*. J. Symbolic Comput. **60** (2014), 94–112.
- **[Sinz05]** C. Sinz, *Towards an optimal CNF encoding of Boolean
  cardinality constraints*. In Principles and Practice of Constraint
  Programming — CP 2005, LNCS **3709**, Springer, 827–831.
