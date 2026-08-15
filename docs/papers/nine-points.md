# The extremal 4-uniform sunflower-free families on nine points

**Claim.** `g(4,9) = ι(4,9) = 27`, and up to relabelling there are exactly
two extremal families — one intersecting, one not.

Canonical version of this note: `docs/papers/nine-points.md` in
`thomas-falk-research/sunflower-formal`, branch
`claude/sunflower-session-n11-mkonqv`. Every number below is reproducible
by a command given in §9.

---

## 1. Definitions

Let `[n] = {0, 1, …, n−1}` and let `C([n], m)` be the `m`-subsets of `[n]`.

Three **distinct** sets `A, B, C` form a **3-sunflower** when

```
    A ∩ B  =  A ∩ C  =  B ∩ C .
```

The common value is the *core*, and it may be empty. A family is
**sunflower-free** when no three of its members form a 3-sunflower. A
family is **intersecting** when no two members are disjoint.

```
    g(m,n)  =  max { |F| : F ⊆ C([n],m), F sunflower-free }
    ι(m,n)  =  max { |F| : F ⊆ C([n],m), F sunflower-free and intersecting }
```

Trivially `ι(m,n) ≤ g(m,n)`.

*Note on distinctness.* A family here is a set of sets, so distinctness is
automatic. The Coq development represents families as lists and therefore
carries `Distinct` as an explicit hypothesis; the two agree.

---

## 2. The input: `g(3,8) = 12`

> **Proposition 1.** `g(3,8) = 12`.

This is a finite computation and it is the only external input to
everything that follows. It was verified **twice, by unrelated methods**:

| method | how | result |
|---|---|---|
| Branch and bound | `rust/examples/g_small.rs`, DFS over the 56 candidate 3-sets, pruned by the standard remaining-candidates bound | `12`, in **14 294 037 nodes**, ≈2.9 s |
| SAT | one Boolean per 3-set, one clause per sunflower triple, cardinality by a Sinz sequential counter, solved with `cadical` 1.7.3 | `≥ 12` **SAT**, `≥ 13` **UNSAT** |

Every SAT model was decoded back to a family and re-checked for
uniformity, distinctness and sunflower-freeness before being believed.
The same pair of methods agrees on `g(3,6) = 10` and `g(2,6) = 6`.

An attaining family, printed by the DFS:

```
    012  013  023  045  046  056  123  145  147  157  267  367
```

> The first SAT encoding written for this check was **wrong** and reported
> `≥ 13` as satisfiable. It was caught by decoding the model, which
> contained only 12 sets. See §11.

---

## 3. Upper bound

> **Lemma 2 (link).** Let `F ⊆ C([n],4)` be sunflower-free and `x ∈ [n]`.
> Then `L_x = { A \ {x} : A ∈ F, x ∈ A }` is a sunflower-free subfamily of
> `C([n] \ {x}, 3)` with `|L_x| = deg_F(x)`.

*Proof.* Each `A \ {x}` has three elements. If `A \ {x} = B \ {x}` with
`x ∈ A ∩ B` then `A = B`, so the map is injective and `|L_x| = deg_F(x)`.
If `A\{x}, B\{x}, C\{x}` are distinct with common pairwise intersection
`Y`, then `A, B, C` are distinct with common pairwise intersection
`Y ∪ {x}`, contradicting sunflower-freeness of `F`. ∎

This is `PureLink.link_at_point_bounded` in the Coq development.

> **Theorem 3.** `g(4,9) = ι(4,9) = 27`.

*Proof.* Let `F ⊆ C([9],4)` be sunflower-free. By Lemma 2 every degree
satisfies `deg(x) ≤ g(3,8) = 12` (Proposition 1). Counting incidences
`{(x,A) : x ∈ A ∈ F}` in both directions,

```
    4·|F|  =  Σ_{x ∈ [9]} deg(x)  ≤  9 · 12  =  108 ,
```

so `|F| ≤ 27`. The family `F₁` of §6 has 27 members, lies in `C([9],4)`,
and is sunflower-free, so `g(4,9) = 27`. `F₁` is also intersecting, so
`ι(4,9) ≥ 27`, and `ι ≤ g` gives `ι(4,9) = 27`. ∎

> **Corollary 4 (forced regularity).** Every 27-member sunflower-free
> `F ⊆ C([9],4)` is exactly 12-regular.

*Proof.* `Σ deg(x) = 108 = 9·12` with every `deg(x) ≤ 12` leaves no
slack. ∎

Corollary 4 is what makes §5 finish: a point that reaches degree 12 is
closed to every later member. Without the degree cap the same Case 1
search was attempted three times and terminated none of them — 110 s
unpruned, 300 s with only the pair-degree bound, and a third run stopped
by hand at about 330 s. With the cap it finishes in ≈75 s.

---

## 4. Machine-checked status

Theorem 3 and Corollary 4 are formalised in Coq 8.18:

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
context`** — no axioms, no `admit`. Proposition 1 enters as the
hypothesis `GThreeOnEight`, never as an axiom; the development carries
computational inputs this way throughout.

The counting step is `IotaGround.link_degree_ground_bound`, which predates
this note.

---

## 5. Classification

> **Theorem 5.** Up to relabelling of the nine points there are exactly
> **two** sunflower-free families in `C([9],4)` of size 27: one
> intersecting (`F₁`) and one not (`F₂`). In particular the extremal
> family for `ι(4,9)` is **unique**, and the extremal family for `g(4,9)`
> is **not**.

The two cases are exhaustive, and each was searched to the end.

**Case 1: `F` intersecting.** Relabel a member onto `A₀ = {0,1,2,3}`. Let
`B ≠ A₀` be another member. Since `F` is intersecting and its members are
distinct 4-sets, `j = |B ∩ A₀| ∈ {1,2,3}`. The stabiliser of `A₀` is
`Sym(A₀) × Sym([9]\A₀)` and acts transitively on `{B : |B ∩ A₀| = j}`, so
a further relabelling fixing `A₀` carries `B` onto the representative

```
    R₁ = {0,4,5,6}      R₂ = {0,1,4,5}      R₃ = {0,1,2,4}
```

Hence every intersecting extremal family has a relabelling containing
`A₀` and some `R_j`. Searching all three, with the degree cap of
Corollary 4:

```
    40 families found,  139 433 999 nodes,  ≈75 s
    orbits under Sym([9]): 1
```

**Case 2: `F` not intersecting.** Then `F` has two disjoint members `A, B`
with `|A ∪ B| = 8 ≤ 9`, so a relabelling carries them onto `{0,1,2,3}`
and `{4,5,6,7}`. Searching all families containing that pair:

```
    144 families found,  15 640 126 124 nodes
    orbits under Sym([9]): 1
```

The node count is from a completed run and is deterministic. Its wall
time was not captured, and a timed re-run was still going at 39 minutes
single-core when this was written; treat the cost as "tens of minutes"
rather than any figure this note could stand behind.

Note that disjointness is *possible* here: three pairwise disjoint 4-sets
would need twelve points, so on nine points an empty-core sunflower cannot
occur and sunflower-freeness does not imply intersecting. This is exactly
why Case 2 is non-empty.

### 5.1 Independent verification of both counts

The two searches were checked against a computation that does not use them.
Orbits were generated by brute force over all `9! = 362 880` relabellings:

```
    |orbit(F₁)| = 280     |Aut(F₁)| = 362880/280 = 1296
    |orbit(F₂)| = 7560    |Aut(F₂)| = 362880/7560 =   48
```

From the orbit of `F₁` alone, the number of labelled copies containing
`A₀` together with `R_j` is

```
    j = 1 : 18      j = 2 : 10      j = 3 : 12      sum = 40
```

which is exactly what the Case 1 search reported. From the orbit of `F₂`
alone, the number of labelled copies containing a *fixed* disjoint pair is

```
    |orbit(F₂)| · (disjoint pairs in F₂) / (disjoint pairs of 4-sets in [9])
      =  7560 · 6 / 315  =  144
```

which is exactly what the Case 2 search reported.

These predictions are computed from the orbits only. They confirm the
searches in both directions: the searches missed nothing in those orbits,
and — because the totals *match* rather than merely bound — no further
orbit meets either search space. Had a third class existed and met the
search space, the observed counts would have exceeded 40 and 144.

---

## 6. The two families

Points are `0…8`; each row is one member.

**`F₁` — intersecting, `|Aut| = 1296`.** This is the Abbott–Hanson–Sauer
substitution of the triangle into itself, `ι(2)·ι(2)² = 3·9 = 27`; it is
`Product.iota4` in the development.

```
0123  0124  0134  0235  1235  0245  1245  0345  1345
0167  2367  2467  3467  0567  1567
0168  2368  2468  3468  0568  1568
0178  2378  2478  3478  0578  1578
```

**`F₂` — not intersecting, `|Aut| = 48`, six disjoint pairs.**

```
0123  4567  0124  0134  0234  1234  0156  0256  3456
0157  0257  3457  1267  3467  3567
1358  2358  1458  2458  1268  0368  0468
1278  0378  0478  1678  2678
```

Shared invariants, verified for both: 27 members, 4-uniform, distinct,
zero 3-sunflowers, support exactly `[9]`, **12-regular**, and maximum
pair-degree **6** — which is `g(2) = 6`, so the pair bound is attained in
both.

`F₁` and `F₂` are non-isomorphic. This needs no canonical form: their
automorphism groups have different orders, 1296 against 48. The value
`|Aut(F₁)| = 1296` was independently obtained from `nauty` in earlier work
on this repository, so it is a check against an outside tool rather than a
restatement of our own.

---

## 7. Where the method stops

The link-plus-counting argument of §3 is sharp at nine points and reaches
no further:

| `n` | degree bound | gives | against the open question `ι(4,11) ≥ 32` |
|---|---|---|---|
| 9 | `g(3,8) = 12` | `\|F\| ≤ 27` | attained — **sharp** |
| 10 | `g(3,9) = 14` | `\|F\| ≤ 35` | above 32, decides nothing |
| 11 | `g(3,10) ≥ 16` | `\|F\| ≤ 44` | above 32, decides nothing |

`g(3,9) = 14` was computed the same way (273 104 763 nodes, ≈74 s). To
settle the eleven-point question this way one would need `g(3,10) ≤ 12`,
while `g(3,10) ≥ 16` is already witnessed. The method therefore does not
extend, and that limit is stated here rather than left for a reader to
discover.

---

## 8. Verification status, claim by claim

| # | claim | status | artefact |
|---|---|---|---|
| 1 | `g(3,8) = 12` | computation, **two independent methods** | `rust/examples/g_small.rs`; SAT script in §9 |
| 2 | link lemma | **Coq**, closed | `PureLink.link_at_point_bounded` |
| 3 | `g(4,9) = ι(4,9) = 27` | **Coq**, closed, conditional on claim 1 | `Support.four_uniform_on_nine_is_exactly_27` |
| 4 | 12-regularity forced | **Coq**, closed, conditional on claim 1 | same file |
| 5 | exactly two orbits | computation, cross-checked orbit-theoretically | `rust/examples/nine_point_census.rs`, `disjoint_seed.rs` |
| 6 | `\|Aut\|` = 1296, 48 | computation; 1296 agrees with `nauty` | `rust/tests/nine_points.rs` |
| 7 | the two families are valid | **Coq** for `F₁`, Rust + Python for both | `Product.iota4_*`; `rust/tests/nine_points.rs` |

---

## 9. Reproduction

Environment: Coq 8.18.0, rustc 1.94.1, cadical 1.7.3, Intel Xeon @ 2.80 GHz,
4 cores.

Timings are wall-clock on one core and vary by a percent or two between
runs; the **node counts are deterministic** and are the figure to
reproduce. Where a timing is given it is one measured run, not an
average.

```bash
# Proposition 1 and the n = 9, 10 inputs
cd rust && cargo build --release --examples
./target/release/examples/g_small 3 8      # g(3,8) = 12,  14 294 037 nodes
./target/release/examples/g_small 3 9      # g(3,9) = 14, 273 104 763 nodes
python3 ../tools/gsat.py                   # SAT cross-check of the same values

# Case 1 of Theorem 5 — intersecting census
./target/release/examples/nine_point_census 27      # 40 families, 1 orbit

# Case 2 of Theorem 5 — the disjoint-pair search
./target/release/examples/disjoint_seed 27          # 144 families, 1 orbit

# The Coq side
cd .. && make -j4 verify        # every audited theorem: Closed under the global context
make coqchk                     # independent kernel re-check

# The claims as falsifiable tests
cd rust && cargo test --release --test nine_points
```

The SAT cross-check of Proposition 1 is a short standalone script; it
builds one variable per 3-set, one clause per sunflower triple, a Sinz
sequential counter for the cardinality bound, and calls `cadical`. It is
reproduced in the repository alongside this note.

---

## 10. What is **not** proved

Stated plainly, because the value of the note depends on it.

1. **Proposition 1 is a computation, not a machine-checked proof.** The
   Coq theorems are explicitly conditional on `GThreeOnEight`. Two
   independent implementations agree, and every SAT model was re-verified,
   but neither is a proof object.
2. **The censuses of §5 are Rust programs.** Their correctness rests on
   the symmetry reductions (proved above), the degree cap (Corollary 4,
   machine-checked), and the implementations. The orbit-theoretic checks
   of §5.1 are strong — they match exactly rather than merely bounding —
   but they are not a formal proof of the enumeration.
3. **The prior-art search is not exhaustive.** See §12.
4. Nothing here bears on `ι(4)` itself, on the Erdős–Rado conjecture, or
   on the open `ι(4,11)` question; §7 gives the precise reason.

---

## 11. Errata and methodological notes

Recorded because both are the kind of error that silently produces a wrong
paper.

**A wrong cardinality encoding nearly produced a false refutation.** The
first SAT check of Proposition 1 reported `≥ 13` as *satisfiable*, which
would have contradicted the branch-and-bound result and invalidated
everything downstream. The model was decoded before being believed and
contained only 12 sets: the hand-rolled sequential counter was too weak,
not the DFS wrong. The encoding was rewritten as a standard Sinz counter
and **validated exhaustively on every `n ≤ 7` and `k ≤ n+2`** against
brute-force truth before being used again. The lesson is narrow and
practical: a cross-check disagreeing with the thing it checks is not
evidence about the thing until the check itself has been checked.

**A scratch script miscounted disjoint pairs.** Iterating pairs with
`for A in F for B in F if A < B` over Python `frozenset`s uses `<` as
*proper subset*, not as an order, and reported zero disjoint pairs for
both families. Recounted with `itertools.combinations`: `F₁` has 0, `F₂`
has 6, which is what the Rust test asserted throughout. No published
number was affected.

---

## 12. Prior art

The literature was searched and the outcome is a negative, so the scope of
the search is given rather than the conclusion alone.

Searched: three targeted web searches on sunflower-free uniqueness and on
exact small values; the most recent survey in the area, *Delta-system
method: a survey* (arXiv:2508.20132, August 2025), read specifically for
exact values and uniqueness statements — it contains **neither**, only
asymptotics and structural theorems. Earlier commissioned work on this
repository covered arXiv full-text, Google Scholar forward-citation chains
from Abbott–Hanson–Sauer 1972 and from Kostochka's survey, Springer,
ScienceDirect, zbMATH, Semantic Scholar, and all 434 comments of the seven
Polymath10 threads read first-hand.

The structural argument is stronger than any single search. A uniqueness
theorem at `(4,9)` presupposes the **value** `g(4,9) = 27`. No exact value
of this kind for `k = 4` on a bounded ground set appears anywhere located;
the only exact value in the area is Abbott–Gardner's `g(3) = 20` (1969),
which is an unbounded-ground-set quantity. If the value is unpublished, a
classification of its extremal families is too.

That is **high confidence, not certainty**. No search proves a negative,
and this paragraph is offered as a description of what was looked at, not
as a claim about what exists.

---

## 13. Acknowledgement of scope

This is a small, self-contained finite result. It settles nine points
completely and, by §7, says nothing about ten or eleven. Its interest is
that the extremal number is the same for the general and the intersecting
problem while the extremal *families* are not: relaxing "intersecting"
admits exactly one further family and no larger one.
