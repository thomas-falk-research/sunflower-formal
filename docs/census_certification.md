# Certifying the census: a staged plan

**Status: stages 1 and 2 done (`coq/CensusIota.v`, and below); stages 3–5
not started.** Each stage says what it would establish and
what it would still trust. The decision points are measurements, not
opinions.

## The premise in question

`g(4) ≤ 76` (`Link21Certs.g_four_at_most_76_of_census_21`) is a kernel
theorem from three premises:

* `IotaAtMost 4 27`: no intersecting 3-sunflower-free family of 28
  distinct 4-sets;
* `CensusL classes21 21`: every such family of at least 21 members is,
  up to relabelling, one of the 491,536 listed classes (sizes 21–27);
* `MeetingBound 4 56`: [ABCDN26] Prop. 6.5.

The first two are VALIDATED, not proved: they come from an exhaustive
McKay canonical-augmentation search (`docs/ladder/iota4_replication/`),
1.06×10¹¹ orbit representatives and 8.3×10⁹ classes in about 67
core-hours, written twice independently and agreeing on an
isomorphism-invariant total to the unit. The trust base is nauty, gcc,
two C programs, McKay's theorem and the bookkeeping. A SAT/DRAT proof
is out of reach: no useful ground-set bound is known (the trivial one is
85 points; SAT stalls at 11).

## Stage 1 — one premise instead of two (`iota_of_census`)

`Covered` preserves the number of distinct members, and every listed
class has at most 27 members, so `CensusL classes21 21` implies
`IotaAtMost 4 27`: a family of 28 or more would be covered by a listed
class of the same size. The lemma is short (the maximum class size is
decided by `vm_compute`), and `g(4) ≤ 76` then rests on the census and
the meeting bound alone. This is not a reduction of trust in substance
— both premises come from the same search — but it makes the paper's
assumption one precise statement. *Done:* `CensusIota.iota_of_census` and
`CensusIota.g_four_at_most_76_of_census`, closed under the global
context, `coqchk` passing (roadmap §74).

## The idea: certify completeness only

For "nothing at 28" and "every family ≥ 21 is listed", a search may do
redundant or duplicate work freely; it must never *discard* a class.
So the task is to make every pruning step justify itself locally, with
nauty demoted to an untrusted oracle that proposes witnesses.

* **Orbit merging** (children identified by an automorphism of the
  parent) is locally checkable: apply the claimed automorphism and
  compare. Missing automorphisms only merge less.
* **Canonical deletion** (McKay's test) is not: it is correct only
  because the canonical labelling is isomorphism-invariant across
  different nodes. Two ways around it:
  1. **Orderly generation with witness pruning** (chosen for stage 2).
     Order labelled families; keep a node unless the oracle supplies a
     relabelling π with π(N) ≺ N, which is checked. A lemma proved once
     — deleting the largest row of an order-minimal family leaves an
     order-minimal family — makes the search complete *whatever the
     oracle does*: the minimal member of each class has no witness
     against it, so it is never pruned, and neither are its ancestors.
  2. **Certified canonical labelling**: nauty-style search with a
     certificate per canonical form, checked by a verified checker
     (prior work on this exists for graphs, in Isabelle; to be
     identified precisely before it is cited). Keeps the fast
     algorithm, at one certificate per node.

**The order.** A row (a member) is its bitmask `Σ 2^x`, a natural
number; a family is the ascending sorted list of its row masks; families
of equal size are compared lexicographically. *Hereditary lemma:* let
`F = G + r` with `r` the largest row. If some relabelling π has
`π(G) ≺ G`, then `π(F) ≺ F`. Sketch: let `i` be the first position
where `π(G)` and `G` differ, `π(G)_i < G_i`. Inserting `π(r)` into
`π(G)` either lands before position `i` — then at its position it is
smaller than the corresponding row of `G`, which is unchanged in `F` up
to there — or at or after `i`, and then position `i` already decides;
`F` is `G` followed by `r`, so it agrees with `G` at every position
`≤ i`. Either way `π(F) ≺ F`. Two further facts make the search finite
on an unbounded ground set: a minimal family uses exactly the labels
`0..v−1` (moving a used label onto a smaller unused one decreases every
affected mask and so the sorted list), and so the children of a node on
`v` points need only rows inside `0..v+3`.

## The obstacle is scale, and LPCert can shrink it

Some 10¹¹ certificates are far beyond the kernel. Two levers:

* **Prune with certified bounds.** A census of classes of size ≥ 21
  never needs to expand a node that cannot grow to 21. The extensions of
  a partial family form a finite candidate set (up to fresh points);
  disjoint pairs and sunflower triples are the conflict rows; so "cannot
  reach 21" is an integer program, and that is what `LPCert` certifies.
  The class counts suggest most nodes at sizes 15–20 are dead ends (308
  million classes at 20, 407 thousand at 21), but **how much this prunes
  is unmeasured**, and it decides everything below.
* **Where the check runs.** The kernel (`vm_compute`/`native_compute`)
  if pruning brings the count to roughly 10⁷–10⁸; otherwise a verified
  program (Coq extracted to OCaml — extraction and the OCaml runtime then
  trusted — or CakeML for an end-to-end verified binary). The slowdown
  against the C search is unmeasured.

## Stages

| stage | work | establishes | still trusted |
|---|---|---|---|
| 1 | `iota_of_census` | one premise instead of two | the census |
| 2 | Coq: orderly generation with witness pruning, generic in the hereditary, relabelling-invariant property; the hereditary lemma; label compression; "every valid family is covered by a kept node"; `CensusL` from a search whose levels ≥ 21 are covered by the list and whose level 28 is empty — the oracle abstract. A small instance run in the kernel end to end. | the mathematics of a certified census, independent of how it is executed | — (no computation at scale yet) |
| 3 | measurement: the existing search with LPCert "cannot reach 21" pruning, counting surviving nodes | which execution route is feasible | — |
| 4 | the certifying search at scale, nauty as the witness oracle, every witness checked | `CensusL classes21 21` as a theorem | the kernel, or extraction + OCaml, or CakeML |
| 5 (optional, independent) | a third search with a different canonicaliser (Traces or bliss); mass-formula checks (labelled counts against Σ n!/\|Aut\|) at small sizes | stronger validation without proofs | as now |

Decision point after stage 3: about 10⁸ surviving nodes or fewer → a
kernel-checked census; otherwise the extracted or CakeML route.

## Stage 2 — done

`coq/CensusGen.v`, `coq/CensusSearch.v` and `coq/CensusDemo.v`, all in
the theory build and all closed under the global context
(`make print-assumptions`):

* **The order and the hereditary lemma.** `lexb_insert_last`,
  `parent_improves`: a relabelling that improves the parent improves the
  child. `MinK_parent`: the parent of a minimal node is minimal.
* **No gaps.** `gap_improves`: an unused label below the largest one
  can be swapped in to strictly improve the family, via
  `lexb_first_diff` (the order on strictly sorted lists through the
  smallest element of the symmetric difference). `MinK_no_gap`,
  `last_in_cand`: the largest row of a minimal node is among its parent's
  candidates, the `b`-subsets of `0 .. nl + b − 1`.
* **Witnesses.** A witness is a list checked by `is_permb` (a
  permutation of `0 .. n − 1`, the identity above), with a proved
  inverse; the oracle is any function, and a node is pruned only when its
  witness checks and has exactly the node's label range.
* **Completeness.** `level_complete`: every minimal node whose family
  has the property is in its level and is kept, *whatever the oracle
  answers*. `minimal_relabel`: every family with distinct rows has a
  minimal relabelling (the least key over all permutations of its label
  range, `argmin_spec`, with `perms_complete` and composition).
* **The census.** `census_of_search`: if every node kept at levels
  `lo .. hi` is covered by a class of `L` and no node is kept at level
  `hi + 1`, then `CensusB b L lo` — for `b = 4` exactly
  `Link23.CensusL L lo` (`CensusB_4`). `iota_of_search` is the case
  `L = []`. The node test need only accept every valid node
  (`validb_complete` for the concrete `validb b`); it never has to be
  proved to reject anything.
* **End to end in the kernel at `b = 2`.** `CensusDemo.iota_two_by_search`:
  `ι(2) ≤ 3` by running the search with `vm_compute` and no oracle at
  all (levels of 1, 1, 4, 2, 0 nodes).

One lesson recorded: `CensusGen` first reused five names of the library
(`mask`, `mask_bit`, `nodupb`, `rmapF`, `subsets`). With every module
loaded, existing statements then printed with qualified names and the
statement baseline flagged them as changed; the definitions were renamed
and the baseline diff is now the new entries only.

**What stage 2 leaves open.** The coverage hypothesis of
`census_of_search` (each kept node at levels `lo .. hi` covered by a
class) is abstract; for execution it needs a checked form (a witness
permutation and a class index per node, checked by comparing keys),
which belongs with stage 4.

**Measured for the pilot at `b = 3`.** Without an oracle the levels
grow about seventeen-fold per row (1, 1, 18, 513, 8,511 nodes at rows
0–4, `vm_compute`), so even `ι(3) = 10` needs pruning. The oracle can be
a precomputed table looked up by a hash of the node: collisions or wrong
entries cost only extra work, never soundness, because every witness is
checked. `ι(3) ≤ 10` through that route is the natural pilot before
stage 3's measurement at `b = 4`.

## Precedents (from memory; each to be checked before it is cited)

Flyspeck's tame-graph enumeration verified in Isabelle (including
isomorphism checking); Keller's conjecture and the empty hexagon (SAT
with DRAT proofs and verified symmetry-breaking encodings); R(4,5) = 25
formalised in HOL4 (Gauthier and Brown, 2024), which had to handle
isomorphism classes of graphs; VeriPB proof logging with symmetry and
dominance rules (Bogaerts, Gocht, McCreesh, Nordström) and the verified
CakePB checker. None of these did an isomorph-free enumeration at this
scale over an unbounded ground set.
