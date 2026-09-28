# ι(4) ≤ 27 — an independent replication

**Verdict: VALIDATED, not PROVEN.** An exhaustive isomorph-free search,
written independently of the one in arXiv:2609.06175 (Axante, Budala,
Chitic, Dumitru, Nacu, Prop. 6.8), finds **no intersecting,
3-sunflower-free family of 28 distinct 4-sets on any ground set**. It
reaches depth 27 (the Abbott–Hanson family), and finds **exactly one
isomorphism class there**. In the repository's terms this is evidence for
`IotaRate.IotaAtMost 4 27`. It is a second computation, not a certificate:
nothing here can be checked without re-running a search of the same size.

## The one number that makes it more than "a second program said so"

The number of orbit representatives a correct canonical-augmentation
search visits is an isomorphism invariant: it is the sum, over every
isomorphism class of valid families of size 6 to 27, of the number of
`Aut`-orbits of its valid one-row extensions. Any two correct searches
must report the same total, whatever their canonical-deletion rule.

```text
  arXiv:2609.06175 archived run, 11720 shard logs, sum of nodes=   105,917,089,577
  minus one root node counted per shard                         -           11,720
  predicted for this search                                        105,917,077,857
  this search, audit.py, "visited orbit representatives"           105,917,077,857
```

Equal to the unit. The two programs share only nauty (different
releases: 2.8.9 there, 2.8.8 here); candidate generation, canonical
deletion rule, orbit merging, sharding and bookkeeping are all different.
A completeness bug in either would have to remove exactly as many orbit
representatives as a bug in the other adds, at the same total.

## What was run

| item | value |
|---|---|
| program | `tools/iota4/isearch.c` for chunks started before 2026-09-27T22:13:51Z, then `tools/iota4/isearch2.c` for chunks started after it — output-identical, see below |
| nauty | 2.8.8, from the pynauty 2.8.8.1 sdist |
| compiler | gcc 13.3.0, `-O3 -march=native` |
| frontier | depth 6, 11720 classes, `d6.txt.gz` (sha256 in `d6.sha256`) |
| ledger | `logs/chunk_*.log`: 293 chunks × ≤ 40 shards, each record `SHARD i ... NONE visited=… time=…` + per-depth `ACCEPTED` vector, each chunk ending `DONE exit=20` |
| split shards | 1522, 1565, 1813, 6550 run as their depth-10 descendants (`emit_*.log` + `split_batches.tsv`), folded back into one record by `tools/iota4/combine.py` |
| solver time | 242,061 s of per-shard wall time summed over the records (≈ 67 h; an upper bound on CPU, as the run was at times oversubscribed), 4 cores, 2026-09-27 15:28 → 2026-09-28 05:10 UTC; plus roughly 10–15 core-hours discarded when heavy shards were stopped and split |
| audit | `python3 tools/iota4/audit.py docs/ladder/iota4_replication/logs <(zcat docs/ladder/iota4_replication/d6.txt.gz)` → `AUDIT PASS` |

Full sub-shard logs were not committed (25 MB compressed):
`split_sublogs.tgz` sha256 `46b1b8817481763303fb85f7c9cc3488a9973e5e310eb3604b78fe6a692bb496`,
sub-shard frontiers `subs.tgz` sha256
`9bb8355dd209674d739d45021df7c0b5081abe218fe6dfe197860455cf997b43`.
`split_batches.tsv` is their per-batch summary, and re-derives each
split shard's committed record exactly.

## Isomorphism classes of intersecting 3-sunflower-free families of 4-sets

Every class of every size, on every ground set (a complete census, since
nothing was found at 28 and the search does not stop early otherwise):

```text
  size  classes            size  classes
    0   1                   15   867,480,975
    1   1                   16   847,743,828
    2   3                   17   914,824,721
    3   14                  18   955,491,548
    4   104                 19   748,933,702
    5   993                 20   308,191,503
    6   11,720              21   407,115
    7   133,931             22   69,616
    8   1,266,326           23   12,524
    9   8,986,483           24   1,976
   10   45,743,106          25   298
   11   163,237,419         26   6
   12   404,322,516         27   1
   13   697,302,136         28   0
   14   868,085,917
```

Sizes 0–5 were checked against a nauty-free oracle (`tools/iota4/oracle.py`,
networkx VF2), size 6 too (11,720), and sizes 6, 7, 8 against
the paper's program (`-e 6/7/8`: 11,720, 133,931, 1,266,326).

Two features, neither claimed as novel:

* **The extremal family is unique.** One class at 27. The 9-point run
  (`control_C9_m28.log`: no 28-family on ≤ 9 points, exactly one class at
  27) shows it lives on nine points, where §38 of the roadmap already had
  it "in essentially one way". This makes it the Abbott–Hanson family
  `Product.iota4`, the one the 9-point search found and `verify` checked.
* **A cliff after 20.** 308 million classes at 20, 407 thousand at 21.

## Controls and cross-checks

| check | result |
|---|---|
| known values, same program | ι(2) = 3, ι(3) = 10, g(2) = 6 |
| nauty-free oracle (VF2) | k=3 intersecting full series; k=2 general; k=4 intersecting sizes 0–6 |
| fresh-context reviewer's own brute force (no nauty) | 8 further series incl. k=4 intersecting on ≤ 7 points (full), k=5 intersecting on ≤ 8 points to size 8 — all equal |
| candidate generator vs brute force | 300 random cases, 27.5 M candidates, identical |
| canonical-deletion invariance | 3000 randomly relabelled symmetric families, 0 failures, every generator an automorphism |
| shard mode = whole run | depth-5 frontier on ≤ 8 points, every depth equal |
| positive control | 27-family found on ≤ 9 points (verified independently in Python); depth 27 reached in the main run |
| negative control | no 28-family on ≤ 9 points, agreeing with the repository's two-solver `ι(4,9) = 27` |
| split = unsplit | shard 1537 split at depth 10 reproduces its direct record exactly |
| isearch2 = isearch | identical output on 5 validation series and 120 real shards and sub-shards |
| **invariant total** | **105,917,077,857 = paper total − 11,720** |

## What this does not establish

* **It is not a proof certificate.** Trust rests on nauty 2.8.8, gcc, the
  two C sources, the McKay canonical-augmentation theorem, and the shell
  and Python bookkeeping — all reviewed, none machine-checked. A DRAT
  certificate is out of reach because no useful ground-set bound is known
  (the trivial one is 85 points; SAT stalls at 11 at this target).
* **It is not independent of nauty.** Both searches use it; the nauty-free
  checks stop at size 6 (whole problem) and at ≤ 7–8 points.
* **The run was not clean-room.** The author read the paper's program
  before writing this one. The design differs deliberately at every step,
  but the framework (row-by-row canonical augmentation, fresh columns) is
  the same.
* **Operational events**, all visible in the ledger's construction:
  three heavy shards were stopped after hours and re-run split; one
  worker pool was killed by an over-broad `pkill` and restarted; chunk
  logs 6520, 10080, 10360 were assembled from a stopped worker's finished
  records plus separately run shards (`tools/iota4/combine.py`, and
  `tools/iota4/rebuild.py`). The auditor requires every one of
  the 11720 shard indices exactly once with a `NONE` verdict, and passes.
