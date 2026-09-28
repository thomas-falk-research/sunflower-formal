# tools/iota4 — independent exhaustive search for ι(4)

The program and scripts behind `docs/ladder/iota4_replication/`, which
records the run and its verdict. Read that file first.

| file | role |
|---|---|
| `isearch.c` | the search: McKay canonical augmentation over rows (members), candidate rows as hitting sets, minimum-invariant canonical deletion, nauty for canonical labelling and automorphisms, hash-based orbit merging. `-k -m -I -C -e -o -r -l -n`, see the header comment |
| `isearch2.c` | the same algorithm with a trace-bucketed sunflower test and incremental invariants; output-identical to `isearch.c` (validated on 5 series and 120 shards) and ≈ 1.45× faster |
| `run.sh` | **reusable entry point**: build, emit the depth-6 frontier, run all 11720 shards resumably. `tools/iota4/run.sh <nauty-src> <work-dir> [jobs]` |
| `audit.py` | the ledger auditor: every shard once, every verdict `NONE`, every chunk `DONE exit=20`, per-depth class totals, the invariant visited total |
| `oracle.py` | nauty-free class counts (networkx VF2), for small sizes |
| `tests/` | the fresh-context reviewer's harnesses: `bf.c` (nauty-free brute-force class counts), `candtest.c` (candidate generation vs brute force), `canontest.c` (canonical-deletion invariance under random relabelling) |
| `split.sh`, `combine.py`, `rebuild.py`, `tail.sh`, `watch.sh` | **as-run records**, with the run directory `/tmp/claude-0/iota` hard-coded: splitting a heavy shard at depth 10 and folding its descendants back into one record, rebuilding a chunk log from a stopped worker plus separately run shards, and the parallel tail. Kept because the ledger was assembled with them, not as general tools |

Build (nauty 2.8.8 source from the pynauty 2.8.8.1 sdist, `./configure` first):

```sh
N=path/to/nauty2_8_8
gcc -O3 -march=native -I $N -o isearch tools/iota4/isearch.c \
  $N/nauty.c $N/nautil.c $N/naugraph.c $N/schreier.c $N/naurng.c
./isearch -k 3 -m 11 -I      # NONE, ACCEPTED 1 1 2 5 13 17 20 8 3 1 1 0  (iota(3) = 10)
./isearch -k 4 -m 28 -I -e 6 -o d6.txt   # EMITTED depth=6 count=11720
```

Exit code 10 means a family of `m` rows was found (printed as `SOLUTION`),
20 means none exists.
