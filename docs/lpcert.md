# LPCert: kernel-checked bounds for integer linear programs

`coq/LPCert.v` is a small checker, independent of the rest of this
repository, that turns a certificate into a Coq theorem of the form

> every integer point satisfying these rows has `c·x < T`

or, with `c = []` and `T = 0`, that the rows have no integer solution.
The arithmetic is exact (`Z`), the check is decided by `vm_compute`, and
the soundness theorem is closed under the global context.

## What is proved

```coq
Theorem tree_sound :
  forall (tag : Type) (rowf : tag -> row) (n : nat) (c : svec) (T : Z) (tr : tree tag),
    check tag rowf n c T [] tr = true ->
    forall x : nat -> Z, (forall t, sat (rowf t) x) -> dot c x < T.

Corollary infeasible_of_tree : ... check tag rowf n [] 0 [] tr = true ->
    forall x, ~ (forall t, sat (rowf t) x).

Corollary tree_sound_list : (rows given as an explicit list)
```

* Variables are integers, `x : nat -> Z`. Continuous variables are not
  supported: branching needs `a·x` to be an integer.
* A row `(a, b)` means `a·x ≤ b`, with `a` a sparse list of
  `(index, coefficient)`; repeated indices add up. Bounds, equalities
  (two rows) and `≥` rows (negate) are all rows.
* Rows come from any function `rowf : tag -> row`, so a problem with
  millions of implicit rows needs no list; an explicit list is
  `list_rows rows` (out-of-range tags read as the trivial row `0 ≤ 0`).

## The certificate

A tree.

* `Node a f l r` branches on the integer linear form `a·x`: the left
  child adds the row `a·x ≤ f`, the right child `-a·x ≤ -f-1`
  (`a·x ≥ f + 1`). Every integer point lies in one of them.
* `Leaf K ys` with `K ≥ 0` and multipliers `ys`, each on a problem row
  (`Base t`) or on the `k`-th branching row of the path (`Br k`; out of
  range reads as `0 ≤ 0`). It is accepted when, for `rs` the named rows:
  1. `K ≥ 0` and every multiplier is `≥ 0`;
  2. every index of `c` and of every named row is below `n`;
  3. for every `j < n`: `K·c_j = Σ y·a_j` exactly;
  4. `Σ y·b < K·T`.

Then `K·(c·x) = Σ y·(a·x) ≤ Σ y·b < K·T`, so `c·x < T` when `K > 0`, and
there is no point when `K = 0`. Each condition is shown load-bearing by
`tools/mutations.toml` (`lpcert-*`) and by a rejected example in
`coq/LPCertExamples.v`.

## JSON form and tools

`tools/lpcert/lpcert.py`:

```
problem = {"n": int, "rows": [[[[j, a], ...], b], ...], "c": [[j, c], ...], "T": int}
tree    = {"leaf": {"K": int, "y": [[["base", r] | ["br", k], y], ...]}}
        | {"branch": [[j, a], ...], "f": int, "le": tree, "ge": tree}

lpcert.py solve PROBLEM.json TREE.json      branch-and-bound (scipy/HiGHS), exact duals
lpcert.py check PROBLEM.json TREE.json      exact checker, the Coq semantics line by line
lpcert.py coq   PROBLEM.json TREE.json OUT.v NAME   a module proving the bound
```

The solver takes the dual LP's support from HiGHS and re-solves the
equations of condition 3 exactly over the rationals before scaling to
integers, so floating point never reaches a certificate. The Python
checker is a second implementation for convenience; the trusted check
is Coq's.

`python3 tools/lpcert/test_lpcert.py --coq` (also run by `make verify`):
the examples of `coq/LPCertExamples.v` with the same verdicts; 300
random small programs against brute force (bounds proved at the
optimum, false claims refused, infeasible ones refuted); every
certificate with one multiplier changed rejected; and a certificate
exported to Coq compiles while the same with one multiplier changed
does not.

## Scaling

For hundreds of thousands of certificates, `docs/roadmap.md` §71
records what keeps a kernel check within memory: certificates inside
opaque proofs (a module exports only what it certifies), modules cut by
certificate size, and `coqchk -norec` per module.

## Relation to the sunflower development

`coq/Link23.v` contains an earlier, special-purpose checker of the same
shape (nonnegative variables, `≤` rows built from tags, an all-ones
objective). LPCert is its generalisation; the two are separate proofs,
both closed under the global context.
