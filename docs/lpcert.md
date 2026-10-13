# LPCert: kernel-checked bounds for integer linear programs

`coq/LPCert.v` is a small checker, independent of the rest of this
repository, that turns a certificate into a Coq theorem of the form

> every integer point satisfying these rows, and nonnegative on the
> variables declared nonnegative, has `c·x < T`

or, with `c = []` and `T = 0`, that the rows have no integer solution.
The arithmetic is exact (`Z`), the check is decided by `vm_compute`, and
the soundness theorem is closed under the global context.

## What is proved

```coq
Theorem tree_sound :
  forall (tag : Type) (rowf : tag -> row) (nonneg : nat -> bool) (n : nat) (c : svec) (T : Z) (tr : tree tag),
    check tag rowf nonneg n c T [] tr = true ->
    forall x : nat -> Z, (forall t, sat (rowf t) x) -> (forall j, nonneg j = true -> 0 <= x j) ->
    dot c x < T.

Corollary infeasible_of_tree : ... check tag rowf nonneg n [] 0 [] tr = true ->
    forall x, (forall j, nonneg j = true -> 0 <= x j) -> ~ (forall t, sat (rowf t) x).

Corollary tree_sound_list    : (rows given as an explicit list)
Corollary tree_sound_list_nn : (and the nonnegative variables as a list, nonneg_of l)
```

* Variables are integers, `x : nat -> Z`. Continuous variables are not
  supported: branching needs `a·x` to be an integer.
* A row `(a, b)` means `a·x ≤ b`, with `a` a sparse list of
  `(index, coefficient)`; repeated indices add up. Bounds, equalities
  (two rows) and `≥` rows (negate) are all rows.
* Rows come from any function `rowf : tag -> row`, so a problem with
  millions of implicit rows needs no list; an explicit list is
  `list_rows rows` (out-of-range tags read as the trivial row `0 ≤ 0`).
* `nonneg : nat -> bool` declares variables nonnegative (`free`: none;
  `nonneg_of l`: those listed). A declaration is a hypothesis of the
  theorem, so it must be discharged for the `x` at hand. It lets a leaf
  leave slack on those variables (condition 3 below) instead of spending
  one explicit row `-x_j ≤ 0` per variable, which for the sunflower
  certificates would multiply their size.

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
  3. for every `j < n`: `K·c_j = (Σ y·a)_j` exactly, or `K·c_j ≤ (Σ y·a)_j`
     when `x_j` is declared nonnegative;
  4. `Σ y·b < K·T`.

Then `K·(c·x) ≤ Σ y·(a·x) ≤ Σ y·b < K·T` (termwise, the slack in 3 is
multiplied by `x_j ≥ 0`), so `c·x < T` when `K > 0`, and there is no
point when `K = 0`. Each condition is shown load-bearing by
`tools/mutations.toml` (`lpcert-*`, including `lpcert-slack-everywhere`,
`lpcert-slack-reversed` and `lpcert-declare-all` for the declaration)
and by a rejected example in `coq/LPCertExamples.v` (section 3 shows a
certificate accepted only with the declaration, rejected without it or
with it on the wrong variable, and a point showing the claim needs it).

The check adds the multiplied rows up in a `PositiveMap` (`zcomb`) and
reads one coefficient per variable, so a leaf costs
`O((nnz + n) log n)`; `zget_zcomb` proves the map holds the
coefficient-wise sum used in the proof.

## JSON form and tools

`tools/lpcert/lpcert.py`:

```
problem = {"n": int, "rows": [[[[j, a], ...], b], ...], "c": [[j, c], ...], "T": int,
           "nonneg": [j, ...]}                                   (optional; default [])
tree    = {"leaf": {"K": int, "y": [[["base", r] | ["br", k], y], ...]}}
        | {"branch": [[j, a], ...], "f": int, "le": tree, "ge": tree}

lpcert.py solve PROBLEM.json TREE.json      branch-and-bound (scipy/HiGHS), exact duals
lpcert.py check PROBLEM.json TREE.json      exact checker, the Coq semantics line by line
lpcert.py coq   PROBLEM.json TREE.json OUT.v NAME   a module proving the bound
```

The solver takes the dual LP's support from HiGHS and re-solves the
equations of condition 3 (for the declared variables, those the LP left
tight) exactly over the rationals before scaling to integers, so
floating point never reaches a certificate; the result is re-checked by
the exact checker before it is returned. The Python
checker is a second implementation for convenience; the trusted check
is Coq's.

`python3 tools/lpcert/test_lpcert.py --coq` (also run by `make verify`):
the examples of `coq/LPCertExamples.v` with the same verdicts; 300
random small programs against brute force (bounds proved at the
optimum, false claims refused, infeasible ones refuted), the lower
faces of the box given as rows in half of them and as declarations in
the other half; every certificate with one multiplier increased judged
by an independent dense reference checker, with which the checker agrees
on every one (without declarations every one is rejected; with them the
extra slack can leave a valid proof of the same true claim);
certificates that use a declaration rejected without it; and
certificates exported to Coq (with and without declarations) compile
while the same with one multiplier changed, or with the declaration
withheld, do not.

## Scaling

For hundreds of thousands of certificates, `docs/roadmap.md` §71
records what keeps a kernel check within memory: certificates inside
opaque proofs (a module exports only what it certifies), modules cut by
certificate size, and `coqchk -norec` per module.

## Relation to the sunflower development

Every certificate of the link descent is checked by `LPCert.check`.
`coq/Link23.v` states the integer program of a link class as LPCert
rows (`zrowf`: the tagged rows proved valid by `rows_valid`, and the
upper bounds `x_j ≤ ub_of`), declares every type count nonnegative, and
proves `bound_of_lpcheck` from `LPCert.tree_sound`. The earlier
special-purpose checkers of `Link23.v` were removed in the port
(`docs/roadmap.md` §73). The §64 LP certificates (`coq/LinkLP.v`,
`LinkCerts*`) remain in the repository as an independent cross-check
by a different model and checker; no census theorem depends on them.
