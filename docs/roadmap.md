# Roadmap

What is worth doing next, why, and what to avoid. Written to be picked
up cold: each item states the target, the technical choice that decides
whether it is feasible, and the failure mode that would sink it.

The repository's state is in [`STATUS.md`](../STATUS.md); the testing
layer and its limits are in [`testing.md`](testing.md).

---

## Done: the testing layer

Both errors this development has produced were errors of *statement*,
invisible to the kernel. Four mechanisms now target that class — see
[`testing.md`](testing.md). Everything below is safer for having them,
and new definitions should arrive with the corresponding checks rather
than acquire them later:

* a new definition gets a coherence theorem in `coq/Audit.v` if there
  is any question it should obviously answer;
* a new decision procedure gets a second, independently implemented
  opinion and a proof they agree, as `Reflect.rao_witness_agrees` does
  for `Spread.rao_witness`;
* a new hypothesis gets a mutation in `tools/mutations.toml`. If the
  mutation survives, the hypothesis is doing no work — find out why
  before writing anything on top of it.

---

## 1. Discharging the axiom: Rao's Lemma 2

The one axiom is `ALWZ.Rao20_lemma2`. Everything downstream of it is
already proved, so discharging it is the single highest-value target,
and the interface is fixed: prove `SpreadYieldsDisjoint n k r` for
`r ≳ k log(nk)` and the file closes with no other changes.

Rao's proof is elementary — injections between finite sets and
binomial estimates, no measure theory — which is what makes it a
realistic target at all. Re-read the paper before writing a line. That
discipline is what caught the fractional-vs-absolute error.

### Stage A — the counting layer

**The technical choice that decides feasibility.** The covering step
is usually stated for a uniformly random subset of *fixed size*, which
drags in binomial coefficients and their estimates. Stated instead for
the **product measure** — each element included independently with
probability 1/2 — "probability" becomes plain cardinality over the
powerset, and `Spread.subsets` is already exactly that enumeration.

Build:

* `count : (list nat -> bool) -> list (list nat) -> nat`;
* injection-implies-`≤`;
* additivity over disjoint predicates;
* `length (subsets U) = 2 ^ length U`.

Self-contained, independently testable, reusable. Likely one session.

### Stage B — the encoding

The mathematical core: the map from "sets `W` containing no member of
`F`" to compressed encodings, and its injectivity. This is where a
session's budget should go, and where the stall risk is.

### Stage C — the arithmetic

Where the explicit constant lives.

**Scoping decision — do not chase the constant.** The axiom is
existentially quantified over `α`, so *any* explicit constant
discharges it: `α = 2²⁰` closes the file exactly as well as `α = 64`.
Chasing sharpness is where this campaign dies.

### What the testbed now buys here

Each stage's statements can be checked before they are proved. A
counting lemma is a Rust one-liner to falsify; an encoding is a map to
run over the exhaustive enumeration in `rust/src/testbed.rs` and check
injective. Use it — the cost of finding out a lemma is false after
half a session of proof is the main way this campaign goes wrong.

---

## 2. Bounded investigation: is the spread restatement an *equivalence*?

`Conjecture.spread_conjecture_suffices` proves one direction: a
constant-threshold spread lemma implies the Erdős–Rado conjecture. The
converse was looked for and not found; the obvious route — feed a
spread family to the sunflower bound — yields a sunflower, not disjoint
sets, and the core gets in the way.

If the converse holds, the repository contains a formal *equivalence*:
the Erdős–Rado conjecture is equivalent to a statement in which no
sunflower appears. That is a materially stronger claim than anything
else on this list.

Timeboxed. First a literature check — this is likely known or folklore.
Then an attempt via the link structure. Drop it on schedule if it does
not yield.

---

## 3. If Rao stalls: the `f(2,k)` program

`f(2,k)` is the Chvátal–Hanson extremal problem at `D = ν = k-1`.
Working from that formula (**verify against the source** — this is
recalled, not checked):

* `f(2,k) = k(k-1) + 1` for odd `k`;
* `f(2,k) = (k-1)² + (k-2)/2 + 1` for even `k`.

At `k = 3` this gives 7, matching `F23.f_2_3_eq_7` — a good sign the
recollection is right, and the first thing to confirm.

**The lower bound is the completable half.** For odd `k` it is two
disjoint copies of `K_k`: max degree `k-1`, matching number `k-1`,
`k(k-1)` edges — literally `F23.two_triangles` generalised. That gives
an infinite family of exact sunflower lower bounds, still (as far as
was found) unformalised anywhere.

**The upper bound is the hard half** and needs its own campaign. The
naive counts (`2νD`, `ν(2D-1)`) are tight only at `k = 3`, which is
why `F23.v` works and will not generalise.

Wanted underneath it: the structural lemma that for 2-uniform families
a `k`-sunflower is either `k` disjoint edges or `k` edges through a
point. That would let `F23.v` be re-derived more cleanly.

---

## 4. Smaller targets opened up by this session

Concrete, bounded, and each motivated by something the testbed
measured rather than by taste.

* **The threshold at uniformity 2.** `make testbed` reports `r* = 3`
  for `(m,k) = (2,3)` over every ground set up to 9. Coq proves
  `r ≥ 3` is necessary (`Audit.no_spread_yields_disjoint_2_3_2`) but
  nothing proves `r = 3` suffices — the elementary lemma only gives
  `r = 5`. Proving `SpreadYieldsDisjoint 2 3 3` would be the first
  sharp spread threshold in the development.

* **Generalise the five-cycle refutation.** `C₅` refutes `r = 2` at
  `(m,k) = (2,3)`. The odd cycle `C_{2k-1}` should refute any `r` with
  `r² < 2k-1` at `(m, k)`: it is 2-regular, hence `r`-spread for
  `r ≥ 2`, has `2k-1` edges, and `k` disjoint edges would need `2k`
  vertices. That would show the threshold grows with `k` at fixed
  uniformity, generalising a concrete `vm_compute` witness into a
  theorem. Estimated 150–250 lines: the work is proving `Distinct` and
  the degree bounds for a symbolic cycle.

* **Sharpen the sandwich.** `Audit.spread_yields_disjoint_sandwich`
  brackets the axiom's shape between `k-1` and `n(k-1)`. Both ends are
  loose. Narrowing either narrows what the axiom is actually assuming.

* **Fewer script-level kills.** `lowerbound-at-least` is killed only
  because four `apply H` steps break when a goal changes from `=` to
  `≥`. Writing those as `rewrite H; lia` would make the mutation
  survive outright, which is the honest outcome. Low value on its own,
  but the same brittleness will distort future mutation results.

* **Widen the mutation manifest.** It currently covers the definitions
  the two historical errors touched, plus the reduction's arithmetic.
  `Sets.v`, `Graph.v`, `Matching.v` and the Hall/Kőnig layer are
  untouched.

---

## What not to do

* **Do not run the Rao campaign and the `f(2,k)` campaign in the same
  session.** Both are grinds; interleaving them is how both stall.

* **Do not expect progress on the conjecture itself.** The `log n` is
  a conceptual barrier, not bookkeeping.

* **Do not chase sharp constants** anywhere. See Stage C.

* **Do not add a definition without adding its checks.** The two
  errors this corpus has produced were both invisible to the kernel,
  and the machinery in [`testing.md`](testing.md) only helps for
  definitions it has been pointed at.
