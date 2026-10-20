# LRAT: kernel-checked unsatisfiability proofs

`coq/LRAT.v` is a small checker, independent of the rest of this
repository, for LRAT proofs of propositional unsatisfiability. An
accepted proof gives the Coq theorem

> no valuation satisfies this CNF

(`lrat_sound : lrat_check F ps = true -> forall v, cnf_sat v F = false`),
closed under the global context.

## What is checked

A literal is a nonzero integer, a clause a list of literals, the CNF's
clauses are numbered `1, 2, …`. A proof is a list of steps:

* `Add i C hs` — the clause `C`, numbered `i`, by reverse unit
  propagation along the hints `hs`: assume every literal of `C` false;
  each hinted clause in turn must have all its literals false but one,
  which becomes true, until a hinted clause has all its literals false.
  A hinted clause that names nothing, has a true literal, or has two
  literals not yet false makes the step fail. A clause to add may not
  contain `0`.
* `Del is` — forget the clauses numbered `is`.

The proof succeeds when it adds the empty clause. The clause database is
a `PositiveMap`, and a step costs about the total length of its hinted
clauses. Only reverse-unit-propagation steps are supported; RAT steps
(negative hints, needed after extended resolution) are refused by the
parser and would fail in the checker.

The proof of soundness keeps a partial assignment that agrees with any
valuation satisfying the database and falsifying the new clause, and
derives a contradiction from the conflict (`rup_sound`); every step keeps
the database satisfied, so the empty clause can never be added under a
satisfying valuation.

## Tools and tests

`tools/lrat/lrat.py` parses DIMACS and textual LRAT (CaDiCaL:
`cadical --lrat=true --binary=false F.cnf F.lrat`), checks with the same
semantics in Python, and emits a Coq module whose theorem is the
refutation. `make lrat-test` (`tools/lrat/test_lrat.py --coq`, needs
`cadical`):

* pigeonhole PHP(n+1, n), n = 2..6, and 80 random 3-CNF on 12 variables:
  every CaDiCaL proof accepted, every model of a satisfiable formula
  checked;
* a semantic oracle on the formulas with at most 14 variables: every
  clause a proof adds is checked by brute force to follow from the
  clauses present at that step, for every proof the checker accepts,
  tampered ones included;
* rejection of the proof cut before the empty clause, of hints naming
  no clause, of a bogus refutation of a satisfiable formula, and of RAT
  hints;
* a proof exported to Coq compiles, and the same with a missing hint
  does not.

`coq/LRATExamples.v` refutes PHP(4,3) in the kernel and shows four
rejected proofs. Mutations `lrat-*` in `tools/mutations.toml` remove one
condition of the check each.

## What it does not do yet

It turns a SAT solver's UNSAT answer into a theorem *about the CNF*. A
theorem about sunflowers — for the `ι(4, 11)` ladder of
`docs/roadmap.md`, that no family of the given size exists in the cube —
needs a further Coq proof that the CNF encodes the question (the
encoding of `rust/src/sat.rs` and the cube constraints), and proofs of
the size CaDiCaL writes for those cubes may be too large for the kernel;
both are open.
