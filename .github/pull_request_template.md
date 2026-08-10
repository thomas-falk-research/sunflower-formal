<!--
  This template is gated. `tools/prcheck.py` parses the ```toml block
  under "Machine-readable state" below, resolves every claim's evidence
  against the repository, and fails CI if a count is wrong, a name does
  not exist, or a claim of new mathematics carries no literature
  search. Run it before submitting, from the repository root:

      make prcheck PR_BODY=path/to/body.md

  What it cannot check is whether the prose is honest. That part is on
  the author, and the sections are ordered to make dishonesty awkward
  rather than to make it impossible.

  Delete any section that genuinely does not apply, except "What did not
  move", which is mandatory and is checked. The ```toml block is
  required on every pull request, including a one-line one; if that is
  disproportionate for a change, say so in Claim and fill it in anyway,
  because a template with an exemption clause is a template nobody
  fills in.
-->

## Claim

<!-- One sentence. What is now known that was not known before this
     branch? If the answer is "nothing about sunflowers, only about this
     repository", write that. -->

## What did not move

<!-- MANDATORY, and checked for presence. State plainly which bounds,
     exact values, conjecture-ledger rows and open constants are
     unchanged, and whether the axiom count changed. A pull request that
     cannot name what it failed to move has not been read carefully
     enough by its author. -->

## Machine-readable state

```toml
[state]
# Counts, checked against the lists they count. Same discipline as
# tools/docnumbers.py, one level up.
modules             = 0
audited_theorems    = 0
audited_definitions = 0
mutations           = 0
mutations_killed    = 0
rust_suites         = 0
# Every `Axiom` declared anywhere in coq/. Checked against the sources.
axioms              = []

[gates]
# Record the result of each gate as run on the final tree, not as hoped.
# "pass", "fail", or "not-run" with a reason in the prose.
verify      = "not-run"
coqchk      = "not-run"
mutants     = "not-run"
rust        = "not-run"
statements  = "not-run"
docnumbers  = "not-run"
ceilings    = "not-run"

# One [[claim]] per thing this branch asserts. `evidence` must resolve to
# something that exists: an audited Coq name, a Rust `#[test]` function,
# a mutation id, or a repository path. `novelty = "new-mathematics"`
# requires a non-empty `search` that is not "none run" -- that is rule 17
# of docs/reading.md, enforced.
#
# [[claim]]
# id       = "short-slug"
# statement = "One sentence, in the indicative."
# kind     = "theorem"        # theorem | measurement | refutation | correction | tooling
# evidence = "Module.theorem_name"
# novelty  = "new-to-this-development"   # new-mathematics | new-to-this-development | not-new
# search   = "none run"       # required to be a real search if novelty = new-mathematics
```

## Results

<!-- Prose for each claim above: what it says, why it is true, and what
     it costs. Name the theorem or the test, not the intention. -->

## Negative results, with budgets

<!-- Every negative is reported with its budget. "Exhausted",
     "undecided at N nodes" and "stopped by hand with budget unspent"
     are three different statements; say which. Omit the section only if
     the branch produced no negatives. -->

## Corrections

<!-- Anything this branch found to be wrong in the repository's own
     documents, plans or prior claims -- including its own session brief.
     This repository has a consistent record of the plan being one
     hypothesis away from the proof; that is worth recording where the
     next session will look. -->

## Reproduction

```
make -j4 verify
make coqchk
python3 tools/mutate.py
cd rust && cargo test --release
```

<!-- Add any environment step a fresh container needs, and any search
     command with its exact arguments and observed runtime. -->

## What a reviewer should attack

<!-- Name the weakest link, not the strongest. Which mutations probe the
     load-bearing hypotheses? Which statement would you least like to be
     wrong? Which measurement rests on the smallest search? -->

## Handover

<!-- Where the next session should start, and what it should not
     re-run. Link the roadmap section that carries the full handover. -->
