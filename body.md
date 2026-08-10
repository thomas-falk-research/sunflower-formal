## Claim

`f(3,3)` is not an open sunflower number — Abbott and Gardner settled it in
1969, and this repository's own lower bound is the exact value — and the
`ι(4)` frontier that cost the branch-and-bound 4437 seconds now costs 866 on a
new instrument, confirmed by a second solver. What is new *about sunflowers*
is one row: **no intersecting 3-sunflower-free family of 5-sets has 43 members
on nine points or fewer.** `ι(4,11)` was not decided and the run was stopped by
hand; §33.5a records where.

## What did not move

* **No upper bound on `f(n,k)` moved and no lower bound moved.** Erdős–Rado,
  Rao 2020's shape through the axiom, and the `10^(n/2)` record are all exactly
  where session N+10 left them.
* **`Sharp.AHSOptimal` is not decided.** `ι(4)` is trapped in `[27, 59]` with
  the 1969 value carried, and the `31/32` boundary is inside that interval. The
  ladder decides `ι(4, g)` only for `g` on the ladder, and no ground-set bound
  is known that would make it finite.
* **`r*(3,3)` is unchanged at `[3, 4]`**, `Conjecture P` is untouched, and no
  row of the §28.5 conjecture ledger graduated.
* **The axiom is still an axiom.** `make coqchk`'s whole-library census is
  exactly `Sunflower.ALWZ.Rao20_lemma2`, and Stage C of the discharge was not
  begun — deliberately: §32.2 records that finishing it improves no bound.
* **§29's greedy-cover barrier is NOT upgraded.** Kostochka's survey was read
  in full and contains no such remark, but Füredi's 1978 Bolyai paper is
  located and unopened, so rule 19 forbids reporting the negative. The novelty
  status of `Profile.greedy_forces_erdos_rado` is unchanged.
* **No new axiom, no `admit`.** Every audited name reports `Closed under the
  global context`.

## Machine-readable state

```toml
[state]
modules             = 46
audited_theorems    = 683
audited_definitions = 130
mutations           = 151
mutations_killed    = 148
rust_suites         = 32
axioms              = ["Sunflower.ALWZ.Rao20_lemma2"]

[gates]
verify      = "pass"
coqchk      = "pass"
mutants     = "pass"
rust        = "pass"
statements  = "pass"
docnumbers  = "pass"
ceilings    = "pass"

[[claim]]
id        = "f-3-3-known-since-1969"
statement = "f(3,3) = 21 in this development's convention, and Intersecting.lower_bound_3_3_20 is exact rather than a lower bound with a gap above it."
kind      = "correction"
evidence  = "AbbottGardner.f_3_3_is_exactly_21"
novelty   = "not-new"
search    = "Kostochka, Extremal problems on Delta-systems, read in full (9 of 9 pages rendered); p. 4 states it verbatim and attributes it to Abbott and Gardner 1969. Corroborated by Bennett-Priestley arXiv:2509.16355 p. 7, rendered, which cites [AG69b] for the precise small values. Primary source paywalled and not read. docs/reading.md A9, A9a, A9b."

[[claim]]
id        = "gardner-value-pinned-from-below"
statement = "GAtMost 3 19 is false, so the transcription of the 1969 value cannot be too small without failing to compile."
kind      = "theorem"
evidence  = "AbbottGardner.gardner_value_is_not_vacuous"
novelty   = "new-to-this-development"
search    = "none run"

[[claim]]
id        = "iota-four-at-most-59"
statement = "With the 1969 value and the exhaustive iota(3) = 10, iota(4) is at most 59, against the 71 the repository proves from g(3) <= 26."
kind      = "theorem"
evidence  = "AbbottGardner.iota_four_at_most_59_if_iota_three_is_ten"
novelty   = "new-to-this-development"
search    = "none run"

[[claim]]
id        = "cone-route-closed"
statement = "The route roadmap section 13.4 calls the most concrete thing left on the list was already refuted by PureLink.g_three_at_most_26: no 3-uniform sunflower-free family has 32 members, on any ground set."
kind      = "correction"
evidence  = "AbbottGardner.no_three_uniform_sunflower_free_family_has_thirty_two_members"
novelty   = "new-to-this-development"
search    = "none run"

[[claim]]
id        = "iota-five-ladder"
statement = "No intersecting 3-sunflower-free family of 5-sets has 43 members on nine points or fewer; the previous state of that row was iota(5,10) >= 42 with the rung above it undecided in sixteen minutes."
kind      = "measurement"
evidence  = "rust/src/symbreak.rs"
novelty   = "new-mathematics"
search    = "iota(b) is unnamed and untabulated in the literature: not in Kupavskii's 2025 Delta-system survey (66 pages, complete rendered pass, docs/papers/kup25-rendered-pass.md), not in Kostochka's survey (9 pages, read in full this session), not in [Ra20], [ALWZ20], [Lovett], [Rao25], [BCW21]. Kostochka p. 4 records that no exact value of f(k,r) beyond f(3,3) is known for k >= 3, r >= 3, and p. 3 poses the optimality of the 1972 construction in prose. Abbott-Exoo 1992 is the closest prior computational work; its published lower bounds, quoted from two rendered secondary sources, are all for r >= 4. docs/reading.md A9, A12, A13."

[[claim]]
id        = "symbreak-cover"
statement = "The degree-sequence cube split enumerates exactly the degree vectors the encoding admits, checked against a brute-force sweep sharing no code with it."
kind      = "measurement"
evidence  = "the_degree_sequence_cubes_enumerate_every_admissible_vector"
novelty   = "new-to-this-development"
search    = "none run"

[[claim]]
id        = "counter-is-an-iff"
statement = "The degree counters encode at-least-k in both directions, so a degree comparison is a constraint rather than a no-op."
kind      = "measurement"
evidence  = "the_order_counter_is_an_iff_in_both_directions"
novelty   = "new-to-this-development"
search    = "none run"

[[claim]]
id        = "ladder-refutes-thirty-two-to-nine"
statement = "No intersecting 3-sunflower-free family of 4-sets has 32 members on nine points or fewer, re-decided by the new encoding."
kind      = "measurement"
evidence  = "no_thirty_two_member_family_of_four_sets_fits_on_nine_points"
novelty   = "new-to-this-development"
search    = "none run"

[[claim]]
id        = "contention-claim-withdrawn"
statement = "The causal claim that runner contention explained the mutation job's wall times is refuted by the next measurement and is withdrawn from both files that carried it."
kind      = "correction"
evidence  = "docs/reading.md"
novelty   = "not-new"
search    = "none run"

[[claim]]
id        = "b19c-corrected"
statement = "Register row B19c claimed the absolute spread condition was not found in the literature, contradicting row B19d and this file's own transcription check; it now claims only the extremal question."
kind      = "correction"
evidence  = "docs/reading.md"
novelty   = "not-new"
search    = "Bell-Chueluecha-Warnke's definition, already recorded in this file, is the absolute form verbatim."
```

## Results

See `docs/roadmap.md` §33 for the full account. In brief:

**1. `f(3,3)` was decided in 1969.** Kostochka's Δ-system survey, p. 4,
rendered: *"Abbott and B. Gardner [2] proved in 1969 that `f(3,3) = 20`, and
since then no other exact value of `f(k,r)` for `k ≥ 3` and `r ≥ 3` became
known."* His `f(k,r)` is the largest family, not the threshold — p. 1 defines
it that way — so it is this development's `g(3) = 20`, i.e. `f(3,3) = 21`.
`STATUS.md` called `f(3,3)` "the first unknown sunflower number" in three
places. `coq/AbbottGardner.v` carries the value as a `Prop`, not an axiom, and
proves two things about it the kernel *can* check: `~ GAtMost 3 19`, so the
twenty-member family already in the repository pins it from below, and that it
is weaker than the proved `g(3) ≤ 26`.

**2. The cone route to `ι(4) ≥ 32` was already dead.** §13.4 called it "the
most concrete thing left on the list". It needs a 3-uniform sunflower-free
family of 32 members; `PureLink.g_three_at_most_26`, proved in a later session,
says the largest has 26. The 601-second SAT run §13.4 records at `N(3,16) ≥ 30`
was asking a question the kernel in the same tree already answers.

**3. The `ι(4)` ladder.** `rust/src/symbreak.rs` implements §9's named next
step — spend the anchor's stabiliser on a sorted degree sequence — plus a
lexicographic tie-break inside equal-degree runs, an exact-size constraint that
pins the incidence count, a sharper degree floor, a ladder in the support size,
and a two-phase cube split that refines a stalled `deg(0)` cube into its exact
degree sequences.

## Negative results, with budgets

Full table in `docs/roadmap.md` §33.5. The three statements this repository
distinguishes, each used exactly once:

* **Exhausted.** `iota(4,g) >= 32` for every `g <= 10`: UNSAT, no limit hit,
  866 s at `g = 10` — and re-run end to end under `cryptominisat5`, which
  agrees. `iota(5,g) >= 43` for every `g <= 9`: UNSAT, 70.2 s for the whole ladder.
* **Undecided at the limit.** Sixteen of the twenty-one `deg(0)` cubes at
  `g = 11` were still running when the sixty-second slice expired. That is a
  measurement of the slice, not of the question.
* **Stopped by hand, budget unspent.** The `g = 11` rung and the `b = 5`
  `g = 10` rung were both killed to free the machine for the gates. Nothing is
  claimed about either. §33.5a lists what finishing `g = 11` would take, in
  order of expected value.

Two more, from earlier in the session and reported because they cost real time:
the *previous* SAT encoding was re-run as a control on `iota(4,10) >= 32` and
did not decide it — cadical, orbit split, 1800 s per orbit, orbit 1 timed out
and the run was stopped during orbit 2. And a first attempt at the adaptive
cube split refined `deg(0) = 14` at `g = 10` into 684 degree-sequence cubes for
an instance that solves whole in ten minutes; that measurement is why the
refinement is capped.

## Corrections

* **A falsified causal claim, in three places.** `b0f9d25` said runner
  contention explained why two duplicated mutation jobs were slower than a solo
  run. The next measurement refutes it: the solo run was the slowest of the
  three, and the "reference" it was compared against was itself contended. The
  saving is unaffected — one job instead of two — but the explanation is
  deleted from `verify.yml` and `docs/testing.md`, and `docs/reading.md` rule 28
  records the pattern: *a baseline must not carry the defect it is being used
  to measure.*
* **Register row B19c contradicted B19d**, and B19c was wrong: the absolute
  spread condition is published (it is Bell–Chueluecha–Warnke's own
  definition, quoted in this same file). Tightened to claim only the extremal
  question.
* **§13.4's headline target was closed by a later theorem in the same tree**,
  and nothing had gone back to update it. Rule 21, in the direction it was
  written for.
* **The session brief's own premise is corrected**: the "ground-set-10 instance
  that CaDiCaL failed on in 601 s" is `N(3,16) ≥ 30`, a *sixteen*-point
  instance on the general row, and it is refuted outright by `g(3) ≤ 26`.
* **The commissioned deep-research report was not included in the brief** — the
  prompt ends with the literal placeholder. Every register row added here is
  evidenced by this session's own reading; the rows the brief asked for that
  could not be independently evidenced are recorded as not done.

## Reproduction

```
make -j4 verify
make coqchk
python3 tools/mutate.py
cd rust && cargo test --release
make statements && make docnumbers && make ceilings
```

The ladder, which is not part of the test suite because of its runtime:

```
cd rust && cargo run --release --example iota_sym -- 4 12 32 --threads 4 --ladder --slice 90
```

Needs `cadical` on `PATH` (`apt-get install -y cadical cryptominisat`).

## What a reviewer should attack

**The UNSAT verdicts.** They are cadical's word. This repository's standing
rule for UNSAT — `sat::solve_agreed`, two independent solvers required to agree
— was applied to the frontier rung and not to every cube of every rung, and
`docs/roadmap.md` §33.5 says exactly which. An UNSAT nobody can produce a
witness against is the verdict most worth doubting.

**The `all_points_used` restriction.** It is the one option in
`rust/src/symbreak.rs` that is not sound on its own: it asks a strictly smaller
question and is legitimate only because the ladder has already refuted the same
target at every smaller ground set. If the ladder's rungs were run out of order
or one were skipped, every rung above it would be wrong and would look right.

**`AbbottGardner1969` is a citation.** The kernel checks that it is not too
small and not stronger than what is proved. It cannot check that Kostochka's
sentence is true, and the primary source was not read.

## Handover

`docs/roadmap.md` §33.7. The short version: the ladder is the instrument and it
has no stopping rule — deciding `ι(4)` outright needs a ground-set bound for
*intersecting* families, which is `IotaGround.IotaGroundBounded` and is open.
Do not restart Stage C without reading §32.2 first.
