## Claim

The size threshold in `SpreadYieldsDisjoint 3 3 3` is exactly tight: a
3-uniform family of exactly `27 = 3^3` members, 9-regular on nine points,
satisfies Rao's spread condition at `r = 3` and has no three pairwise
disjoint members (`coq/TightThreshold.v`). Separately, an intersecting
3-uniform family under Rao's caps at `r >= 3` with covering number
exactly two has at most `3r + 1` members, attained
(`coq/TwoCoverSharp.v`), sharpening the proved `max(4r, 3r+4)`. About
sunflowers themselves: nothing — `r*(3,3)` is still `{3, 4}`.

## What did not move

`r*(3,3) ∈ {3, 4}` is unchanged at both ends (ten and eleven points are
excluded as a home for a refutation, which narrows where, not whether). No bound on `f(n,k)`, no
exact value, no row of the `r*(m,3)` table, no entry of the conjecture
ledger, and no constant in `[65, 125]` moved. `ι(4)` is still bracketed
`27 ≤ ι(4) ≤ 71`, `ι(4,11) ≤ 31` still rests on cadical with the cube-13
second opinion where §54 left it. The axiom count is unchanged: exactly
`Sunflower.ALWZ.Rao20_lemma2`. What *is* withdrawn is evidence, not a
bound: STATUS.md's 23-member object and §22.5's "weak evidence that the
term really is 3" — the exact maximum on nine points is 27.

## Machine-readable state

```toml
[state]
modules             = 51
audited_theorems    = 771
audited_definitions = 148
mutations           = 171
mutations_killed    = 168
rust_suites         = 43
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
id       = "threshold-27-attained"
statement = "There is a 3-uniform family of exactly 27 members satisfying RaoSpread 3 F 3 with no three pairwise disjoint members, so the non-strict form of SpreadYieldsDisjoint 3 3 3 is false."
kind     = "theorem"
evidence = "TightThreshold.threshold_27_is_attained"
novelty  = "new-to-this-development"
search   = "docs/reading.md, Session N+16: 17 arXiv API, 4 zbMATH, 23 web queries; Khare 2014 and Hou-Yu-Gao-Liu 2017 read from rendered pages; nothing on bounded-degree bounded-matching non-linear 3-graphs found"

[[claim]]
id       = "non-strict-threshold-fails"
statement = "SpreadYieldsDisjointNonStrict 3 3 3 is false."
kind     = "refutation"
evidence = "TightThreshold.non_strict_threshold_fails_at_3_3_3"
novelty  = "new-to-this-development"
search   = "as above"

[[claim]]
id       = "two-cover-3r-plus-1"
statement = "An intersecting 3-uniform family satisfying RaoSpread 3 G r with r >= 3, covered by two points and by neither alone, has at most 3r + 1 members."
kind     = "theorem"
evidence = "TwoCoverSharp.two_cover_at_most_3r_plus_1"
novelty  = "new-to-this-development"
search   = "as above; nearest neighbour FHHZ17 (degree version of Hilton-Milner), which conditions on minimum degree rather than capping maximum degree"

[[claim]]
id       = "two-cover-3r-plus-1-tight"
statement = "The bound 3r + 1 is attained at r = 3 by hm_family, a two-covered intersecting family of 10 members under the caps."
kind     = "theorem"
evidence = "TwoCoverSharp.two_cover_sharp_at_three_is_tight"
novelty  = "new-to-this-development"
search   = "as above"

[[claim]]
id       = "nine-point-maximum-is-27"
statement = "The largest 3-uniform family on nine points with no three pairwise disjoint members, point degree <= 9 and pair degree <= 3 has 27 members."
kind     = "measurement"
evidence = "rust/tests/tight_threshold.rs"
novelty  = "new-to-this-development"
search   = "as above"

[[claim]]
id       = "two-cover-measured"
statement = "On six to nine points the two-covered maximum under the caps is 9, 10, 10, 10 at r = 3 and 10, 12, 13, 13 at r = 4, by an exhaustive depth-first search independent of the Coq."
kind     = "measurement"
evidence = "rust/tests/tight_threshold.rs"
novelty  = "new-to-this-development"
search   = "as above"

[[claim]]
id       = "no-28-on-ten-points"
statement = "No 3-uniform family on ten points with 28 members, no three pairwise disjoint members, point degree <= 9 and pair degree <= 3 exists: all eleven degree-sequence cubes are infeasible under CP-SAT."
kind     = "measurement"
evidence = "docs/ladder/rstar_3_3_10.tsv"
novelty  = "new-to-this-development"
search   = "as above"

[[claim]]
id       = "no-28-on-eleven-points"
statement = "No 3-uniform family on eleven points with 28 members, no three pairwise disjoint members, point degree <= 9 and pair degree <= 3 exists: all 139 degree-sequence cubes are infeasible under CP-SAT, 118 flat and 21 via every pair-degree-profile sub-cube; tools/audit11.py checks the ladders and exits 0."
kind     = "measurement"
evidence = "docs/ladder/rstar_3_3_11.sub.tsv"
novelty  = "new-to-this-development"
search   = "as above"

[[claim]]
id       = "weak-evidence-withdrawn"
statement = "The 23-member object pinned in rust/tests/spread_threshold.rs and offered in docs/roadmap.md section 22.5 as weak evidence for r*(3,3) = 3 is no evidence: the exact maximum on a smaller ground is 27."
kind     = "correction"
evidence = "docs/roadmap.md"
novelty  = "not-new"
search   = "none run"

[[claim]]
id       = "prior-art-pass"
statement = "Two papers (Khare 2014, Hou-Yu-Gao-Liu 2017) were added to the corpus with rendered-page readings; neither bounds the problem at codegree 3."
kind     = "tooling"
evidence = "docs/papers/manifest.json"
novelty  = "not-new"
search   = "none run"
```

## Results

**`TightThreshold.threshold_27_is_attained`.** `nine27` is 27 triples on
`{0..8}`; `nine27_uniform`, `nine27_distinct` and both spread checkers
(`rao_witness_none` and `rao_spreadb`) decide by `vm_compute`, and
`nine27_no_three_disjoint` is the `false` branch of
`SpreadThreshold.decide_three_disjoint`'s boolean, so the family meets
every hypothesis of `SpreadYieldsDisjoint 3 3 3` except `27 < |F|`. The
family is 9-regular (`nine27_regular`), which is the counting ceiling
`9·9/3` on nine points met exactly. Found by exact optimisation in
0.0 s; independently re-checked in `rust/tests/tight_threshold.rs`.

**`TwoCoverSharp.two_cover_at_most_3r_plus_1`.** Cases on whether a
piece has a common point. A common point on one side caps that side at
`r` by a pair, and either the other side shares the point (`r`) or some
member misses it, which pins the first side to two triples and the
second to one pair plus one triple (`r + 1`). No common point on either
side: each side is pinned to four triples by the other, and a side with
four members has two members with disjoint tails (a family of
pairwise-meeting tails with no common point has at most three), whose
four cross triples cannot all occur without forcing the first side to
two — so the two sides total at most seven, which is `2r + 1` at `r = 3`.
Plus `r` for the members through both cover points. The mutations
`twocoversharp-three-r` and `twocoversharp-r-at-least-two` show the `+1`
and the `3 <= r` are load-bearing.

**Gates.** `verify`, `coqchk` (census exactly `Sunflower.ALWZ.Rao20_lemma2`),
`statements` (919 entries, no existing hash moved), `docnumbers` (17),
`ceilings` (9 routes) all pass on the final tree; the four new mutations
are all killed (`tools/mutate.py --only ...`, 365 s each); the new suite
`rust/tests/tight_threshold.rs` passes. The full Rust suite passes, 43 of 43: on the first run two tests in
`spread_threshold.rs` (a file this branch does not touch) panicked with
`NotFound` because `cryptominisat5` was not installed in the container;
after installing it, that suite passes 20 of 20, and the eleven suites
cargo had skipped after the failure were run separately and pass.

**Costs and what remains.** `docs/roadmap.md` §56.7 and §56.5. The
28-member question — `r*(3,3) = 3` or `4` — is open; ten points (§56.9,
eleven cubes) and eleven points (§56.10, 139 cubes, the stalls closed by
pair-degree-profile sub-cubes, about 110 core-hours in all) are now
excluded under CP-SAT, so twelve points is the next thing to cube, with
the sub-cube first and a proof-logging PB solver as the second opinion.

🤖 Generated with [Claude Code](https://claude.com/claude-code)

https://claude.ai/code/session_01SqzBAiCLvej7Q2KfCN32Yj
