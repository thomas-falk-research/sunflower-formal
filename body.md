## Claim

**The prior art existed, it was on a blog, and four sessions failed to
reach it because they had the wrong URL.** All 434 comments across the
seven Polymath10 threads were read this session, through the
WordPress.com JSON API — a different host, which answers this container
without complaint. Three findings, and the first costs something:
`Intersecting.doubling_lower_bound` was stated by Dömötör Pálvölgyi on
23 December 2015 and re-derived here; the `ι(4)` orbit search was
proposed on 14 December 2015 and never run; and **an intersecting
computation *was* run, on 25 November 2015**, which refutes a negative
this repository has repeated since N+9. `coq/Palvolgyi.v` carries the
conjecture that came with the inequality, and `rust/tests/palvolgyi.rs`
re-runs the 2015 experiment and measures why it stopped where it did.


The ground set of a hypothetical 32-member counterexample to
`Sharp.AHSOptimal` at `b = 4` is now pinned from both sides in Coq — **at
least nine points, at most 77** — where before it had one side and that
side was 97. Neither end brings the `ι(4)` ladder within reach, and this
branch says so where the bounds are stated. Separately: the one paper
session N+11 recorded as having no digitisation was on the author's own
website, took one request, and contains no Δ-system material at all.

And one queued item closed: `docs/roadmap.md` §13.1 measured that the
Abbott–Hanson–Sauer substitution families admit no extension, gave the
mechanism, and named the missing piece — *"the general statement needs
`substitute` in Coq"*. `coq/Substitution.v` is that statement. It is a
formalisation of something the repository already knew, and §35.1
records that this session proposed it as a discovery before checking.

## What did not move

* **No upper bound on `f(n,k)` moved and no lower bound moved.** Erdős–Rado,
  Rao 2020's shape through the axiom, and the `10^(n/2)` record are exactly
  where session N+11 left them.
* **`Sharp.AHSOptimal` is not decided,** and §34.5 argues it will not be
  decided by a support bound: the ladder's reachable ceiling is about
  twelve ground points, the proved floor is nine, the ladder's own floor
  is eleven, and the method here tops out at `2n + O(1)`. The right next
  target is an upper-bound argument on `ι(4)` itself, where the gap is
  `[27, 59]` against the needed 31.
* **The nine-point floor is weaker than what the ladder already knows.**
  §33.5 records `ι(4,10) ≥ 32` refuted, so the true floor is at least
  eleven. What is new is that nine is a *proof* and is quantified over
  every `b` and every family size. `the_proof_is_two_rungs_behind_the_search`
  says so in the file.
* **The new support bound is not uniformly better.** Below `n = 4b − 4`
  the single-anchor bound wins;
  `below_the_crossover_the_single_anchor_is_better` records a case where
  quoting the new number would be quoting the worse one.
* **§29's greedy-cover barrier is still NOT upgraded.** Both papers the
  brief named are now read and neither carries the remark — but two
  papers is not a literature search and rule 17 is not satisfied by
  clearing a two-item list. The novelty status of
  `Profile.greedy_forces_erdos_rado` is unchanged.
* **The `ι(4,11)` rung was not attempted** this session, and no ladder
  was run at all.
* **The axiom is still an axiom.** `make coqchk`'s whole-library census is
  exactly `Sunflower.ALWZ.Rao20_lemma2`; Stage C was not begun.
* **The substitution result is NOT new to this repository.** `docs/roadmap.md`
  §13.1 already had the table, the mechanism and three independent
  measurements; `rust/tests/extension.rs` already had the `b = 9` test.
  What was missing is what §13.1 says was missing — the general statement
  in Coq — and that is all this branch adds. A Rust file written before
  that was noticed reimplemented existing code and was deleted rather
  than committed. `docs/reading.md` rule 30.
* **`Sharp.AHSOptimal` is not decided by the maximality result either.**
  Maximal is not maximum; the Fano plane is maximal with seven members.
  `iota(9) <= 10000` is exactly as open as it was.
* **No new axiom, no `admit`.** Every audited name reports `Closed under
  the global context`.

## Machine-readable state

```toml
[state]
modules             = 49
audited_theorems    = 731
audited_definitions = 142
mutations           = 160
mutations_killed    = 157
rust_suites         = 34
axioms              = ["Sunflower.ALWZ.Rao20_lemma2"]

[gates]
verify      = "pass"
coqchk      = "pass"
mutants     = "pass"
rust        = "pass"
statements  = "pass"
docnumbers  = "pass"
ceilings    = "pass"

# verify 12m12s, 731 audited theorems all Closed under the global context
# coqchk 2m58s, whole-library census exactly Sunflower.ALWZ.Rao20_lemma2
# mutate 86m10s, 160 mutations, 157 killed, 2 declared survivors,
#        controls 1/1, 0 unexpected
# rust   26m41s, 36 suites, 339 tests, 0 failures -- after installing
#        cryptominisat5, absent from the rebuilt container; see roadmap 36.6

[[claim]]
id        = "covering-number-at-least-two"
statement = "An intersecting 3-sunflower-free family of 4-sets with 27 or more members has no common point, unconditionally, from the proved g(3) <= 26 rather than the 1969 value."
kind      = "theorem"
evidence  = "Support.twenty_seven_four_sets_have_no_common_point"
novelty   = "new-to-this-development"
search    = "none run"

[[claim]]
id        = "pair-link-bound"
statement = "The link of a pair of points is (b-2)-uniform and sunflower-free, so at most g(b-2) members contain any given pair; at b = 4 that is six, and six is attained."
kind      = "theorem"
evidence  = "Support.link_at_pair_bounded"
novelty   = "new-to-this-development"
search    = "none run"

[[claim]]
id        = "thirty-two-needs-nine-points"
statement = "A 32-member intersecting 3-sunflower-free family of 4-sets needs at least nine ground points, by counting member-pair incidences in both orders."
kind      = "theorem"
evidence  = "Support.thirty_two_four_sets_need_nine_points"
novelty   = "new-to-this-development"
search    = "none run"

[[claim]]
id        = "anchored-support-bound"
statement = "An intersecting b-uniform 3-sunflower-free family of n members has support at most (4b-3) + (b-2)n, improving PureLink.intersecting_support_bound from 97 to 77 at (b,n) = (4,32) and from 23 to 20 at (3,11)."
kind      = "theorem"
evidence  = "Support.anchored_support_bound"
novelty   = "new-to-this-development"
search    = "none run"

[[claim]]
id        = "the-core-is-met-twice"
statement = "The core the support proof builds is met in at least two points by every member, and the link cover never exceeds two members, checked over an exhaustive sweep of 127466 families by a rebuild sharing no code with the Coq development."
kind      = "measurement"
evidence  = "every_member_meets_the_anchored_core_twice"
novelty   = "new-to-this-development"
search    = "none run"

[[claim]]
id        = "crossover-is-real"
statement = "The two-anchor bound beats the single-anchor bound exactly when n > 4b-4, so the new number is the worse one below the crossover."
kind      = "measurement"
evidence  = "the_second_anchor_pays_off_exactly_above_four_b_minus_four"
novelty   = "new-to-this-development"
search    = "none run"

[[claim]]
id        = "furedi-has-no-delta-systems"
statement = "Furedi 1978, named by the session brief as a possible source of a published barrier remark about the greedy/covering method, contains no Delta-system material of any kind and therefore cannot carry one."
kind      = "refutation"
evidence  = "docs/papers/furedi78-rendered-pass.md"
novelty   = "not-new"
search    = "All 31 pages (177-207) rendered at 140 dpi and read, logged per page in docs/papers/furedi78-rendered-pass.md. The words Delta-system and sunflower occur nowhere; Erdos-Rado 1960 is not among the nine references on p. 207 and neither is Abbott. The paper is about the Erdos-Rothschild-Szemeredi problem (p. 178): the largest intersecting r-uniform family with maximum degree at most c|F|, via fractional matchings and covers, nu-critical nuclei, Baranyai's theorem and Pelikan's theorem. docs/reading.md A15."

[[claim]]
id        = "the-acquisition-was-not-impossible"
statement = "Session N+11 reported Furedi 1978 as having no digitisation after four routes; it is a 31-page scan on the author's own Renyi Institute publication list and one request fetched it."
kind      = "correction"
evidence  = "docs/reading.md"
novelty   = "not-new"
search    = "www.renyi.hu/~furedi/PUBS3/furedi_005_ekr_with_upper_bound.pdf, 723721 bytes, retrieved 2026-08-10. The Illinois host session N+11 tried resets the connection from this environment. Recorded as rule 29."

[[claim]]
id        = "iota-three-is-ekr-extremal"
statement = "The iota(3) = 10 witness is an EKR-extremal intersecting family of 3-sets on six points, taking one set from each of the ten complementary pairs, so at b = 3 the sunflower-free constraint costs nothing."
kind      = "measurement"
evidence  = "the_iota_three_witness_is_also_ekr_extremal"
novelty   = "new-to-this-development"
search    = "Furedi 1978 p. 186 builds his extremal family from a 3-uniform intersecting system with 10 members on a 6-element set and says there is exactly one such. The parameters coincide exactly; the identification with his H_1 is NOT made, because Figure 1 is a dot diagram this pass did not decode. docs/reading.md A16."

[[claim]]
id        = "substitution-preserves-maximality"
statement = "If both seeds of an Abbott-Hanson-Sauer substitution are maximal intersecting families whose covering number equals their uniformity, the substituted family is maximal: no set of any kind can be added, on any ground set."
kind      = "theorem"
evidence  = "Substitution.substitution_is_maximal"
novelty   = "new-to-this-development"
search    = "none run"

[[claim]]
id        = "the-tower-is-maximal-in-the-kernel"
statement = "The three pure-substitution rows of roadmap section 13.1 are now theorems rather than measurements: b = 4 (27 members), b = 6 (300) and b = 9 (10000), the last being where AHSOptimal has no margin at all."
kind      = "theorem"
evidence  = "Substitution.iota3_squared_is_maximal"
novelty   = "new-to-this-development"
search    = "none run"

[[claim]]
id        = "covering-number-from-a-seed-certificate"
statement = "The covering-number hypothesis, quantified over all lists, follows from a 2^|U| check on the seed's ground set, because a cover intersected with the ground set still covers."
kind      = "theorem"
evidence  = "Substitution.tau_of_certificate"
novelty   = "new-to-this-development"
search    = "none run"

[[claim]]
id        = "a-proposal-that-was-already-done"
statement = "This session proposed the b = 9 extension question as an unchecked moonshot; roadmap section 13.1, STATUS.md and rust/tests/extension.rs had all already settled it, and the Rust file written before that was noticed was deleted rather than committed."
kind      = "correction"
evidence  = "docs/reading.md"
novelty   = "not-new"
search    = "none run"

[[claim]]
id        = "the-doubling-lemma-is-prior-art"
statement = "Intersecting.doubling_lower_bound, 2*iota(k) <= g(k), was stated by Domotor Palvolgyi in a Polymath10 comment on 23 December 2015 and re-derived independently here. Five modules sit on it and none of them changes; what changes is that the development now carries the citation."
kind      = "correction"
evidence  = "docs/reading.md"
novelty   = "not-new"
search    = "Comment 23193 on gilkalai.wordpress.com/2015/12/08/polymath-10-post-3-how-are-we-doing, 2015-12-23T17:53:31+03:00, author domotorp, retrieved first-hand via https://public-api.wordpress.com/rest/v1.1/sites/gilkalai.wordpress.com/comments/23193 . Verbatim, LaTeX taken from the alt attributes of the two rendered formula images: If we denote the size of the largest k-uniform intersecting family without an r-sunflower by f^{int}(k,r), then we have (r-1) f^{int}(k,r) <= f(k,r). At r=3 that is 2*iota(k) <= g(k)."

[[claim]]
id        = "an-intersecting-computation-was-run-in-2015"
statement = "Since session N+9 this repository has believed no computational work on intersecting sunflower-free families exists. Philip Gibbs ran one on 25 November 2015: randomised, 100 runs per parameter, fifteen (k,n) pairs, reaching maxima of 10 at k=3, 24 at k=4 and 58 at k=5."
kind      = "refutation"
evidence  = "docs/reading.md"
novelty   = "not-new"
search    = "Comment 22690 on gilkalai.wordpress.com/2015/11/11/polymath10-post-2-homological-approach, 2015-11-25T22:42:32+03:00, author GFP, retrieved first-hand via the WordPress.com JSON API. All 434 comments across the seven Polymath10 threads (post IDs 13306, 13347, 13400, 13447, 13932, 13405, 14293) were fetched and searched for the word intersecting; 39 match and this is the only one reporting an executed intersecting computation. Scope: the previous wording said no executed intersecting search IN ANY REFEREED SOURCE, and that qualified form still stands - a blog comment is not refereed. What is refuted is the unqualified belief the qualifier was standing in for."

[[claim]]
id        = "the-repository-is-ahead-of-the-2015-numbers"
statement = "Against the one executed intersecting computation: level at b=3 (his 10 is the exhaustive value here), ahead at b=4 (27 against 24), ahead at b=5 (78 against 58). His search was randomised, so none of his numbers is an upper bound and none is in tension with anything proved here."
kind      = "measurement"
evidence  = "the_repository_is_ahead_of_the_2015_maxima"
novelty   = "new-to-this-development"
search    = "none run"

[[claim]]
id        = "the-2015-experiment-reproduces"
statement = "plateau::search with zero force moves is the 2015 random-fill process: re-running all fifteen rows gives means within 0.5 of the reported ones on every row that can be run here, fourteen of fifteen. The (5,31) row is beyond plateau::candidates 28-point enumerator and was not re-run."
kind      = "measurement"
evidence  = "the_2015_random_fill_reproduces"
novelty   = "new-to-this-development"
search    = "none run"

[[claim]]
id        = "the-2015-experiment-was-underpowered"
statement = "At (4,9) - the nine points the 27-member family of Product.iota_four_at_least_27 lives on - a random fill reaches 27 nineteen times in a million runs. In 100 runs the expected hit count is 0.002, so the 2015 report of 21 there was not a near miss: the experiment was about five hundred times too small to see the answer once."
kind      = "measurement"
evidence  = "the_fill_reaches_twenty_seven_but_almost_never"
novelty   = "new-to-this-development"
search    = "none run"

[[claim]]
id        = "every-sampled-twenty-seven-is-the-ahs-family"
statement = "Five million fills at (4,9) produced 106 hits at size 27, of which 50 are distinct as labelled families; canonicalised under all 9! = 362880 relabellings they fall into one orbit, and it is Product.iota4 s. This is EVIDENCE for uniqueness and not a proof - the exhaustive census was attempted three times and did not finish."
kind      = "measurement"
evidence  = "every_twenty_seven_is_the_ahs_family_relabelled"
novelty   = "new-to-this-development"
search    = "none run"

[[claim]]
id        = "palvolgyi-implies-abbott-gardner"
statement = "Palvolgyi 2015 equality remark, which he himself called unlikely, implies Abbott-Gardner 1969 given the exhaustive iota(3) = 10 - so it is at least as strong as a published theorem. It lands on g(3) <= 20 exactly, because ~ GAtMost 3 19 is proved from a twenty-member family rather than cited."
kind      = "theorem"
evidence  = "Palvolgyi.palvolgyi_implies_abbott_gardner"
novelty   = "new-to-this-development"
search    = "none run"

[[claim]]
id        = "the-iota-four-ladder-now-tests-a-conjecture"
statement = "If the iota(4) ladder closes at 27, Palvolgyi remark says g(4) = 54 exactly - and Product.lower_bound_4_3_54, the doubled substitution family, has exactly 54 members. Its content at b = 4 is precisely that the doubled substitution family is optimal, so deciding iota(4) settles more than a value."
kind      = "theorem"
evidence  = "Palvolgyi.palvolgyi_at_four_if_iota_four_is_27"
novelty   = "new-to-this-development"
search    = "none run"

[[claim]]
id        = "the-wrong-url-not-a-hostile-host"
statement = "Four sessions recorded gilkalai.wordpress.com as blocking this container. The slug every attempt used, 2015/12/11/polymath10-post-3, does not exist; the post is at 2015/12/08/polymath-10-post-3. A wrong slug returns an 80 KB 404 body that renders like a block."
kind      = "correction"
evidence  = "docs/reading.md"
novelty   = "not-new"
search    = "none run"

[[claim]]
id        = "second-solver-claim-corrected-again"
statement = "Section 33.8's one-line verdict still said the ten-point rung was re-decided by a second solver; section 33.5 says correctly that cryptominisat5 was stopped inside that rung, so it rests on cadical alone."
kind      = "correction"
evidence  = "docs/roadmap.md"
novelty   = "not-new"
search    = "none run"
```

## Results

See `docs/roadmap.md` §34. In brief:

**1. The covering number, unconditionally.** A family every member of
which contains a fixed point *is* its own link at that point, so `g(b−1)`
caps it. At `b = 4` the cap is `PureLink.g_three_at_most_26`, which is
proved rather than cited, so a 27-member family has covering number at
least two — and 27 is exactly the known lower bound for `ι(4)`, so the
statement bites on the extremal object itself.

**2. The counting ceiling.** The pair link is `(b−2)`-uniform and
sunflower-free, so `deg [x;y] F ≤ g(b−2)`. Counting incidences `(A,Q)`
with `Q` a two-element subset of `A` in both orders — the list-level
Fubini `PureLink.degsum_eq_sizesum` does for single points, done here for
pairs — gives `|F|·C(b,2) ≤ C(g,2)·g(b−2)`. At `b = 4` the two sixes
cancel and `C(8,2) = 28 < 32 ≤ 36 = C(9,2)`.

**3. Two anchors instead of one.** One anchor charges each member `b−1`
new points. Two anchors meeting in exactly one point charge `b−2`,
because a member avoiding the shared point meets them at two *different*
points; the members through the shared point are covered by two members
of its link, since three pairwise disjoint ones would be a sunflower.

## Negative results, with budgets

* **Exhausted.** Every intersecting 3-sunflower-free family on `(6,2)`,
  `(5,3)`, `(6,3)`, `(7,3)`, `(6,4)` — 127 466 of them — satisfies the
  support bound, the core-met-twice property, the pair-degree bound and
  (at `b = 4`) the counting ceiling. No limit hit.
* **Stopped for a measured reason.** The exhaustive sweep stops at
  `(6,4)` because `(7,4)` has 35 333 735 families and `(8,4)` has more
  than forty million. `(8,4)`, `(9,4)`, `(10,4)` and `(9,3)` are
  **sampled** — 14 000 deterministic pseudo-random maximal families — and
  that is labelled as sampling, not exhaustion.
* **Not attempted.** No ladder was run. `ι(4,11)` is where §33.5a left
  it, and nothing here claims otherwise.

## Corrections

* **An acquisition reported as impossible.** "No digitisation found, not
  on arXiv, not on the author's page" was a claim about the world derived
  from four dead routes, one of which was a host that resets the
  connection. `docs/reading.md` rule 29: *a failed acquisition is a
  statement about the routes tried, never about the document.*
* **The brief's premise about Füredi 1978 was wrong.** It was named as a
  place a Δ-system barrier remark might live. It is not a Δ-system paper.
* **§33.8 still carried the over-claim §33.5 had already retracted** —
  "a second instrument and a second solver" for the ten-point rung. Fixed
  eight paragraphs after the correction that should have caught it.

## Reproduction

```
make -j4 verify
make coqchk
python3 tools/mutate.py
cd rust && cargo test --release
make statements && make docnumbers && make ceilings
```

## What a reviewer should attack

**The two-anchor case split.** The proof splits on whether some member
meets the anchor in exactly one point, and only one branch builds a link
cover. A sweep that exercised one branch would leave the other
unfalsified, so the test asserts both counts (7 293 and 120 168). If that
assertion were dropped the suite would still pass on a broken proof.

**`all the numbers are `nat`.** `(4b − 3)` and `(b − 2)` are truncated
subtractions. At `b = 1` the bound degenerates and the theorem is stated
with `2 ≤ b`; the Rust mirror special-cases `b < 2` and that split is
where a disagreement between the two would hide.

**The nine-point floor cites `g(2) ≤ 6`,** which is
`PureLink.g_two_at_most_six_sharp` — proved — but the *cancellation* that
turns the ceiling into `|F| ≤ C(g,2)` is arithmetic that only works at
`b = 4`. At any other uniformity the two sides do not cancel and the
corollary would need re-deriving.

## Handover

`docs/roadmap.md` §34.9, and §34.5 first: the `ι(4)` ladder has a
reachable ceiling around twelve ground points and a proved floor of nine,
and closing that gap is not a search problem.
