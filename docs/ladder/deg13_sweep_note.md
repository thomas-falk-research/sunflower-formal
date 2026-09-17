# deg(0) = 13 sweep — working note

**Status: 2026-09-17T03:14Z.** Re-verify with `checkpoint_audit.py`; the
figures below go stale as rows land.

This is the operator's note for the long-running `iota(4,11) >= 32`,
deg(0) = 13 sweep. It was carried for days inside a scheduled check-in
prompt, where it would have died with the session; it lives here now so it
survives.

**The commit history is authoritative, not this file.** Every figure below
is a headline plus the commit that derived it, and that commit is the
record. If this file and a commit disagree, the commit wins. Re-derive
from the tools rather than quoting this file from memory.

---

## What is being decided, and what it is not

`deg(0) = 13` is a single cube of the `iota(4,11) >= 32` rung, split into
**1949 degree sequences**. The cube is UNSAT only when **all 1949** are
UNSAT. The percentage below is a counter, not a rung: at 39.66% the
remaining 1176 could still contain a SAT and the rung would not fall.

This sweep is a **second opinion** on cadical's UNSAT for the same cube at
85123.9 s, run under cryptominisat5.

The published bracket is unchanged throughout: **27 ≤ ι(4) ≤ 71**.

---

## Driver

    ./rust/target/release/examples/iota_sym 4 11 32 --only-deg 13 \
      --solver cryptominisat5 --seqprefix 11 --cubecap 2000 \
      --slice 60 --seconds 21600 --threads 4 \
      --checkpoint docs/ladder/iota4_11.deg13.cryptominisat5.tsv

`--seconds` is the **per-cube** budget (21600 s = 6 h), not a total.
Four solver slots run concurrently.

Current pid **32688**, launched 2026-09-16T16:55:41.810Z after restart #36.
Find it with `pgrep -x iota_sym`; **never** `pgrep -af iota_sym`, which
matches the checking shell itself (72dd356). `ps -C cryptominisat5` did not
filter usefully when tried.

---

## Tools — use them, do not re-derive by hand

| tool | what it gives |
|---|---|
| `checkpoint_audit.py [rev]` | re-resolves every row; six invariants; frontier, holes, percentage, cap history. **Run it whenever a row lands.** |
| `checkpoint_audit.py --spans all` (~20 s) | span record, hole trajectories, **computed** monotonicity, ranking, duration distribution. An **open span refuses a duration by design**; a windowed walk left-truncates and refuses to rank. |
| `cnf_mtime_check.py` | validates the CNF-mtime method and prints in-flight cube→pid pairings **with elapsed seconds**. This is what tells you whether a forward-test target is still unobserved. |
| `forward_test.py` | pinned to `REV_AS_RUN = 9528aa9`. `IDX` is keyed on the **label string**, `SEQ` is the list, `cube_list` is the function. |
| `/proc/<pid>/stat` field 22 vs `btime` | a process's exact launch time. Better than any recalled "launched at HH:MM" (4083af8). |

Reuse the helpers with:

```python
exec(open('docs/ladder/forward_test.py').read()
     .split("# ---...--- calibration")[0])   # split on the real calibration banner
```

**Compare tree / staged / HEAD row counts before resolving** (1e409e8;
fired again at 85691ce and dd332e7). The audit reads the **working tree**;
the resolution script reads the **staged index**. When they differ,
re-stage. The waiter polls every 20 s and cannot resolve two close
landings — it is never the source of the count.

---

## Reading the checkpoint

- Rows land in **completion order, never index order**. A row below the
  previous landing is a **straggler**, not a regression (5b0f385, c1fd32f).
- Holes in the frontier are **in-flight work**. A long-running hole is
  **not a stall**: a stall is an `UNKNOWN` row written **at the cap** plus
  0.4–1.4%, never silence.
- **Decided cost** = `max(cost)` over that label's non-`UNKNOWN` rows. 80
  labels carry multiple rows; in 27 the naive max over all rows differs.
  No label is decided twice (invariant I4).
- Say "0 labels undecided-only", never "0 UNKNOWN": there are 169 `UNKNOWN`
  rows in the file, each superseded by a later `UNSAT` on the same label.
- **The cap is soft** (a252d3e). Tight cost clusters sit *above* their
  nominal cap by an amount proportional to it, so a decided cost slightly
  over the cap is a cube that finished inside the checking lag, not an
  anomaly.
- A **block** is the **first four entries only** (ac23afa). A sub-family,
  level or group closing is *not* a block closing.

---

## Restart accounting

Thirteen involuntary restarts, CPU-hours discarded:

    5.160  1.190  4.800  2.645  1.330  2.111  7.204
    3.594  3.564  4.863  2.965  7.033  2.216

median 3.5640, mean 3.7442, **total 48.6747**. The 0.944 CPU-hours at
01:31Z on 09-14 is **not** in this series — that was a stop I chose.

### Absorbing a restart

1. **Check the binary exists** (`rust/target/release/examples/iota_sym`).
2. **Measure before relaunching** — the new driver overwrites CNFs.
3. Teardown instant = mtime of the `[killed]` marker at the end of the
   killed task's output file. Check **both** the driver's and the waiter's,
   use the **earlier**, and note they are **not guaranteed to agree**
   (4083af8). The waiter's output also settles whether a row landed in the
   window.
4. Lost work by the **CNF-mtime method**, glob **always filtered by pid**
   (`/tmp` held 156 CNFs at #36; exactly 4 carried the dead pid). Never
   `/proc/stat btime` for this.
5. Weight by each cube's cpu/elapsed ratio from the last sample before
   teardown, and say that the processes are gone and it is not re-samplable.
6. Re-read `nproc`, CPU model and `MemTotal` and **compare**.
7. Relaunch verbatim, get the new pid's exact launch from `/proc`, append a
   restart header block to the TSV, commit, push, re-check `origin/main` is
   still an ancestor.
8. **A new restart opens the next re-run set.**

Machine spec has been identical for four consecutive containers: 4 cores,
Intel(R) Xeon(R) Processor @ 2.10GHz, MemTotal 16482220 kB. Four is four,
not a promise — re-read it at #37.

**Re-take lag** after a relaunch: 41 s at #35, 60.7 s at #36. Two
observations, not a law. That 60.7 s is near the `--slice 60` value is
**not supported** — #35 ran 41 s under the identical flag.

---

## Re-run sets — all four CLOSED

Ratio is **discarded / re-run** (cd2ad61 — it was carried inverted once and
corrected at 060fb26 by checking it against published data).

| set | commit | n | median | spread |
|---|---|---|---|---|
| one | `8782234` | 8 | 0.3594 | 54.99× |
| two | `cd2ad61` | 4 | 0.4291 | 8.15× |
| three | `1e409e8` | 4 | 0.5026 | 2.06× |
| four | `30f1fbd` | 4 | 0.2125 | 5.3747× |

Set four in full (all four members restarted at the **same instant**, so
their re-run clocks are directly comparable):

| idx | discarded | re-run | ratio |
|---|---|---|---|
| 769 | 3423.1 | 6139.4 | 0.5576 |
| 770 | 1956.0 | 9291.9 | 0.2105 |
| 771 | 1807.8 | 8426.4 | 0.2145 |
| 772 | 853.1 | 8223.6 | 0.1037 |

**The falling-spread sequence is broken.** 54.99×, 8.15×, 2.06×, **5.3747×**
— every record of the first three said "a sequence, **not** a trend", and
the fourth went back up. Medians did the same: 0.3594, 0.4291, 0.5026,
0.2125. Neither is monotone and neither ever was a trend. This is the
caveat being vindicated, **not** a new finding in the other direction:
four points at n = 8, 4, 4, 4 support no shape.

Concordance in set four resolves to **ordinary**: 3 of 6 pairs, exactly the
chance value. The "anti-concordance" visible at n = 2 and n = 3 was labelled
NOT A FINDING both times, which is why nothing had to be retracted.

**A fourteenth restart opens set five.**

---

## Spans (broken-frontier episodes)

Quote **no span figure until the span closes** — no duration, no rank, no
monotonicity. When the last hole fills, run `--spans all` and **copy** the
figures.

| closed by | commits | duration | hole counts | monotone |
|---|---|---|---|---|
| `41b168e` (rec. `3ebf469`) | 7 | 6:05:59 | 2,2,3,2,1,1,1 | **False** |
| `49ddb49` (rec. `8cfb7dc`) | 8 | 3:00:37 | 3,3,2,2,2,1,2,1 | **False** |
| `30f1fbd` (rec. `068b963`) | 2 | 0:52:58 | 2,1 | **True** |
| `6286fe4` (rec. `370cfae`) | 3 | 2:25:37 | 3,2,1 | **True** |
| `446a24f` (rec. `25ce2c7`) | 1 | 1:14:38 | 1 | **True**, vacuously |
| `84bde6a` (rec. below) | 5 | 2:20:52 | 3,3,2,1,1 | **True**, non-trivially |

**These are not compared with each other.** Four points are not a trend,
and a span's duration is set by which cubes happened to be running long
when a fast one finished — the same accident that sets how many holes it
opens with. Monotonicity reads False, False, True, True: a **list**, not a
trend. The third came back `True` only because a two-commit span has
exactly one opportunity to rise; the fourth ran 3,2,1 and the shape was
still not called until the tool computed it, because both multi-commit
spans before it had looked like they were shrinking and then went back up.

Ranks disagree, so give both. The sixth span: **12 of 71** by duration
(11th is only 4:45 longer); **28 of 71** by commit count, five tied at 5 —
the honest form is that **23 of 71** ran longer than 5 commits. Read
through the distribution: **44 of the 71 are 0 or 1 second**, so rank 12
of 71 is rank 12 of the 27 that lasted at all.

**The fifth span's `True` is vacuous.** A one-commit span has a one-point
hole trajectory, and a single number is non-increasing by definition —
`True` there means only that the tool ran. It must **never** be added to
the False, False, True, True list as a fifth observation. The `True` at
`30f1fbd` was already weak for the same reason (a two-commit span has
exactly one chance to rise); this one has none.

Durations 6:05:59, 3:00:37, 0:52:58, 2:25:37, 1:14:38 are not monotone,
and commit counts 7, 8, 2, 3, 1 are not either. Both are set by which
cubes happened to be running long when a short one finished — the same
accident that sets how many holes a span opens with.

**The sixth span's `True` is the first non-trivial one.** Five points,
with two flat steps (3→3 and 1→1) where the count could have risen and did
not. The `True` at `30f1fbd` had one chance to rise; `446a24f` had none.
Six spans now read False, False, True, True, True-vacuous, True — still
**not** a trend: a hole count rises only when a cube that started late
finishes before ones that started early, which is an accident of which
cubes happen to be long.

Durations 6:05:59, 3:00:37, 0:52:58, 2:25:37, 1:14:38, 2:20:52 are not
monotone, and commit counts 7, 8, 2, 3, 1, 5 are not either.

**A seventh span is OPEN** as of 03:13:43Z: idx 790 landed while 787, 788
and 789 were still running, so the frontier broke with **three** holes. idx
787 filled at 03:43:32Z, leaving **two** — 788 and 789. idx 791 landed at
03:50:40Z and did **not** widen it: 790 was already decided, so the highest
decided simply moved 790 → 791 with the same two holes. idx 793 at 04:02:47Z
**did** widen it, landing ahead of 792: holes are now **three** again, [788,
789, 792]. A span's hole count is not monotone while it is open, in either
direction, and no duration, rank or monotonicity for this one until the last
hole fills.

The tool's **"opened after" is the last unbroken commit**, not the previous
span's record commit — asserted wrongly at `0b68df2`, corrected at
`068b963`. More precisely, it is the last commit that **touched the
checkpoint** and left the frontier whole: the fourth span names `068b963`
rather than `fca972d` because `fca972d` added only this note file and
changed no data row (checked with `git show --stat`, not assumed).

---

## Forward tests — their own series

Kept **separate** from the pattern tally so a failure is never absorbed
into a count containing successes.

| commit | outcome | one-sided p | target |
|---|---|---|---|
| `6ec69dc` | NULL | 0.1235 | — |
| `73fcf31` | **MISS** | 0.0245 | idx 760 |
| `aea7189` | **MISS** | 0.4130 | idx 765 |

**Three registered, zero hits. None currently open.**

**The counter-caveat is mandatory.** Under the pinned nulls,

    P(zero hits in all three) = 0.8765 × 0.9755 × 0.5870 = 0.5019

A 0-for-3 record is the **single most likely** outcome of these three tests
with no predictive skill at all. It is **not** evidence of being
systematically wrong, any more than 3-for-3 would be evidence of skill.
**Quote the 0.5019 whenever the 0-for-3 is quoted**, exactly as the 0.675
must accompany the pattern tally's five-for-five.

Registration discipline, learned the hard way:

- **Register only while the outcome is unknown**, and verify the target is
  still running *after* the push (a22c6e7 vs 73fcf31).
- **Condition the null on what you already know** — a target that has run
  1148 s cannot cost less — and **pin it at registration**. Never recompute
  it to suit the outcome, in either direction. Say whether the
  unconditional rate would have flattered a hit, and by how much.
- **Label a weak test weak at registration**, not afterwards (aea7189), and
  register it anyway: protecting a record is the wrong incentive, and
  declining to guess earns nothing (582247f).
- **A band built from points is not evidenced by those points** (3f7c27c).
  Count only out-of-sample members.
- **Do not rescue a failed prediction** by retreating to the part that held
  (d6ff6d3, f0866f6) — **and do not adopt its inverse either** (6dfa62d).

---

## Closed — do not reopen, re-run, reshape or mourn

- Tight band broke `abbd653`; second band `b34fc2e` (CV rank 100 of 680,
  ordinary).
- 0.3-second cost coincidence `d0d1a58`; the tight triple `a22c6e7` is the
  same thing — 4 of 757 triples were that tight and the threshold was set
  by the triple itself.
- 1:55:26 span coincidence `ba6ec65`. 741 naming collision `e5243fc`.
- Block `[13,13,12,10]` closed 49/49 at `49ddb49`. Closed-block descriptive
  stats — **not findings, not compared across**: `[13,13,12,12]` 82 members
  54.1 / 3442.9 / 12831.3, spread 237.18×; `[13,13,12,11]` 65 members
  144.8 / 5704.7 / 16785.7, spread 115.92×; `[13,13,12,10]` 49 members
  578.0 / 5744.1 / 15490.4, spread 26.80×. Spreads fall, minima **rise**,
  maxima **not** monotone; three points at unequal n.
- `SEQ[j][7] = 13` group complete 14/14 at `cf2bccc`, idx 755..768
  (contiguity **verified**): 720.2 / 4441.1 / 5406.6, spread 7.5071×.
- **The sub-family / level story is closed and falsified**
  (`b8291e4` → `aea7189` → `a70828b` → `d6ff6d3` → `948005d` → `6dfa62d`).
  Within block `[13,13,12,9]` by `SEQ[j][8]`: `=13` 6/6 [720.2, 2390.5];
  `=12` 4/4 [4477.0, 5406.6]; `=11` 3/3 [4405.2, 5178.2]; `=10` 1/1 4502.5.
  `=11` is **below** `=12` at both endpoints and the ranges overlap.
  "Costs rise as the level falls" is dead — **and the inverse is not a
  finding either**. The only defensible statement: `=13` is far cheaper
  than what follows; `=12`, `=11`, `=10` are not distinguishable at these
  sample sizes. **Never cite 762/763/764 as support** — all three had
  already run past the threshold when the claim about them was written.
- CNF-mtime method `07b8a61`: ≤ 1 s, n = 8 pinned. It does **not** validate
  the restart case — the `[killed]` marker's own timing is untested and
  **that gap stays open**. Twenty-eight live samples through 19:14:28Z all
  gave max |delta| 0 or 1 s; separate samples, not a reproduction.
- Percent arithmetic — not a result, not in the tally: 36% at idx 702
  (`c235cb5`), 37% at 718 (`cd2ad61`), 38% at 738 (`e33ce40`), 39% at 760
  (`3f7c27c`), **40% at 779** (`86562d4`). Next: 41% needs
  `ceil(0.41 × 1949) = 800`.
- The rebase `109dc97`. **Any PR from here is a new pull request**; #19 is
  finished and must never be reused.

---

## Rules

Compute a quantitative claim **before** writing it (78e5127). No "-ish"
(abbd653). A rounded milestone is not a crossed one, nor is a round **count**
(b34fc2e, 85bb4d1). **Never assume the next index** (d0d1a58).

**Read the figure off the tool; do not recall it** (ba6ec65 / beaa0d3). A
windowed `--spans` walk is not the record.

**Never write an identifier you have not read from the tool** (`bce9af0`).
Commit hashes, pids, indices and timestamps are **read**, never composed.
If the identifier does not exist yet — because the commit has not been
made — omit it, or commit first and patch it in afterwards. At `86562d4`
I wrote `85d9e94` into this file twice for a commit that did not exist;
`git cat-file -e` confirms it never did. A plausible-looking hash is worse
than no hash: a missing one is obviously missing, a wrong one is not.

**Two agreements are two draws, not a property** (4083af8). At restarts #34
and #35 the driver's and waiter's `[killed]` markers carried the *same
nanosecond*; at #36 they differed by exactly 4.000000 ms. The observation
did not reproduce. This is **not** an error-pattern instance — both earlier
records explicitly called it corroboration and *not* validation and left the
gap open, which is exactly why the third sample cost nothing.

**An observation whose outcome was already determined when it was written
earns nothing from that outcome** (aea7189). Reconstruct the row's start
time and compare it with the claim's timestamp. Same rule as "a test whose
target is already observed is not a test", applied to prose.

**Withdraw a guess explicitly when the measurement arrives** (4083af8).

**`idx a..b` means a contiguous span — check contiguity before printing it**
(cf2bccc). `min..max` of a member list is not a span.

**A run of misses at high nulls is not evidence of anti-skill** (d6ff6d3).
Multiply the (1 − p) values first.

**A bound that the closed value respects is a bound behaving like a bound,
not a prediction that came true** (47ef34b, 0b68df2, 30f1fbd).

**The waiter's "ROW LANDED" time is up to 20 s late** (948005d) — it is the
poll that noticed the row, not the write. The "2 s agreement" quoted at
aea7189 was one draw, not precision. Irrelevant against thresholds of
thousands of seconds; CNF-mtime is a separate, separately validated
instrument.

When two ranks of the same thing disagree, **give both** (3ebf469). **Read
the rank through the distribution** (99fd566, 3ebf469).

**Check a definition against published data** (060fb26) — do not re-read it
and believe yourself. **Two figures differing by under a percent do not
confirm each other** (37d44af). **A check that cannot fail is worse than no
check** (99fd566).

**Do not summarise a sequence into a shape; print it and compute the shape**
(cd03f27, 45aacf6, cd2ad61, 1e409e8, 3ebf469, 8cfb7dc, a70828b).

**Scope a superlative to the population you checked** (5c3b08e, e33ce40). A
rank of 1 over 1 is degenerate (85691ce). A rank of N over N in a
mostly-undecided block is worth almost nothing — the decided set is selected
for having finished.

**A caveat is for exactly this** (e33ce40; a70828b → d6ff6d3; 4083af8). **A
mechanism may only explain data it predates** (1e409e8, f0866f6). **Check the
instrument before accusing the figure** (cd03f27). **Quote a measurement as
measured, then name its weakness** (37d44af). **Put the caveat in the code,
not the prose** (4be4958).

A gap that spans a restart is not a gap (c50c59e). A gap whose endpoint is
only bounded is an **interval**, not a measurement (85691ce, c1fd32f).

A statement true at its timestamp is not an error when the state moves
(d06dbe4) — **but that protects a dated record, not a live one.** A figure
sitting in a section that is rewritten around it is being asserted as
current, whatever was true when it was typed. **Refreshing a section means
re-deriving every figure in it, not the ones that catch the eye**, and a
quantity is stated **once** so there is no second copy to go stale. Two
defects in this file were found this way and corrected together (hash
omitted deliberately — it cannot be read before the commit exists):
`## State at 068b963` named a commit where the checkpoint held **942** rows
while the body under it described **957**, surviving six refreshes; and
"1169 undecided", correct at `86562d4` when 780 were decided, sat two lines
under an updated "1161" through three more. Neither overshot its evidence.
Both were simply never re-read.

Take a second sample before quoting a zero (07b8a61). A bound is never ranked
against completed costs (8263cab / 8782234). **Gaps and uptimes: state, never
rank** (9f8cad2). **Holes and spans may be ranked — once closed.**

### Not hits, never in the tally

Block-record and cost-lead resets; the cap disjunction (255adbc); the c615
threshold (d395cb0); all three forward tests; both bands; every cost and
naming coincidence; all four re-run sets; the percent arithmetic; the
CNF-mtime validation; the checkpoint audit; the soft-cap finding; the 684
ratio bound; the spans and their ranking; closed-block and closed-group
statistics; the whole-frontier run length; restart ranks, uptimes and
re-take lags; declining to guess.

### Pattern tally

**Thirteen registered, twelve holding, one failing**, with two permanent
qualifications: the joint probability of five-for-five from always
predicting the prior majority is **0.675**, and two of the five sat on 100%
base rates — **never quote 5-for-5 without the 0.675**; and p=4 was a
*weaker* hit than p=5. **Quote the forward-test series and its 0.5019
alongside it.**

### Error patterns

- **A script whose output asserts what its code does not do — 24 instances**
  (#17 waiter false-positive, #18 61aebeb, #19 78e5127, #20 4be4958,
  #21 99fd566, #22 cf2bccc, #23 068b963, #24 a rank helper that printed a
  hardcoded "25 of 70" beside the tool's actual 26, self-flagged in the
  same line and never quoted). Both #23 and #24 were caught in scratch
  output before reaching a claim; the count includes them because a tally
  that only records the ones that escaped is not a tally.
- A definition carried inverted in my own note (060fb26).
- A figure recalled instead of read (ba6ec65).
- A tally quoted without its base rate (4e5e443).
- A bound quoted as a rank (8263cab).
- **The pattern I am most tempted to register is the one about to break**
  (5682de6) — two instances, 73fcf31 and aea7189.
- Rounding one measurement into a law (36ce276 / 0cf3b8d, cd03f27).
- A standing claim never re-checked (1802af3) — second instance: the
  `## State at 068b963` header, stale across six refreshes of the body
  beneath it, corrected in the commit that banked idx 787.
- A zero quoted from one sample as exactness (07b8a61, 948005d).
- A published figure compressed until it meant something else (8b557b5,
  cd03f27, 45aacf6).
- A superlative wider than its population (5c3b08e, e33ce40).
- A tally line contradicting the table under it (caff592) — second
  instance: "1169 undecided" two lines below "1161 undecided", the
  first stale from `86562d4`, corrected in the commit that banked idx
  787. **THIRD INSTANCE ONE COMMIT LATER**, in the commit that banked
  idx 793: the span's hole list, restated under the frontier line that
  carried it, left at two holes while that line went to three. The rule
  written for instance two did not prevent instance three; the staged
  diff caught it. **Neither of these two is on the pattern tally: they are
  procedural defects and their fix is a rule, not a prediction, and
  the tally is only for predictive commitments.**
- A convenient population by accident (c9982c9, a22c6e7).
- Two near-identical figures treated as corroboration (37d44af).
- A mechanism reached for to dismiss something (f0866f6).
- An already-determined outcome mistaken for corroboration (aea7189).
- A guess written into a durable record before the measurement arrived
  (4083af8, withdrawn in the same commit).
- **A FABRICATED IDENTIFIER** — `85d9e94`, a commit hash that never
  existed, written into this file twice and corrected at `bce9af0`. Its
  own pattern, not a script's fault, and the worst class of error here:
  every other defect on this list overshoots real evidence, while this one
  invents a pointer to nothing. One instance.

---

## Procedure when a row lands

1. **Arm a new waiter first** and confirm its startup line.
2. `git add` the checkpoint.
3. Run `checkpoint_audit.py`.
4. Compare **tree / staged / HEAD**; re-stage if tree and staged differ.
5. Resolve **every** new row through `IDX` — never by label count, never by
   assuming the next index.
6. Read counts from the **staged** index.
7. Read the diff, then commit **in the next invocation**. Commit with the
   heredoc **alone** — chaining a `for` loop after a heredoc mangles the
   parse and commits nothing.
8. Push with `-u origin`, retrying 2s / 4s / 8s / 16s.
9. **Tail-anchored** waiter check (0beb730):
   `tail -1 "$W" | grep -q '\[exited'` — never a whole-file grep.
10. Re-arm the waiter.

Task outputs live at
`/tmp/claude-0/-home-user-sunflower-formal/<session>/tasks/<task_id>.output`.

---

## State as of the last refresh (959 -> 960 rows)

- **960 rows; 791 labels decided; 791 UNSAT; 0 SAT; 0 labels
  undecided-only.**
- **Frontier contiguous 0..787, highest decided 793, holes [788, 789, 792].**
- **791 of 1949 = 40.5849%**; **1158 undecided**. 40% was crossed at idx 779
  (`86562d4`): 779/1949 = 39.9692% is not above 40, 780/1949 = 40.0205%
  is. Next: 41% needs `ceil(0.41 × 1949) = 800` — 9 more (799/1949 =
  40.9954% is not above 41; 800/1949 = 41.0467% is).
- **The counter is not the rung.** Two fifths of the sub-cubes are decided
  and every one came back UNSAT, and that settles nothing: deg(0) = 13 is
  UNSAT only when **all 1949** are, and any one of the undecided cubes
  counted on the line above could be SAT. *That count is stated once, on
  that line, deliberately: it was restated here as 1169 from `86562d4`
  onward and left stale through three refreshes while the line above was
  updated.*
- Block census: `[13,13,12,12]` closed 82/82; `[13,13,12,11]` closed 65/65;
  `[13,13,12,10]` closed 49/49; `[13,13,12,9]` (idx 755..792, contiguity
  verified) at **35 of 38**, three undecided: 788, 789, 792 — 792 is its
  LAST member, so it closes when those three land. A NEW block
  `[13,13,12,8]` has opened: **idx 793..820, 28 members, contiguity
  verified, 1 decided.** TWO BLOCKS ARE NOW OPEN AT ONCE, which is normal
  — four solver slots run ahead of the frontier and do not respect block
  boundaries. When either closes, record its descriptive stats as
  descriptive stats, NOT findings, and do NOT compare them across blocks.
- **One span is open.** Its holes are listed on the frontier line above and
  **nowhere else as holes** — they were restated here too, and this copy was
  left at two holes while the frontier line was updated to three. (The block
  census below names the same three indices today, but as undecided members
  of `[13,13,12,9]`: a DIFFERENT quantity that happens to coincide right now
  and will stop coinciding the moment a hole opens outside that block. Do
  not update one from the other.)
  Caught in the staged diff, not by the re-derivation; the fix is structural
  (state a quantity once, refer to it) because being careful demonstrably
  is not enough. No re-run set, no forward test, no registered pattern
  commitment. **Do not invent a commitment to fill the gap, and quote no
  span figure until this span closes.**
- All six audit invariants hold.
- **Bracket unchanged: 27 ≤ ι(4) ≤ 71.**

### One open question, with no answer

Whether to keep running here (4 cores) or move to a VM with 10+ cores. I
recommended moving. **The user has not decided, and this note must not be
read as though they had.** At roughly 43.3 cubes/day, ~1176 remaining is
~27 more days here; 48.6747 CPU-hours have been lost to thirteen restarts.
That is context for the question, not an answer to it.
