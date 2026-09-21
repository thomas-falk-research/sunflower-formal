#!/usr/bin/env python3
"""Check EVERY span figure written in deg13_sweep_note.md against `--spans all`.

WHY THIS EXISTS
---------------
Span ranks, durations, commit counts, tie counts, hole-count chains and
monotone verdicts are recomputed by hand at every close, by a scratchpad
script rewritten from scratch each time.  That has twice let a
recomputation pass key on a pattern that matched nothing and report
success anyway -- the note records both instances.  A script that finds
nothing reports the same silence whether there is nothing to find or its
pattern is wrong.

So this tool does two things, and the second matters as much as the first:

  1. it checks every parsed figure against the walk, and
  2. it ASSERTS HOW MANY FIGURES IT FOUND, and exits non-zero if the
     counts fall below the floors declared below.

A run that checks nothing is a FAILURE here, not a pass.

WHAT IT READS
-------------
* `--spans all` from checkpoint_audit.py -- the authority.  Durations are
  parsed from the `H:MM:SS` (or `N days, H:MM:SS`) string, NEVER from the
  parenthesised hours: those print to four decimals, the smallest step is
  0.36 s, and sub-second spans round across the one-second line.  The note
  records that exact error.
* the SPANS TABLE in the note: `| <ordinal> \`sha\` | dur | r of N | c | r of N (t tied) |`
* the MONOTONICITY TABLE: `| n | \`sha\` | chain | comparisons | verdict |`

CONVENTIONS, matching the note
------------------------------
* rank is COMPETITION ranking: 1 + (number strictly greater).
* the tie count is EXCLUSIVE: members sharing the value, minus itself.
* table ordinal n is walk position n + 65 (OFFSET below).
"""
import collections
import re
import subprocess
import sys

NOTE   = 'docs/ladder/deg13_sweep_note.md'
AUDIT  = 'docs/ladder/checkpoint_audit.py'
OFFSET = 65

# Floors: a run that parses fewer than these has a broken pattern, not a
# clean file.  Raise them when the tables grow; never lower them to make a
# run pass.
MIN_SPANS      = 100
MIN_TABLE_ROWS = 44
MIN_MONO_ROWS  = 58
# The opening-width census is written in PROSE at every span open and struck
# at every close, so it never reaches either table above -- and prose is where
# the stale figure lives.  At the fifty-seventh open the sentence read "the
# first opening at three since the forty-second" when the walk says the
# fifty-first, and it read so with the words "counted off the chains rather
# than recalled" attached to it: a claim of method that was false when
# written.  Nothing here could have caught that.  Now the census is parsed
# too -- ONLY while a span is open, because when none is open the sentences
# are correctly absent and their absence is not a failure.
# THE CENSUS FLOOR HAS A SAWTOOTH AND MUST LAG THE LIVE COUNT BY ONE.
# While a span is open the note carries one census sentence per past close
# PLUS the live entry's.  The CLOSING commit strikes the live one and adds
# nothing (it carries no figures), so the count DROPS BY ONE at that commit
# and is restored by the figures commit that follows.  Set this floor to the
# count at a CLOSING commit, never to the count while a span is open --
# raising it to the open-span count passes today and fails at the next close
# on correct prose.
MIN_CENSUS_SENTENCES = 7
MIN_CENSUS_LIVE      = 4
# The monotonicity prose -- the True partition, the False-chain column and
# the rank sentence beside them -- is the OTHER half of the gap the note
# named: "the remedy would have to be mechanical, and it is not one yet".
# It has gone stale three times on record (a headline stuck at 31 of 53 for
# a close, a False-chain list missing row 52's 4, "fifty-one verdicts" stale
# for three closes).  It is checked here.  FROZEN paragraphs are NOT: the
# one headed "as of ordinal 31" states its True partition at 31 and its
# False-chain list at 32, and naming its own vintage is exactly what makes
# it honest -- a checker keyed to the headline ordinal would fail correct
# prose.  Only the CURRENT bullets are checked.
MIN_MONO_PROSE       = 15

SPAN_OPEN = "<!-- SPAN-STATE: open -->"

# Ordinal words, BUILT rather than typed: a hand-written table of ninety-nine
# words is itself a place for a wrong entry to sit unread for months.
_ONES = ('first second third fourth fifth sixth seventh eighth ninth tenth '
         'eleventh twelfth thirteenth fourteenth fifteenth sixteenth '
         'seventeenth eighteenth nineteenth').split()
_TENS_C = 'twenty thirty forty fifty sixty seventy eighty ninety'.split()
_TENS_O = ('twentieth thirtieth fortieth fiftieth sixtieth seventieth '
           'eightieth ninetieth').split()
WORDS = {w: i + 1 for i, w in enumerate(_ONES)}
for _t, (_c, _o) in enumerate(zip(_TENS_C, _TENS_O)):
    WORDS[_o] = (_t + 2) * 10
    for _u, _w in enumerate(_ONES[:9]):
        WORDS[f'{_c}-{_w}'] = (_t + 2) * 10 + _u + 1
# Cardinals to ninety-nine, built the same way and for the same reason: the
# monotonicity prose counts things in words ("Fourteen of the thirty-four
# Trues"), and a word is a figure like any other.
_C1 = ('one two three four five six seven eight nine ten eleven twelve '
       'thirteen fourteen fifteen sixteen seventeen eighteen nineteen').split()
CARDS = {w: i + 1 for i, w in enumerate(_C1)}
for _t, _c in enumerate(_TENS_C):
    CARDS[_c] = (_t + 2) * 10
    for _u, _w in enumerate(_C1[:9]):
        CARDS[f'{_c}-{_w}'] = (_t + 2) * 10 + _u + 1


def secs(d):
    """Exact seconds from 'H:MM:SS' or 'N day(s), H:MM:SS'. Never from hours."""
    days = 0
    m = re.match(r'(\d+) days?, (.+)$', d)
    if m:
        days, d = int(m.group(1)), m.group(2)
    h, mi, s = (int(x) for x in d.split(':'))
    return days * 86400 + h * 3600 + mi * 60 + s


def walk():
    out = subprocess.run([sys.executable, AUDIT, '--spans', 'all'],
                         capture_output=True, text=True, check=True).stdout
    blocks = re.findall(
        r'span of (\d+) broken commit\(s\)\n'
        r'\s*opened after : (\w+).*?\n'
        r'\s*closed by\s*: (\w+).*?\n'
        r'\s*duration\s*: (.+?) \([\d.]+ h\).*?\n'
        r'\s*hole counts\s*:\s*([\d,]+)', out)
    spans = []
    for c, opened, closed, dur, chain in blocks:
        v = [int(x) for x in chain.split(',')]
        spans.append(dict(commits=int(c), opened=opened, closed=closed,
                          dur=dur, secs=secs(dur), chain=v,
                          comps=len(v) - 1,
                          mono=all(v[k + 1] <= v[k] for k in range(len(v) - 1))))
    m = re.search(r'RANKED over the complete history \((\d+) closed spans', out)
    declared = int(m.group(1)) if m else None
    return spans, declared


def ranker(pop, key):
    vals = sorted((key(s) for s in pop), reverse=True)
    return (lambda v: vals.index(v) + 1), (lambda v: vals.count(v) - 1)


def census(note, spans):
    """Check EVERY opening-width census sentence against the walk.

    Two kinds of sentence carry this census, and they are checked
    differently because they mean different things:

      * a CLOSE WRITEUP states the census as it stood at ITS OWN close --
        a permanent record of a past state.  It is still checkable: the
        census "at N closed chains" is the census of the walk's FIRST N
        spans, so every one of them is re-derivable from a prefix today.
      * the LIVE OPEN ENTRY states the census as it stands now, plus
        figures only an open span has ("since the Nth", "last five").

    The first version of this function searched the WHOLE note for one
    sentence and took `re.search`'s first hit -- which is the newest close
    writeup, not the live entry.  It reported eleven figures checked and
    passed a note whose live percentage had been mutated, because the
    sentence it actually read was a different, correct one further up.
    bank.py's own span guard carries the same lesson in its comments: a
    pattern that cannot tell an assertion from an older assertion checks
    the wrong thing and says so confidently.  Hence: all sentences are
    checked, each against its own N, and the live-only figures are read
    ONLY from the text at and after the open marker.

    Positions are carried alongside each span and never recovered with
    list.index(): these are dicts, dicts compare by value, and two spans
    agreeing in every field would hand back the first one's position.
    """
    bad = []
    flat = re.sub(r'\s+', ' ', note)
    ow = [(i + 1 - OFFSET, s['chain'][0]) for i, s in enumerate(spans)]

    def tally_of(k):
        """Opening-width census over the walk's FIRST k closed spans."""
        w = [x for _, x in ow[:k]]
        return {v: w.count(v) for v in sorted(set(w))}

    sentences = re.findall(
        r'Over the \*\*(\d+)\*\* closed chains the opening hole count is '
        r'\*\*(.+?)\*\*, so (\w+) is \*\*([\d.]+)%\*\*', flat)
    checked = 0
    for dn, body, word, pct in sentences:
        k = int(dn)
        checked += 1
        if not 1 <= k <= len(spans):
            bad.append(('census', 'declared N', f'note {k}, walk has {len(spans)}'))
            continue
        want = tally_of(k)
        got = {int(a): int(b) for a, b in re.findall(r'(\d+) in (\d+)', body)}
        checked += 2
        if got != want:
            bad.append((f'census at {k}', 'width tally', f'note {got} vs walk {want}'))
        if sum(got.values()) != k:
            bad.append((f'census at {k}', 'tally total',
                        f'note sums to {sum(got.values())} vs its own N {k}'))
        checked += 1
        w = CARDS.get(word)
        exp = round(100 * want.get(w, 0) / k, 1)
        if w is None or abs(float(pct) - exp) > 0.05:
            bad.append((f'census at {k}', 'percent',
                        f'note {pct}% for "{word}" vs walk {exp}%'))

    live = 0
    if SPAN_OPEN in note:
        # Scoped to the open entry: the archived writeups above it use the
        # same words about different spans.
        lf = re.sub(r'\s+', ' ', note[note.index(SPAN_OPEN):])
        m = re.search(r'first opening at (\w+) since the ([a-z-]+)\*\*', lf)
        if not m:
            bad.append(('live census', '"since the" sentence',
                        'NOT FOUND -- pattern or prose changed'))
        else:
            live += 1
            seen = [o for o, x in ow if x == CARDS.get(m.group(1))]
            want = seen[-1] if seen else None
            if WORDS.get(m.group(2)) != want:
                bad.append(('live census', '"since the"',
                            f'note {m.group(2)} ({WORDS.get(m.group(2))}) vs walk {want}'))
        m = re.search(r'opened at (\w+) are \*\*(\d+)\*\* of the (\d+)', lf)
        if not m:
            bad.append(('live census', '"of the N" sentence',
                        'NOT FOUND -- pattern or prose changed'))
        else:
            live += 2
            seen = [o for o, x in ow if x == CARDS.get(m.group(1))]
            if int(m.group(2)) != len(seen):
                bad.append(('live census', 'width count',
                            f'note {m.group(2)} vs walk {len(seen)}'))
            if int(m.group(3)) != len(spans):
                bad.append(('live census', 'of the N',
                            f'note {m.group(3)} vs walk {len(spans)}'))
            m5 = re.search(r'the last five of them ordinals \*\*([\d, and]+)\*\*', lf)
            if not m5:
                bad.append(('live census', '"last five" sentence',
                            'NOT FOUND -- pattern or prose changed'))
            else:
                live += 1
                said = [int(x) for x in re.findall(r'\d+', m5.group(1))]
                if said != seen[-5:]:
                    bad.append(('live census', 'last five ordinals',
                                f'note {said} vs walk {seen[-5:]}'))
    return len(sentences), checked, live, bad


def mono_prose(note, spans):
    """Check the CURRENT monotonicity prose against the walk.

    The two tables are already covered; this is the prose beside them --
    the True partition, the False-chain column and the rank sentence --
    which is where the stale figure has actually lived.  On record: a
    headline stuck at "31 of 53" for a close, a False-chain list missing
    row 52's 4, and "fifty-one verdicts" stale for three closes.

    FROZEN paragraphs are deliberately out of scope.  The superseded one
    headed "as of ordinal 31" gives its True partition at 31 and its
    False-chain list at 32, and says so itself ("until the thirty-second's
    10 was inserted above it").  Checked against its headline ordinal it
    reads 13 chains where it says 14 -- and the first pass through this
    work took that for an error in the note.  It is not one.  A checker
    keyed to a frozen paragraph's headline fails correct prose and invites
    a "fix" to it, which is worse than not checking it at all.

    Count-words are figures too: "Fourteen of the thirty-four Trues" is
    two numbers spelled out, and both are checked.
    """
    bad, checked = [], 0
    flat = re.sub(r'\s+', ' ', note)
    tbl = {i + 1 - OFFSET: s for i, s in enumerate(spans) if i + 1 - OFFSET >= 1}
    T = {o: s for o, s in tbl.items() if s['mono']}
    F = {o: s for o, s in tbl.items() if not s['mono']}
    def nums(s): return [int(x) for x in re.findall(r'\d+', s)]

    def bullet(name, pat, want_ords):
        nonlocal checked
        m = re.search(pat, flat)
        if not m:
            bad.append(('mono prose', name, 'NOT FOUND -- pattern or prose changed')); return
        checked += 2
        said_n, said = CARDS.get(m.group(1).lower()), nums(m.group(m.lastindex))
        if said_n != len(want_ords):
            bad.append(('mono prose', f'{name} count', f'note {m.group(1)} ({said_n}) vs walk {len(want_ords)}'))
        if said != want_ords:
            bad.append(('mono prose', f'{name} ordinals', f'note {said} vs walk {want_ords}'))
        return m

    m = bullet('zero-comparison Trues',
        r'\*\*([\w-]+) of the ([\w-]+) Trues contain zero comparisons and could not '
        r'have come out False\*\*: ordinals \*\*([\d, ]+)\*\*',
        sorted(o for o, s in T.items() if s['comps'] == 0))
    if m:
        checked += 1
        if CARDS.get(m.group(2).lower()) != len(T):
            bad.append(('mono prose', 'True total', f'note {m.group(2)} vs walk {len(T)}'))
    bullet('one-comparison Trues',
        r'\*\*([\w-]+) more rest on a single comparison\*\*.{0,120}?: \*\*([\d, ]+)\*\*',
        sorted(o for o, s in T.items() if s['comps'] == 1))

    # The standalone headline above the bullets.  It was stale at the
    # fifty-seventh close ("Thirty-four True of fifty-six") and the first
    # version of this function did NOT catch it -- it read the bullets'
    # count-words and not this sentence.  Enumerate the sentences; do not
    # claim "the prose" as a class.
    m = re.search(r'\*\*([\w-]+) True of ([\w-]+)\*\* — and the breakdown', flat)
    if not m:
        bad.append(('mono prose', 'True/total headline', 'NOT FOUND'))
    else:
        checked += 2
        if CARDS.get(m.group(1).lower()) != len(T):
            bad.append(('mono prose', 'headline True', f'note {m.group(1)} vs walk {len(T)}'))
        if CARDS.get(m.group(2).lower()) != len(tbl):
            bad.append(('mono prose', 'headline total', f'note {m.group(2)} vs walk {len(tbl)}'))

    m = re.search(r'\*\*([\w-]+) carry more than one\*\*: (.+?)\.', flat)
    if not m:
        bad.append(('mono prose', 'many-comparison Trues', 'NOT FOUND'))
    else:
        checked += 2
        want = {o: s['comps'] for o, s in T.items() if s['comps'] > 1}
        if CARDS.get(m.group(1).lower()) != len(want):
            bad.append(('mono prose', 'many count', f'note {m.group(1)} vs walk {len(want)}'))
        got = {}
        for grp, word in re.findall(r'((?:\*\*\d+\*\*(?:,| and)? ?)+)with ([a-z]+)', m.group(2)):
            for o in nums(grp):
                got[o] = CARDS.get(word)
        if got != want:
            bad.append(('mono prose', 'many breakdown', f'note {got} vs walk {want}'))

    m = re.search(r'\*\*The ([\w-]+) False chains, by comparison count\*\*: ([\d, \*]+) —', flat)
    if not m:
        bad.append(('mono prose', 'False chain list', 'NOT FOUND'))
    else:
        checked += 2
        want = sorted((s['comps'] for s in F.values()), reverse=True)
        if CARDS.get(m.group(1).lower()) != len(F):
            bad.append(('mono prose', 'False count', f'note {m.group(1)} vs walk {len(F)}'))
        if nums(m.group(2)) != want:
            bad.append(('mono prose', 'False chains', f'note {nums(m.group(2))} vs walk {want}'))

    m = re.search(r'The column holds (.+?) — summing to (\d+)', flat)
    if not m:
        bad.append(('mono prose', 'value tally', 'NOT FOUND'))
    else:
        checked += 2
        want = collections.Counter(s['comps'] for s in F.values())
        got = collections.Counter()
        for cnt, val in re.findall(r'([a-z]+) (\d+)s?\b', m.group(1)):
            if cnt in CARDS: got[int(val)] = CARDS[cnt]
        if got != want:
            bad.append(('mono prose', 'tally', f'note {dict(got)} vs walk {dict(want)}'))
        if int(m.group(2)) != len(F):
            bad.append(('mono prose', 'tally total', f'note {m.group(2)} vs walk {len(F)}'))

    m = re.search(r"\*The ([\w-]+)'s nine is (\d+)(?:st|nd|rd|th), unchanged\.\*", flat)
    if not m:
        bad.append(('mono prose', 'nine-rank sentence', 'NOT FOUND'))
    else:
        checked += 2
        o = WORDS.get(m.group(1))
        if o not in F or F[o]['comps'] != 9:
            bad.append(('mono prose', 'nine row', f'note row {o} vs walk comps '
                        f'{F[o]["comps"] if o in F else "not False"}'))
        else:
            rank = 1 + sum(1 for s in F.values() if s['comps'] > 9)
            if int(m.group(2)) != rank:
                bad.append(('mono prose', 'nine rank', f'note {m.group(2)} vs walk {rank}'))
    return checked, bad


def main(note_path=NOTE):
    spans, declared = walk()
    n = len(spans)
    print(f'walked {n} closed spans; the tool itself declares {declared}')
    if declared is not None and declared != n:
        print(f'!! PARSE DISAGREES WITH THE TOOL: {n} parsed vs {declared} declared')
        return 1
    if n < MIN_SPANS:
        print(f'!! only {n} spans parsed, floor is {MIN_SPANS} -- pattern is broken')
        return 1

    by_sha = {s['closed']: s for s in spans}
    ordinal = {i + 1 - OFFSET: s for i, s in enumerate(spans) if i + 1 - OFFSET >= 1}
    rank_d, _      = ranker(spans, lambda s: s['secs'])
    rank_c, tied_c = ranker(spans, lambda s: s['commits'])

    note = open(note_path).read()
    bad = []

    rows = re.findall(
        r'^\| ([a-z-]+) `(\w+)` \| \*{0,2}([\d:, a-z]+?)\*{0,2} \| \*{0,2}(\d+) of (\d+)\*{0,2} '
        r'\| \*{0,2}(\d+)\*{0,2} \| \*{0,2}(\d+) of (\d+)\*{0,2} \(\*{0,2}(\d+) tied\*{0,2}\) \|$',
        note, re.M)
    print(f'spans-table rows parsed: {len(rows)}')
    if len(rows) < MIN_TABLE_ROWS:
        print(f'!! floor is {MIN_TABLE_ROWS} -- pattern is broken')
        return 1
    # Same contiguity idea on the other table: the rows must be exactly the
    # walk's ordinals from the table's first to the newest close, with no
    # ordinal skipped by a pattern that failed to match its row.
    tbl_shas = {sha for _, sha, *_ in rows}
    tbl_ords = sorted(o for o, sp in ordinal.items() if sp['closed'] in tbl_shas)
    if tbl_ords and tbl_ords != list(range(tbl_ords[0], max(ordinal) + 1)):
        missing = sorted(set(range(tbl_ords[0], max(ordinal) + 1)) - set(tbl_ords))
        print(f'!! spans-table ordinals are not contiguous to the newest close;'
              f' missing {missing}')
        return 1
    for name, sha, dur, rd, nd, com, rc, nc, tie in rows:
        s = by_sha.get(sha)
        if s is None:
            bad.append((name, 'sha not in walk', sha)); continue
        for label, got, want in (('duration', s['dur'], dur),
                                 ('dur N', n, int(nd)),
                                 ('dur rank', rank_d(s['secs']), int(rd)),
                                 ('commits', s['commits'], int(com)),
                                 ('com N', n, int(nc)),
                                 ('com rank', rank_c(s['commits']), int(rc)),
                                 ('tied', tied_c(s['commits']), int(tie))):
            if got != want:
                bad.append((f'{name} `{sha}`', label, f'note {want} vs walk {got}'))

    mono = re.findall(r'^\| (\d+) \| `(\w+)` \| ([\d,…]+) \| \*{0,2}(\d+)\*{0,2} \| \*{0,2}(True|False)',
                      note, re.M)
    print(f'monotonicity rows parsed: {len(mono)}')
    if len(mono) < MIN_MONO_ROWS:
        print(f'!! floor is {MIN_MONO_ROWS} -- pattern is broken')
        return 1
    # Contiguity is a far stronger check than a floor: a pattern that misses
    # one row leaves a gap, and a gap fails here.  This caught the very first
    # run of this tool, where row 22's bolded **True** did not match.
    nums = sorted(int(m[0]) for m in mono)
    gaps = sorted(set(range(1, max(nums) + 1)) - set(nums))
    if gaps:
        print(f'!! monotonicity ordinals are not contiguous; missing {gaps}'
              f' -- the pattern missed a row, it is not that the row is absent')
        return 1
    for num, sha, chain, comps, verdict in mono:
        s = ordinal.get(int(num))
        if s is None:
            bad.append((f'row {num}', 'ordinal not in walk', sha)); continue
        if s['closed'] != sha:
            bad.append((f'row {num}', 'sha', f'note {sha} vs walk {s["closed"]}')); continue
        if '…' not in chain and chain != ','.join(map(str, s['chain'])):
            bad.append((f'row {num}', 'chain', f'note {chain} vs walk {s["chain"]}'))
        if int(comps) != s['comps']:
            bad.append((f'row {num}', 'comparisons', f'note {comps} vs walk {s["comps"]}'))
        if (verdict == 'True') != s['mono']:
            bad.append((f'row {num}', 'monotone', f'note {verdict} vs walk {s["mono"]}'))

    nsent, cchecked, live, cbad = census(note, spans)
    bad += cbad
    print(f'census sentences parsed: {nsent} ({cchecked} figures);'
          f' live-span figures: {live}')
    if nsent < MIN_CENSUS_SENTENCES:
        print(f'!! only {nsent} census sentences parsed, floor is'
              f' {MIN_CENSUS_SENTENCES} -- the pattern is broken, it is not'
              f' that the note is clean')
        return 1
    if SPAN_OPEN in note and live < MIN_CENSUS_LIVE:
        print(f'!! a span is open but only {live} live-census figures parsed,'
              f' floor is {MIN_CENSUS_LIVE}')
        return 1

    mchecked, mbad = mono_prose(note, spans)
    bad += mbad
    print(f'monotonicity-prose figures parsed: {mchecked}')
    if mchecked < MIN_MONO_PROSE:
        print(f'!! only {mchecked} monotonicity-prose figures parsed, floor is'
              f' {MIN_MONO_PROSE} -- the pattern is broken, it is not that the'
              f' note is clean')
        return 1

    checked = len(rows) * 7 + len(mono) * 4 + cchecked + live + mchecked
    print(f'figures checked: {checked}')
    if bad:
        print(f'\n!! {len(bad)} MISMATCH(ES):')
        for b in bad:
            print('   ', b)
        return 1
    print('every parsed span figure agrees with `--spans all`.')
    return 0


if __name__ == '__main__':
    # An optional path lets the tool be pointed at a MUTATED COPY of the note,
    # which is how it is proved to fail: a checker that has never failed is not
    # known to work.
    sys.exit(main(sys.argv[1] if len(sys.argv) > 1 else NOTE))
