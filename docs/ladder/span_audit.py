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
MIN_TABLE_ROWS = 40
MIN_MONO_ROWS  = 54


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

    checked = len(rows) * 7 + len(mono) * 4
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
