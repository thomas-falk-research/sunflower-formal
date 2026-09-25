#!/usr/bin/env python3
"""Refigure the spans table for a close.  PARAMETERISED, not copied.

Two earlier closes were refigured by sed-patching the previous close's script;
one of those left a bare old N in an expected-value tuple and reported 39
spurious mismatches.  The remedy taken then was "write it fresh each time",
which trades one failure mode for another -- a fresh script is unchecked.
This one takes the spans file and the closing sha as ARGUMENTS and derives
every N from the walk, so it can be re-run rather than re-typed.

    python3 refig.py <spans-file> <closing-sha7> <ordinal-word>
"""
import re, sys, os
from collections import Counter
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import safe_stdout  # noqa: F401  -- a closed stdout must not skip side effects

SPANS, NEW_SHA, ORDINAL = sys.argv[1], sys.argv[2], sys.argv[3]
txt = open(SPANS).read()
blocks = re.findall(
    r"span of (\d+) broken commit\(s\)\n\s+opened after : (\S+)\s+(\S+)\n\s+closed by    : (\S+)\s+(\S+)\n"
    r"\s+duration     : ((?:\d+ days?, )?\d+:\d+:\d+) \(([\d.]+) h\)[^\n]*\n\s+hole counts  : ([\d,]+)\n"
    r"\s+monotone non-increasing\? (True|False)", txt)
declared = int(re.search(r"RANKED over the complete history \((\d+) closed spans", txt).group(1))
assert len(blocks) == declared, f"PARSE {len(blocks)} vs DECLARED {declared}"
print(f"walk: {len(blocks)} parsed, {declared} declared -- agree")

def secs(d):
    m = re.match(r"(?:(\d+) days?, )?(\d+):(\d+):(\d+)$", d)
    return int(m.group(1) or 0)*86400 + int(m.group(2))*3600 + int(m.group(3))*60 + int(m.group(4))

ALL = [dict(nc=int(a), closed=d, dur=f, secs=secs(f),
            chain=[int(x) for x in h.split(',')], mono=(i == 'True'))
       for a, b, c, d, e, f, g, h, i in blocks]
OLD = [r for r in ALL if not r['closed'].startswith(NEW_SHA)]
N_NEW, N_OLD = len(ALL), len(OLD)
assert N_NEW == N_OLD + 1, (N_NEW, N_OLD)
assert sum(1 for r in ALL if r['closed'].startswith(NEW_SHA)) == 1, "sha not unique in the walk"
print(f"N_OLD={N_OLD}  N_NEW={N_NEW}   (both derived from the walk, neither typed)")

def rk(pop, r):
    return (sum(1 for x in pop if x['secs'] > r['secs']) + 1, r['nc'],
            sum(1 for x in pop if x['nc'] > r['nc']) + 1,
            sum(1 for x in pop if x['nc'] == r['nc']) - 1)

NOTE = open('docs/ladder/deg13_sweep_note.md').read()
LINE = re.compile(r'^\| (?P<name>[a-z-]+) `(?P<sha>\w+)` \| (?P<b1>\*{0,2})(?P<dur>[\d:, a-z]+?)(?P=b1) '
                  r'\| (?P<b2>\*{0,2})(?P<rd>\d+) of (?P<nd>\d+)(?P=b2) '
                  r'\| (?P<b3>\*{0,2})(?P<com>\d+)(?P=b3) '
                  r'\| (?P<b4>\*{0,2})(?P<rc>\d+) of (?P<nc>\d+)(?P=b4) '
                  r'\((?P<b5>\*{0,2})(?P<tie>\d+) tied(?P=b5)\) \|$')
rows = [m.groupdict() for m in (LINE.match(l) for l in NOTE.split('\n')) if m]
print(f"spans-table rows parsed: {len(rows)}")
assert len(rows) == N_OLD - 79, f"table has {len(rows)} rows; the walk implies {N_OLD-79}"

bysha = {r['closed'][:7]: r for r in ALL}
mis = d = c = tc = untouched = 0
out = []
for g in rows:
    r = bysha[g['sha']]; o = rk(OLD, r); n = rk(ALL, r)
    got = (r['dur'], int(g['rd']), int(g['nd']), int(g['com']), int(g['rc']), int(g['nc']), int(g['tie']))
    want = (r['dur'], o[0], N_OLD, o[1], o[2], N_OLD, o[3])
    if got != want:
        mis += 1; print(f"  !! OLD-N MISMATCH {g['name']} {g['sha']}: note {got} vs walk-at-{N_OLD} {want}")
    dd, cc, tt = o[0] != n[0], o[2] != n[2], o[3] != n[3]
    d += dd; c += cc; tc += tt; untouched += not (dd or cc or tt)
    out.append(f"| {g['name']} `{g['sha']}` | {g['b1']}{r['dur']}{g['b1']} "
               f"| {g['b2']}{n[0]} of {N_NEW}{g['b2']} | {g['b3']}{r['nc']}{g['b3']} "
               f"| {g['b4']}{n[2]} of {N_NEW}{g['b4']} ({g['b5']}{n[3]} tied{g['b5']}) |")
print(f"REPRODUCED AT THE OLD N={N_OLD}: {len(rows)-mis} of {len(rows)}, {mis} mismatch(es)")
print(f"AT THE NEW N={N_NEW}: {d} duration + {c} commit + {tc} tie = {d+c+tc} figures move; "
      f"{untouched} of {len(rows)} untouched")
m = bysha[NEW_SHA]; f = rk(ALL, m)
newrow = (f"| {ORDINAL} `{NEW_SHA}` | {m['dur']} | {f[0]} of {N_NEW} | {m['nc']} "
          f"| {f[2]} of {N_NEW} ({f[3]} tied) |")
out.append(newrow)
print(f"\nNEW SPANS ROW: {newrow}")
print(f"NEW MONO ROW:  | {N_NEW-65} | `{NEW_SHA}` | {','.join(map(str,m['chain']))} "
      f"| {len(m['chain'])-1} | {m['mono']} |")
shorter = {g['sha'] for g in rows if bysha[g['sha']]['secs'] < m['secs']}
fewer   = {g['sha'] for g in rows if bysha[g['sha']]['nc'] < m['nc']}
equal   = {g['sha'] for g in rows if bysha[g['sha']]['nc'] == m['nc']}
dm = {g['sha'] for g in rows if rk(OLD, bysha[g['sha']])[0] != rk(ALL, bysha[g['sha']])[0]}
cm = {g['sha'] for g in rows if rk(OLD, bysha[g['sha']])[2] != rk(ALL, bysha[g['sha']])[2]}
tm = {g['sha'] for g in rows if rk(OLD, bysha[g['sha']])[3] != rk(ALL, bysha[g['sha']])[3]}
print(f"SET EQUALITIES: duration {dm==shorter} ({len(dm)}/{len(shorter)}); "
      f"commits {cm==fewer} ({len(cm)}/{len(fewer)}); ties {tm==equal} ({len(tm)}/{len(equal)})")
print(f"  commit-count histogram of the carried rows: "
      f"{dict(sorted(Counter(bysha[g['sha']]['nc'] for g in rows).items()))}")
print(f"\nGLOBALS at {N_NEW}: monotone True {sum(1 for r in ALL if r['mono'])}, "
      f"False {sum(1 for r in ALL if not r['mono'])}")
ge5 = [r for r in ALL if len(r['chain'])-1 >= 5]
print(f"  >=5 comparisons: {len(ge5)}, monotone {sum(1 for r in ge5 if r['mono'])} = "
      f"{100.0*sum(1 for r in ge5 if r['mono'])/len(ge5):.1f}%")
cc2 = Counter(r['chain'][0] for r in ALL)
print(f"  opening widths {dict(sorted(cc2.items()))}; 1 is {100.0*cc2[1]/N_NEW:.1f}%")
last = [r for r in ALL if r['secs'] > 1]
print(f"  longer than a second {len(last)} of {N_NEW}; shorter than this span among them "
      f"{sum(1 for r in last if r['secs'] < m['secs'])}")
for lab, thr in (("1 minute", 60), ("10 minutes", 600), ("1 hour", 3600), ("4 hours", 14400)):
    print(f"  longer than {lab}: {sum(1 for r in ALL if r['secs']>thr)} of {N_NEW}  "
          f"(this span {'is' if m['secs']>thr else 'is NOT'})")
print(f"  single-entry chains: {sum(1 for r in ALL if len(r['chain'])==1)}, "
      f"all True: {all(r['mono'] for r in ALL if len(r['chain'])==1)}")
# The one thing here that is NOT derived from the walk: the historical
# movement figures, which exist only in the note.  Guarded so a stale list
# fails loudly instead of printing a wrong total -- the series must hold one
# entry per close, and the closes start at walk position 89.
series = [1,5,8,14,20,5,17,19,33,19,5,21,15,10,38,14,35,42,50,16,36,32,8,56,23,39,50,29,33,11,18,41,17,46,35,63,38,43,45,71,74,36,24,70,79,19,26,105,52,62,100,57,51,82,55,82,17,49,65,31,127,51,41,102,36,133,60,88,103,60,78,88,137,46,100,112,28,86,128,46,60,75]
assert len(series) == N_OLD - 88, (
    f"movement series has {len(series)} entries; the walk implies {N_OLD-88}. "
    f"Append the previous close's figure before re-running.")
print(f"\nMOVEMENT SERIES: {len(series)} entries summing to {sum(series)}")
new = series + [d+c+tc]
print(f"  with {d+c+tc}: {len(new)} entries summing to {sum(new)}; top five {sorted(new,reverse=True)[:5]}")
print(f"  {d+c+tc} ranks {1+sum(1 for x in new if x>d+c+tc)} of {len(new)}, "
      f"tied with {sum(1 for x in new if x==d+c+tc)-1}")
open(SPANS.rsplit('/',1)[0] + '/table_new.txt', 'w').write('\n'.join(out) + '\n')
print(f"\nwrote {len(out)} table rows")
