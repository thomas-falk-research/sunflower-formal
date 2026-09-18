"""Stage the checkpoint, read every figure from the STAGED blob, refresh the
note's state lines from those figures, and print what a commit message may
say.  Nothing here is recalled: the counts come from the staged index in the
same run that rewrites the note, which is the fix for e5c0c73.

The open-block census is rewritten here too, guarded: if the note's census
line does not match what SEQ says about the one open block, this REFUSES to
touch it and says so loudly, rather than writing a figure it cannot justify."""
import subprocess, re, statistics
from collections import OrderedDict
exec(open('docs/ladder/forward_test.py').read()
     .split("# ------------------------------------------------------------------ calibration")[0])

subprocess.run(['git','add','docs/ladder/iota4_11.deg13.cryptominisat5.tsv'],check=True)
def rows_of(spec):
    txt=subprocess.run(['git','show',spec],capture_output=True,text=True).stdout
    return [l for l in txt.splitlines() if l and not l.startswith('#')]
CK='docs/ladder/iota4_11.deg13.cryptominisat5.tsv'
head=rows_of(f'HEAD:{CK}'); stg=rows_of(f':{CK}')
dec={}
for l in stg:
    q=l.split('\t')
    if q[1]!='UNKNOWN': dec[IDX[q[0]]]=max(dec.get(IDX[q[0]],0.0), float(q[2]))
n=len(dec); pct=100.0*n/1949
costs=sorted(dec.values(), reverse=True)
idxs=sorted(dec)
top=-1
for i in range(1949):
    if i in dec: top=i
    else: break
holes=[i for i in range(top+1, max(idxs)+1) if i not in dec]
blocks=OrderedDict()
for j,s in enumerate(SEQ): blocks.setdefault(tuple(s[:4]),[]).append(j)
openb=[(k,[x for x in v if x in dec],v) for k,v in blocks.items()
       if any(x in dec for x in v) and not all(x in dec for x in v)]

print(f"HEAD {len(head)} -> staged {len(stg)}: {len(stg)-len(head)} new row(s)")
for l in stg[len(head):]:
    p=l.split('\t'); i=IDX[p[0]]
    print(f"  idx {i}  {p[1]}  {p[2]} s  ({float(p[2])/21600:.4f} of cap)  "
          f"rank {costs.index(dec[i])+1} of {n}; cheaper {sum(1 for c in costs if c<dec[i])}"
          f"   {p[0]}")
print(f"decided {n} = {pct:.4f}%; undecided {1949-n}")
print(f"frontier contiguous 0..{top}; highest decided {max(idxs)}; holes {holes}")
for k,d,v in openb:
    print(f"open block {k}: {len(d)} of {len(v)}, undecided {[x for x in v if x not in dec]}")
if not openb: print("NO open block")

now=subprocess.run(['date','-u','+%Y-%m-%dT%H:%MZ'],capture_output=True,text=True).stdout.strip()
p='docs/ladder/deg13_sweep_note.md'
t=open(p).read()
m=re.search(r'\*\*Status: [^*]+\.\*\*', t)
t=t[:m.start()]+f"**Status: {now}.**"+t[m.end():]
if len(stg) > len(head):
    t=re.sub(r"## State as of the last refresh \(\d+ -> \d+ rows\)",
             f"## State as of the last refresh ({len(head)} -> {len(stg)} rows)", t, count=1)
else:
    # no new rows: the heading records the last refresh THAT BANKED SOMETHING,
    # and rewriting it to "N -> N rows" would erase that with a tautology.
    print("refresh heading left alone: 0 new rows this run")
t=re.sub(r"- \*\*\d+ rows; \d+ labels decided; \d+ UNSAT; 0 SAT",
         f"- **{len(stg)} rows; {n} labels decided; {n} UNSAT; 0 SAT", t, count=1)
t=re.sub(r"count is not a decision count: \d+ decided plus",
         f"count is not a decision count: {n} decided plus", t, count=1)
t=re.sub(r"- \*\*\d+ of 1949 = \d+\.\d+%\*\*; \*\*\d+ undecided\*\*",
         f"- **{n} of 1949 = {pct:.4f}%**; **{1949-n} undecided**", t, count=1)
t=re.sub(r"- \*\*Frontier contiguous 0\.\.\d+, highest decided \d+, holes[^*]*\*\*",
         f"- **Frontier contiguous 0..{top}, highest decided {max(idxs)}, "
         f"holes {holes}.**", t, count=1)

# ---- open-block census, mechanical: regenerate the whole delimited region ----
# The old version rewrote a single prose sentence and assumed exactly ONE open
# block, so it refused (correctly) the moment a second opened.  The region form
# has no such assumption: bank.py owns everything between the markers.
BEG="<!-- OPEN-BLOCK-CENSUS: rewritten by docs/ladder/bank.py; do not hand-edit -->"
END="<!-- /OPEN-BLOCK-CENSUS -->"
if t.count(BEG)!=1 or t.count(END)!=1 or t.index(END)<t.index(BEG):
    print("!! CENSUS NOT REWRITTEN: the delimited region is missing or malformed. "
          "Restore the two markers; do not type the numbers.")
else:
    lines=[]
    if not openb:
        lines.append("*No block is open: every block with any decided member is complete.*")
    for k,d,v in openb:
        und=[x for x in v if x not in dec]
        # keep the rendered line under 90 chars: list the undecided only while
        # they are few, otherwise give the count and the span they occupy
        shown=str(und) if len(und)<=5 else f"{len(und)} spanning {min(und)}..{max(und)}"
        lines.append(f"- `{list(k)}` idx {min(v)}..{max(v)}: **{len(v)} members**,\n"
                     f"  **{len(d)} decided**, undecided {shown}")
    body="\n".join(lines)
    t = t[:t.index(BEG)+len(BEG)] + "\n\n" + body + "\n\n" + t[t.index(END):]
    print(f"census region rewritten: {len(openb)} open block(s)")

# ---- span/hole consistency guard ------------------------------------------
# The staged diff at idx 952 caught the Frontier line saying "holes [950, 951]"
# with "No span is open" in the very next sentence.  bank.py owns the first
# sentence and not the prose after it, so it could rewrite one and leave the
# other contradicting it.  It cannot write that prose -- a span's figures come
# from `--spans all` after the span closes -- but it CAN refuse to be silent.
says_none = "No span is open" in t
says_open = "A SPAN IS OPEN" in t
if holes and says_none:
    print(f"!! SPAN PROSE CONTRADICTS THE FRONTIER: holes {holes} but the note "
          f"still says 'No span is open'. A SPAN HAS OPENED. Fix the prose; do "
          f"not claim figures for it until it closes.")
elif not holes and says_open:
    print("!! SPAN PROSE CONTRADICTS THE FRONTIER: holes [] but the note still "
          "says 'A SPAN IS OPEN'. The span has CLOSED -- read its figures from "
          "`--spans all` AFTER this commit exists, and recompute every quoted "
          "span rank against the new N together.")
elif holes and says_open:
    print(f"span guard: holes {holes}, note says a span is open -- consistent. "
          f"No figures are claimed here; they come from `--spans all` on close.")
else:
    print("span guard: holes [], note says no span is open -- consistent.")

# ---- driver line, mechanical -----------------------------------------------
# This line was left stale across three commits after restart #40 and was found
# only by reading the staged diff.  The pid is not in the checkpoint, but it IS
# readable from the live process, so bank.py reads it rather than trusting the
# note.  If the driver is not running, or more than one is, it REFUSES.
import os, datetime
pg=subprocess.run(['pgrep','-x','iota_sym'],capture_output=True,text=True).stdout.split()
dm=re.search(r"- \*\*Driver is pid (\d+)\*\*, launched (\S+) \(read from\n  `/proc/\d+/stat` field 22\)", t)
if dm is None:
    print("!! DRIVER LINE NOT FOUND in the expected form; not rewritten.")
elif len(pg)!=1:
    print(f"!! DRIVER LINE NOT REWRITTEN: pgrep -x iota_sym returned {len(pg)} pid(s) "
          f"{pg}. The note still says pid {dm.group(1)}. Check it by hand.")
else:
    pid=pg[0]
    if pid==dm.group(1):
        print(f"driver line: pid {pid} matches the live process -- unchanged.")
    else:
        bt=[int(l.split()[1]) for l in open('/proc/stat') if l.startswith('btime ')][0]
        st=open(f'/proc/{pid}/stat').read()
        start=int(st[st.rindex(')')+2:].split()[19])/os.sysconf('SC_CLK_TCK')
        iso=datetime.datetime.fromtimestamp(bt+start, datetime.timezone.utc)\
              .isoformat().replace('+00:00','Z')
        t = t[:dm.start()] + (f"- **Driver is pid {pid}**, launched {iso} (read from\n"
                              f"  `/proc/{pid}/stat` field 22)") + t[dm.end():]
        print(f"driver line REWRITTEN from the live process: pid {dm.group(1)} -> {pid}, "
              f"launch {iso}")

open(p,'w').write(t)
subprocess.run(['git','add',p],check=True)
print(f"note state lines rewritten from the staged index; status {now}")
