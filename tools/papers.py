#!/usr/bin/env python3
"""Regenerate docs/papers/{MANIFEST.md,ATTRIBUTION.md,fetch.sh,sunflower.bib}
from docs/papers/manifest.json.

manifest.json is the single source of truth for the paper corpus. Every
other file in docs/papers/ is generated from it, so a record can never
drift out of step with its attribution or its fetch line.

Run after editing manifest.json:

    python3 tools/papers.py

The `redistributable` flag decides whether a PDF may live under
docs/papers/pdf/. It is set from the licence the publisher states; this
script only reads it, never sets it.
"""
import json, os, re

DST = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "docs", "papers")
R=json.load(open(os.path.join(DST,"manifest.json")))
def lic_short(l):
    if not l: return "unstated"
    if "by-sa/4.0" in l: return "CC BY-SA 4.0"
    if "by/4.0" in l: return "CC BY 4.0"
    if "nonexclusive-distrib" in l: return "arXiv non-exclusive"
    return l
def auth(r):
    a=r["authors"]
    if len(a)<=3: return ", ".join(a)
    return a[0]+" et al."

# ---------- MANIFEST.md ----------
rows=[]
for r in R:
    loc = f"`pdf/{r['file']}`" if r["redistributable"] else "not stored"
    ident = r["arxiv"] and f"arXiv:{r['arxiv']}" or (r["doi"] and f"doi:{r['doi']}" or "—")
    rows.append(f"| `{r['key']}` | {auth(r)} | {r['title']} | {ident} | {r['pages']} | {lic_short(r['license'])} | {loc} | {r['read']} |")
md = """# Paper archive

The corpus behind `docs/reading.md`, pinned so no future session has to
re-find it.

Every row records the **exact bytes that were read**: a SHA-256 over the
PDF as downloaded, its page count, the URL it came from, and the date it
was retrieved. `fetch.sh` rebuilds the corpus from those records and
fails loudly if a byte has changed — a paper that is silently revised
upstream will not pass unnoticed.

## Why some PDFs are here and most are not

`manifest.json` has a `redistributable` flag, set from the licence the
publisher actually states, not from convenience:

* **CC BY 4.0 / CC BY-SA 4.0** — redistributable with attribution. Stored
  in `pdf/`, unmodified, attributed in `ATTRIBUTION.md`.
* **BSD** (the AFP entry) — same.
* **arXiv non-exclusive distribution licence** — grants arXiv the right to
  distribute, **not** third parties. Not stored. `fetch.sh` gets it.
* **In copyright** (the 1960/1961/1969 journal scans, the PCMI notes) —
  not stored. `fetch.sh` gets it from the source that made it public.

Storing a paper we have no licence to store would be the same class of
error this reading session exists to correct, so the flag is derived
mechanically and the fetch script covers the gap.

## Rebuilding the corpus

```
  cd docs/papers && ./fetch.sh          # download all 29, verify SHA-256
  cd docs/papers && ./fetch.sh --render # also render every page to PNG
```

`fetch.sh` skips anything already present in `pdf/`, so it only reaches
the network for what is not stored.

## The corpus

`read` states how much of each was actually read, per the evidence classes
in `docs/reading.md`. "not read" means downloaded and rendered and no
more; it is not a claim about the contents.

| key | authors | title | id | pp | licence | stored | read |
|---|---|---|---|---|---|---|---|
""" + "\n".join(rows) + f"""

{len(R)} records, {sum(1 for r in R if r['redistributable'])} PDFs stored,
{sum(1 for r in R if r['read'].startswith('read in full'))} read in full.

## What bears on what

| key | bears on this repository |
|---|---|
""" + "\n".join(f"| `{r['key']}` | {r['bears_on']} |" for r in R) + """

## Provenance rules

1. A record is added only after the PDF has been downloaded and its page
   count verified with `pdfinfo`. No record is created from a search
   result.
2. `sha256` is over the bytes that were rendered and read. If a later
   session re-fetches and the hash differs, the paper was revised —
   re-read before relying on any quotation.
3. `read` is updated only by a session that actually rendered the pages.
4. Nothing is stored under `pdf/` whose licence does not permit it.
"""
open(os.path.join(DST,"MANIFEST.md"),"w").write(md)

# ---------- ATTRIBUTION.md ----------
att = """# Attribution for the stored PDFs

The files in `pdf/` are redistributed here **unmodified**, under the
licences their authors chose. Each entry gives the attribution that
licence requires: author, title, source, licence, and the fact that the
work is unchanged.

Nothing in this directory is authored by this repository. The reading of
these papers — `docs/reading.md` — is; the papers are not.

"""
for r in R:
    if not r["redistributable"]: continue
    src = r["arxiv"] and f"https://arxiv.org/abs/{r['arxiv']}" or r["url"]
    att += f"""### `pdf/{r['file']}`

* **Title:** {r['title']}
* **Authors:** {", ".join(r['authors'])}
* **Source:** {src}
* **Licence:** {lic_short(r['license'])} — <{r['license'] if r['license'].startswith('http') else 'https://opensource.org/license/bsd-3-clause'}>
* **Changes:** none; redistributed as retrieved on {r['retrieved']}
* **SHA-256:** `{r['sha256']}`

"""
open(os.path.join(DST,"ATTRIBUTION.md"),"w").write(att)

# ---------- fetch.sh ----------
lines=["#!/bin/sh",
"# Rebuild the paper corpus from docs/papers/manifest.json and verify every",
"# byte against the SHA-256 recorded when it was read. Generated file: edit",
"# manifest.json and re-run tools/papers.py, not this script.",
"set -eu",
'cd "$(dirname "$0")"',
'RENDER=""',
'if [ "${1:-}" = "--render" ]; then RENDER=1; fi   # not && : set -e would exit',
'mkdir -p pdf',
'fail=0',
'get() { # key url file sha256',
'  if [ -f "pdf/$3" ]; then',
'    have=$(sha256sum "pdf/$3" | cut -d" " -f1)',
'    if [ "$have" = "$4" ]; then echo "ok       $1"; else echo "MISMATCH $1  (upstream changed; re-read before quoting)"; fail=1; fi',
'    return 0',
'  fi',
'  echo "fetch    $1  <- $2"',
'  if curl -sS -L --max-time 180 -A "sunflower-formal/1.0" -o "pdf/$3" "$2"; then',
'    have=$(sha256sum "pdf/$3" | cut -d" " -f1)',
'    if [ "$have" != "$4" ]; then echo "MISMATCH $1  expected $4 got $have"; fail=1; fi',
'  else echo "FAILED   $1"; fail=1; fi',
'}',
]
for r in R:
    lines.append(f'get "{r["key"]}" "{r["url"]}" "{r["file"]}" "{r["sha256"]}"')
lines += [
'if [ -n "$RENDER" ]; then',
'  for f in pdf/*.pdf; do d="render/$(basename "$f" .pdf)"; mkdir -p "$d"; pdftoppm -png -r 150 "$f" "$d/p"; done',
'  echo "rendered to render/"',
'fi',
'[ "$fail" = 0 ] && echo "all records verified" || { echo "SOME RECORDS FAILED"; exit 1; }',
]
p=os.path.join(DST,"fetch.sh"); open(p,"w").write("\n".join(lines)+"\n"); os.chmod(p,0o755)

# ---------- BibTeX ----------
bib=["% Generated from docs/papers/manifest.json by tools/papers.py. Do not edit by hand.",
     "% Every entry here corresponds to a PDF that was downloaded and page-counted;",
     "% see docs/papers/MANIFEST.md for how much of each was read.",""]
for r in R:
    fields=[f"  author       = {{{' and '.join(r['authors'])}}}",
            f"  title        = {{{r['title']}}}"]
    if r["journal_ref"]: fields.append(f"  note         = {{{r['journal_ref']}}}")
    # Two separate fields, so the join below puts a comma between them. They
    # used to be one string with a bare newline, which left every arXiv entry
    # missing its comma and the whole .bib unparseable.
    if r["arxiv"]:
        fields.append(f"  eprint       = {{{r['arxiv']}}}")
        fields.append(f"  archiveprefix= {{arXiv}}")
    if r["doi"]: fields.append(f"  doi          = {{{r['doi']}}}")
    fields.append(f"  urldate      = {{{r['retrieved']}}}")
    fields.append(f"  pagetotal    = {{{r['pages']}}}")
    yr = (r["published"] or (re.search(r'(19|20)\d\d', r["journal_ref"] or "") or [None])[0] or "")
    if r["published"]: fields.append(f"  year         = {{{r['published'][:4]}}}")
    bib.append("@misc{"+r["key"]+",\n"+",\n".join(fields)+"\n}")
open(os.path.join(DST,"sunflower.bib"),"w").write("\n\n".join(bib)+"\n")
# ---------- pdf/.gitignore ----------
# fetch.sh downloads every paper into pdf/, including the ones we have no
# licence to store. This whitelist is what keeps those out of the commit.
gi = ["# Generated by tools/papers.py. Do not edit.",
      "#",
      "# fetch.sh downloads all " + str(len(R)) + " papers here. Only the ones whose licence",
      "# permits redistribution are tracked; everything else is ignored, so a",
      "# rebuilt corpus never turns into a copyright problem in a commit.",
      "*", "!.gitignore"]
for r in sorted(R, key=lambda x: x["file"]):
    if r["redistributable"]:
        gi.append("!" + r["file"])
open(os.path.join(DST, "pdf", ".gitignore"), "w").write("\n".join(gi) + "\n")
open(os.path.join(DST, ".gitignore"), "w").write("# Generated by tools/papers.py. Do not edit.\nrender/\n")
print("wrote MANIFEST.md ATTRIBUTION.md fetch.sh sunflower.bib pdf/.gitignore")
