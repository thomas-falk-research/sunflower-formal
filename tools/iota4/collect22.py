#!/usr/bin/env python3
"""Collect the link classes of size 22 from the size-22 shard reruns.

  collect22.py LEDGER_LOG_DIR SHARD_LOG_DIR CANON_BIN OUT.txt.gz

Every shard log must end with DONE exit=20, reproduce its ledger record
(the ACCEPTED vector) exactly, and the BIG lines of size 22 are kept;
duplicates up to isomorphism (nauty canonical form of the incidence
graph, CANON_BIN) are reported and must be absent.
"""
import sys, os, re, glob, gzip, subprocess, hashlib

ledger_dir, shard_dir, canon, out = sys.argv[1:5]
ledger = {}
for f in sorted(glob.glob(os.path.join(ledger_dir, "chunk_*.log"))):
    lines = open(f).read().split("\n")
    for i, l in enumerate(lines):
        if l.startswith("SHARD"):
            ledger[int(l.split()[1])] = lines[i + 1].strip()
shards = [int(x) for x in open(os.path.join(shard_dir, "..", "shards22.txt")).read().split()]
big = []
ok = 0
for s in shards:
    f = os.path.join(shard_dir, f"s_{s}.log")
    if not os.path.exists(f):
        print("MISSING", s); continue
    lines = open(f).read().split("\n")
    if not any(l.startswith("DONE exit=20") for l in lines):
        print("NOT DONE", s); continue
    acc = [l.strip() for l in lines if l.startswith("ACCEPTED")]
    if len(acc) != 1 or acc[0] != ledger[s]:
        print("LEDGER MISMATCH", s); continue
    ok += 1
    for l in lines:
        if l.startswith("BIG "):
            r = int(l.split()[1])
            if r == 22:
                big.append(f"{s} {l}")
print("shards ok", ok, "of", len(shards), "size-22 families", len(big))
res = subprocess.run([canon], input="\n".join(big) + "\n", capture_output=True, text=True, check=True)
forms = res.stdout.split("\n")[:len(big)]
assert len(forms) == len(big) and all(forms)
seen = {}
dups = 0
for b, c in zip(big, forms):
    if c in seen:
        dups += 1
    seen.setdefault(c, b)
print("distinct canonical forms", len(seen), "duplicates", dups)
with gzip.open(out, "wt") as fh:
    fh.write("\n".join(big) + "\n")
h = hashlib.sha256(("\n".join(big) + "\n").encode()).hexdigest()
print("wrote", out, "sha256 of uncompressed", h)
