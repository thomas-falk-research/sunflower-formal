#!/bin/bash
# Build isearch, emit the depth-6 frontier, and run all of it, resumably.
#   tools/iota4/run.sh <nauty-source-dir> <work-dir> [jobs]
# A chunk of 40 shards is done when its log ends with a DONE line; rerunning
# the script skips done chunks. Then: python3 tools/iota4/audit.py <work-dir>/logs <work-dir>/d6.txt
set -euo pipefail
N=$1; W=$2; J=${3:-4}; SRC=$(cd "$(dirname "$0")" && pwd)
mkdir -p "$W/logs"; cd "$W"
[ -x isearch ] || gcc -O3 -march=native -I "$N" -o isearch "$SRC/isearch.c" \
  "$N/nauty.c" "$N/nautil.c" "$N/naugraph.c" "$N/schreier.c" "$N/naurng.c"
[ -f d6.txt ] || ./isearch -k 4 -m 28 -I -e 6 -o d6.txt > emit.log || true
seq 0 40 11719 | xargs -P "$J" -I{} bash -c '
  f=logs/chunk_$(printf %05d {}).log
  if [ -f $f ] && grep -q "^DONE" $f; then exit 0; fi
  ./isearch -r d6.txt -l {} -n 40 > $f.tmp; code=$?
  echo "DONE exit=$code" >> $f.tmp; mv $f.tmp $f'
echo ALLDONE
