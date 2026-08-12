#!/bin/sh
# One batch of deg(0) cubes for a single rung of the iota ladder, run as
# separate single-threaded processes so a container restart loses at most
# the batch in flight. Verdicts append to the checkpoint; already-decided
# cubes are skipped.
#
#   tools/rung.sh <b> <ground> <target> <budget-seconds> <deg>...
#
# See docs/roadmap.md §36 for why the rung is run this way.
set -e
B=$1; G=$2; T=$3; BUDGET=$4; shift 4
CK="docs/ladder/iota${B}_${G}.tsv"
BIN=rust/target/release/examples/iota_sym
for D in "$@"; do
  if awk -F'\t' -v d="$D" '$1==d {found=1} END {exit !found}' "$CK" 2>/dev/null; then
    echo "skip deg0=$D (already decided)"; continue
  fi
  ( OUT=$("$BIN" "$B" "$G" "$T" --ladder --from "$G" --only-deg "$D" \
            --threads 1 --slice "$BUDGET" 2>&1 || true)
    LINE=$(printf '%s\n' "$OUT" | grep -E "deg\(0\)=$D " | tail -1)
    V=$(printf '%s' "$LINE" | awk '{print $3}')
    S=$(printf '%s' "$LINE" | awk '{print $4}' | tr -d 's')
    [ -n "$V" ] || V=undecided
    [ -n "$S" ] || S="$BUDGET"
    printf '%s\t%s\t%s\t%s\n' "$D" "$V" "$S" "$BUDGET" >> "$CK"
    echo "deg0=$D -> $V ${S}s" ) &
done
wait
echo "--- checkpoint ---"
cat "$CK"
