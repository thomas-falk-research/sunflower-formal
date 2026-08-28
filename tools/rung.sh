#!/bin/sh
# One batch of deg(0) cubes for a single rung of the iota ladder, run as
# separate single-threaded processes so a container restart loses at most
# the batch in flight. Verdicts append to the checkpoint; already-decided
# cubes are skipped.
#
#   tools/rung.sh <b> <ground> <target> <budget-seconds> <deg>...
#
# Env:
#   RUNG_THREADS  cores per cube (default 1). With more than one, set
#                 RUNG_SLICE below the budget so the cube stalls and
#                 phase two splits it by degree sequence -- that split is
#                 what is parallel; a single cube whole is one sequential
#                 cadical and uses one core no matter what this is set to.
#   RUNG_SLICE    seconds before a cube is handed to the sequence split
#                 (default: the whole budget, i.e. never split). Set it
#                 well below the budget when you want the split: at the
#                 default a cube that does not refine is not re-run at
#                 all, because phase two would repeat phase one exactly
#                 (docs/roadmap.md §49.3).
#   RUNG_CUBECAP  most sequence cubes to accept (default 400).
#   RUNG_SEQPREFIX  fix only the first N degrees when splitting, instead
#                 of the whole sequence. This is the dial that decides how
#                 large the split is, and at eleven points it is the
#                 difference between 726 sub-cubes and more than a
#                 million: see docs/roadmap.md §49.2 for the table.
#                 Default: the whole ground set.
#
# The checkpoint is a TRACKED file and this script appends to it, so a
# run leaves the working tree dirty and `git pull` will refuse. The rows
# are data worth keeping: commit them rather than stashing.
#
#   git add docs/ladder/iota${B}_${G}.tsv
#   git commit -m 'iota(4,11): cube N from <machine>'
#   git pull --rebase
#
# .gitattributes sets merge=union on these files, so rows appended on two
# machines merge instead of conflicting.
#
# See docs/roadmap.md §36 for why the rung is run this way.
set -e
B=$1; G=$2; T=$3; BUDGET=$4; shift 4
SOLVER="${RUNG_SOLVER:-cadical}"
# A second solver gets its own checkpoint: sat::solve_agreed wants two
# independent verdicts per cube, and merging them into one file keyed by
# deg0 would silently overwrite one with the other.
BASE="docs/ladder/iota${B}_${G}"
[ "$SOLVER" = "cadical" ] || BASE="${BASE}.${SOLVER}"

# The checkpoint used to be keyed by (b, ground) alone, but a rung is a
# (b, ground, TARGET) question. The skip test below matches the deg
# column and ignores everything else, so a target-32 row in the file
# would be read as a target-28 verdict and the cube never run -- a
# recorded result for a search that did not happen, which is the failure
# class docs/roadmap.md §36 exists to prevent. So the target picks the
# file, and an existing file is used only when it is this target's.
if [ -n "${RUNG_CHECKPOINT:-}" ]; then
  CK="$RUNG_CHECKPOINT"
elif [ -f "${BASE}.t${T}.tsv" ]; then
  CK="${BASE}.t${T}.tsv"
elif [ ! -f "${BASE}.tsv" ] || head -5 "${BASE}.tsv" | grep -q ">= $T "; then
  CK="${BASE}.tsv"
else
  CK="${BASE}.t${T}.tsv"
fi
echo "rung.sh: checkpoint $CK"
if [ ! -f "$CK" ]; then
  printf '# iota(%s,%s) >= %s ?  %s pass, one line per deg(0) cube.\n# Written by tools/rung.sh. The rung is UNSAT only when EVERY cube is.\n# An `undecided` row carries the budget it was stopped at.\n# deg0\tverdict\tseconds\tbudget\n' \
    "$B" "$G" "$T" "$SOLVER" > "$CK"
fi
BIN=rust/target/release/examples/iota_sym
# Passed through only when set, so the default stays whatever the driver's
# default is rather than being pinned here in a second place.
if [ -n "${RUNG_SEQPREFIX:-}" ]; then
  PREFIX_ARG="--seqprefix ${RUNG_SEQPREFIX}"
else
  PREFIX_ARG=""
fi

# A missing solver must not become a mathematical verdict. Without this
# check the driver errors, no verdict line is printed, and the fallback
# below writes `undecided` with the full budget -- a ten-hour exhausted
# search that never ran. That happened; see docs/roadmap.md §36.
if ! command -v "$SOLVER" >/dev/null 2>&1; then
  echo "rung.sh: solver '$SOLVER' is not on PATH -- refusing to run." >&2
  echo "         install it, or a failed run is recorded as a result." >&2
  exit 2
fi
for D in "$@"; do
  if awk -F'\t' -v d="$D" '$1==d {found=1} END {exit !found}' "$CK" 2>/dev/null; then
    echo "skip deg0=$D (already decided)"; continue
  fi
  ( T0=$(date +%s)
    # shellcheck disable=SC2086  # PREFIX_ARG is a flag pair or empty
    OUT=$("$BIN" "$B" "$G" "$T" --ladder --from "$G" --only-deg "$D" \
            --threads "${RUNG_THREADS:-1}" --slice "${RUNG_SLICE:-$BUDGET}" \
            --seconds "$BUDGET" --cubecap "${RUNG_CUBECAP:-400}" \
            $PREFIX_ARG --solver "$SOLVER" 2>&1 || true)
    printf '%s\n' "$OUT" | grep -E "^# g = .*(refined|sequence cubes|UNSAT|UNKNOWN)" || true
    # A cube decided whole reports on its own line; one decided by the
    # sequence split reports only in the rung summary, so take that.
    LINE=$(printf '%s\n' "$OUT" | grep -E "deg\(0\)=$D " | tail -1)
    V=$(printf '%s' "$LINE" | awk '{print $3}')
    S=$(printf '%s' "$LINE" | awk '{print $4}' | tr -d 's')
    if [ -z "$V" ] || [ "$V" = "UNKNOWN" ]; then
      SUM=$(printf '%s\n' "$OUT" | grep -E "^# g = $G: (UNSAT|UNKNOWN) after" | tail -1)
      [ -n "$SUM" ] && V=$(printf '%s' "$SUM" | awk '{print $5}')
      [ -n "$SUM" ] && S=$(printf '%s' "$SUM" | awk '{print $7}' | tr -d 's')
    fi
    ELAPSED=$(( $(date +%s) - T0 ))
    [ -n "$V" ] || V=undecided
    [ -n "$S" ] || S="$BUDGET"
    # An `undecided` that did not spend most of its budget did not run.
    # Record it as an error with what actually happened, never as a
    # search that was performed.
    if [ "$V" = "undecided" ] && [ "$ELAPSED" -lt $(( BUDGET / 2 )) ]; then
      echo "rung.sh: deg0=$D gave up after ${ELAPSED}s of a ${BUDGET}s budget:" >&2
      printf '%s\n' "$OUT" | tail -5 >&2
      V=ERROR; S="$ELAPSED"
    fi
    printf '%s\t%s\t%s\t%s\n' "$D" "$V" "$S" "$BUDGET" >> "$CK"
    echo "deg0=$D -> $V ${S}s" ) &
done
wait
echo "--- checkpoint ---"
cat "$CK"
