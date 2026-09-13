#!/bin/sh
# Checkpointed sweep of the 139 eleven-point cubes. Args: cap_seconds jobs.
# Banks one TSV row per attempt into ladder11.tsv; cubes already INFEASIBLE
# (or SAT) are skipped on re-runs, UNKNOWN ones are re-attempted.
cap=${1:-1800}; jobs=${2:-4}
LADDER=ladder11.tsv; touch $LADDER
run_one() {
  c=$1; cap=$2
  if grep -q "^$c	.*	INFEASIBLE\|^$c	.*	FEASIBLE" $LADDER 2>/dev/null; then exit 0; fi
  out=$(python3 cuben.py 11 $c 1 $cap 62 16 2>&1)
  degs=$(echo "$out" | sed -n 's/.*degs=\[\([0-9, ]*\)\].*/\1/p' | tr -d ' ')
  st=$(echo "$out" | sed -n 's/.*status \([A-Z]*\) time \([0-9.]*\)s.*/\1\t\2/p')
  wit=$(echo "$out" | grep WITNESS | head -1)
  printf '%s\t%s\t62\t16\t%s\t%s\n' "$c" "$degs" "$st" "$wit" >> $LADDER
}
export -f run_one 2>/dev/null
export LADDER
cat cubes11.txt | xargs -P $jobs -I{} sh -c "$(declare -f run_one); run_one {} $cap"
