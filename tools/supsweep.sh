#!/bin/bash
# Checkpointed sweep of the support cubes at n points with the Frankl cut B=10.
# supsweep.sh <n> <cap> ; reads cubes<n>.txt, appends to ladder_sup<n>.tsv
cd "$(dirname "$0")"; N=$1; CAP=$2; L=ladder_sup$N.tsv; touch $L
while read c; do
  [ -z "$c" ] && continue
  awk -F'\t' -v c="$c" '$1==c && ($5=="INFEASIBLE"||$5=="FEASIBLE"||$5=="OPTIMAL"){f=1} END{exit !f}' $L && continue
  out=$(python3 cuben.py $N "$c" 1 "$CAP" 62 10 2>&1)
  degs=$(echo "$out" | sed -n 's/.*degs=\[\([0-9, ]*\)\].*/\1/p' | tr -d ' ')
  st=$(echo "$out" | grep -oE 'status [A-Z_]+ time [0-9.]+s' | tail -1)
  status=$(echo "$st" | awk '{print $2}'); secs=$(echo "$st" | awk '{print $4}' | tr -d s)
  wit=$(echo "$out" | grep '^WITNESS' | head -1)
  printf '%s\t%s\t62\t10\t%s\t%s\t%s\n' "$c" "$degs" "${status:-ERROR}" "${secs:-0}" "$wit" >> $L
done < cubes$N.txt
