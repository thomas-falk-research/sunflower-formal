#!/bin/bash
# Checkpointed sub-cube sweep: subsweep.sh <cube> <cap seconds> <jobs>
# Reads sub_<cube>.txt, appends to ladder11sub.tsv:
#   cube \t profile \t K \t B \t status \t seconds \t witness
cd "$(dirname "$0")"
CUBE=$1; CAP=$2; JOBS=${3:-1}; LIST=${4:-sub_$CUBE.txt}; L=ladder11sub.tsv; touch $L
run_one() {
  local cube=$1 prof=$2 cap=$3 L=ladder11sub.tsv
  if awk -F'\t' -v c="$cube" -v p="$prof" '$1==c && $2==p && ($5=="INFEASIBLE"||$5=="FEASIBLE"||$5=="OPTIMAL"){f=1} END{exit !f}' $L; then return; fi
  out=$(python3 cubesub.py 11 "$cube" "$prof" 1 "$cap" 62 16 2>&1)
  st=$(echo "$out" | grep -oE 'status [A-Z_]+ time [0-9.]+s' | tail -1)
  status=$(echo "$st" | awk '{print $2}'); secs=$(echo "$st" | awk '{print $4}' | tr -d s)
  wit=$(echo "$out" | grep '^WITNESS' | head -1)
  printf '%s\t%s\t62\t16\t%s\t%s\t%s\n' "$cube" "$prof" "${status:-ERROR}" "${secs:-0}" "$wit" >> $L
}
export -f run_one
grep -v "^#" "$LIST" | xargs -P "$JOBS" -I{} bash -c 'run_one "$0" "$1" "$2"' "$CUBE" {} "$CAP"
