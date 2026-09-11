#!/bin/bash
# Run sub-cube sweeps for every cube stalled at the cap in ladder11.tsv,
# one at a time, until the main pass is done and nothing is left.
# subchain.sh <cap seconds>
cd "$(dirname "$0")"; CAP=${1:-600}
while true; do
  next=""
  # stalled cubes, longest cap first (7200 s stalls before 1800 s ones)
  for c in $(awk -F'\t' '$5=="UNKNOWN"{print $6"\t"$1}' ladder11.tsv | sort -t$'\t' -k1,1nr | cut -f2 | awk '!s[$0]++'); do
    # skip cubes closed flat on a later re-run
    awk -F'\t' -v c="$c" '$1==c && $5=="INFEASIBLE"{f=1} END{exit !f}' ladder11.tsv && continue
    [ -f "sub_$c.txt" ] || python3 cubesub.py 11 "$c" --list > "sub_$c.txt" 2>/dev/null
    tot=$(wc -l < "sub_$c.txt"); k=$(awk -F'\t' -v c="$c" '$1==c && $5=="INFEASIBLE"' ladder11sub.tsv | wc -l)
    [ "$k" -ge "$tot" ] && continue
    pgrep -f "subsweep.sh $c " >/dev/null && continue
    next=$c; break
  done
  if [ -n "$next" ]; then bash subsweep.sh "$next" "$CAP" 1; continue; fi
  if ! pgrep -f 'sweep11.sh' >/dev/null && ! pgrep -f 'subsweep.sh' >/dev/null; then echo "subchain: nothing left"; exit 0; fi
  sleep 120
done
