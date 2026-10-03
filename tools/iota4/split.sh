#!/bin/bash
# split.sh CHUNK HEAVY...   -- redo chunk CHUNK (40 shards) with the listed
# heavy shards split at depth 10 and their sub-shards run 4-way parallel.
cd /tmp/claude-0/iota; C=$1; shift; H=" $* "
mkdir -p split/$C; out=split/$C/records.txt; : > $out
for i in $(seq $C $((C+39))); do
  [ $i -ge 11720 ] && break
  if [[ "$H" == *" $i "* ]]; then
    ./isearch -r d6.txt -l $i -n 1 -e 10 -o split/$C/sub_$i.txt > split/$C/emit_$i.log
    n=$(grep -c "^S " split/$C/sub_$i.txt)
    seq 0 200 $((n-1)) | xargs -P 4 -I{} sh -c "./isearch -r split/$C/sub_$i.txt -l {} -n 200 > split/$C/sub_${i}_\$(printf %07d {}).log; echo \"DONE exit=\$?\" >> split/$C/sub_${i}_\$(printf %07d {}).log"
    python3 combine.py $i split/$C/emit_$i.log split/$C/sub_$i.txt "split/$C/sub_${i}_*.log" >> $out || exit 1
  else
    ./isearch -r d6.txt -l $i -n 1 | sed -n '1,2p' >> $out
  fi
done
echo "DONE exit=20" >> $out
