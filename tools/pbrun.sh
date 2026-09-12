#!/bin/bash
# pbrun.sh <n> <cube> <K> <B> : export, solve with proof log, verify; append a row to pbladder.tsv
S=${PB_SCRATCH:?set PB_SCRATCH to a directory holding roundingsat/ and VeriPB/ builds}
cd $S/pb; n=$1; c=$2; K=$3; B=$4; tag="c${n}_${c}_K${K}_B$B"
python3 $S/cube_opb.py $n $c $K $B > $tag.opb
t0=$(date +%s.%N); $S/roundingsat/build/roundingsat --proof-log=$tag $tag.opb > $tag.rs.log 2>&1; rc=$?; t1=$(date +%s.%N)
verdict=$(grep -E '^s ' $tag.rs.log | head -1 | cut -c3-)
$S/VeriPB/target/release/veripb --opb $tag.opb $tag > $tag.vp.log 2>&1; vrc=$?; t2=$(date +%s.%N)
vres=$(grep -E '^s ' $tag.vp.log | head -1 | cut -c3-)
size=$(stat -c %s $tag 2>/dev/null)
printf '%s\t%s\t%s\t%s\t%s\t%.1f\t%s\t%.1f\t%s\n' "$n" "$c" "$K" "$B" "${verdict:-none(rc=$rc)}" "$(echo "$t1-$t0"|bc)" "${vres:-none(rc=$vrc)}" "$(echo "$t2-$t1"|bc)" "$size" >> $S/pb/pbladder.tsv
[ "$vres" = "VERIFIED UNSATISFIABLE" ] && rm -f $tag   # keep proofs only if something is off
