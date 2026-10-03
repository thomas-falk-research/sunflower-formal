#!/bin/bash
# watch.sh CHUNK LASTSHARD: once SHARD LASTSHARD's record is complete in the
# chunk's tmp log, stop the chunk worker (its remaining shards run in tail.sh).
cd /tmp/claude-0/iota; C=$1; L=$2; f=logs/chunk_$(printf %05d $C).log.tmp
until grep -q -A1 "^SHARD $L " $f 2>/dev/null && [ $(grep -A1 "^SHARD $L " $f | grep -c "^ACCEPTED") -eq 1 ]; do sleep 5; done
for p in $(pgrep -x isearch); do tr '\0' ' ' < /proc/$p/cmdline | grep -q -- "-l $C -n 40" && kill $p && echo "stopped chunk $C after shard $L"; done
