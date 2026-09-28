#!/bin/bash
# Parallel tail: run the not-yet-started shards of the last three chunks as
# singletons, and stop each chunk worker once its current shard's record lands.
cd /tmp/claude-0/iota
pid_of() { for p in $(pgrep -x isearch); do tr '\0' ' ' < /proc/$p/cmdline | grep -q -- "-l $1 -n 40" && echo $p; done; }
# chunk 10360: stop now (its current shard 10366 is re-run below)
p=$(pid_of 10360); [ -n "$p" ] && kill $p
( for i in $(seq 6551 6559) $(seq 10111 10119) $(seq 10366 10399); do echo $i; done ) | \
  xargs -P 3 -I{} sh -c './isearch -r d6.txt -l {} -n 1 > extra/shard_{}.log; echo "DONE exit=$?" >> extra/shard_{}.log'
echo PREDONE
