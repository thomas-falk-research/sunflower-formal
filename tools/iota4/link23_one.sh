#!/bin/bash
# one.sh K : CNF -> CaDiCaL (DRAT) -> drat-trim; writes cK.log with both verdicts; deletes proof after checking
W=$(dirname $0); k=$1; cd /home/user/sunflower-formal
[ -f $W/c$k.cnf ] || python3 tools/iota4/link23.py cnf docs/ladder/iota4_replication/classes_23_27.txt.gz $k $W/c$k.cnf > /dev/null
if [ ! -f $W/c$k.solved ]; then
  /tmp/claude-0/tools/cadical/build/cadical -q $W/c$k.cnf $W/c$k.drat > /dev/null; echo "cadical_rc=$?" > $W/c$k.solved
fi
/tmp/claude-0/tools/drat-trim/drat-trim $W/c$k.cnf $W/c$k.drat -t 20000 > $W/c$k.dt 2>&1
{ echo "class $k"; head -1 $W/c$k.cnf; cat $W/c$k.solved; tr -d "\r" < $W/c$k.dt | grep -E "^s |verification time|in core"; sha256sum $W/c$k.cnf | cut -c1-64; } > $W/c$k.log
tr -d "\r" < $W/c$k.dt | grep -q "^s VERIFIED" && rm -f $W/c$k.drat
