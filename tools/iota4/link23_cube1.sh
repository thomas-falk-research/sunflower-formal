#!/bin/bash
# cube1.sh FILEBASE : solve + drat-trim one cube; writes FILEBASE.res (UNSAT-VERIFIED / SAT / FAIL)
b=$1; [ -f $b.res ] && exit 0; mkdir $b.lock 2>/dev/null || exit 0
/tmp/claude-0/tools/cadical/build/cadical -q $b.cnf $b.drat > $b.out; rc=$?
if [ $rc = 20 ]; then
  /tmp/claude-0/tools/drat-trim/drat-trim $b.cnf $b.drat -t 50000 | tr -d '\r' > $b.dt
  if grep -q "^s VERIFIED" $b.dt; then echo "UNSAT-VERIFIED $(grep 'verification time' $b.dt)" > $b.res; else echo "FAIL drat" > $b.res; fi
elif [ $rc = 10 ]; then echo "SAT" > $b.res
else echo "FAIL rc=$rc" > $b.res; fi
rm -f $b.drat
