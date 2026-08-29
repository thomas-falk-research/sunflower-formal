#!/bin/sh
# Drive a rung to completion in batches, committing after each so that a
# container restart costs at most the batch in flight.
set -e
cd /home/user/sunflower-formal
until [ "$(ps -eo args | grep -c '[i]ota_sym')" -eq 0 ]; do sleep 30; done
for BATCH in "18 17 16 15" "14 13 12"; do
  # shellcheck disable=SC2086
  tools/rung.sh 4 11 32 7200 $BATCH || true
  git add -A
  git commit -q -m "iota(4,11): cubes $BATCH

Verdicts appended to docs/ladder/iota4_11.tsv by tools/rung_chain.sh.
A cube recorded 'undecided' carries the budget it was stopped at; the
rung is UNSAT only when every one of the twenty-one is." || true
  git push -q origin claude/sunflower-session-n11-mkonqv || true
done
echo CHAIN_DONE
