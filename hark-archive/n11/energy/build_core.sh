#!/bin/bash
# build one core module: $1 = EnergyReplay/... (no .lean). oleans in /tmp/en (RAM), log appended.
set -o pipefail
M=$1; LEAN=/var/tmp/lean/lean-4.33.1-linux_aarch64/bin/lean
SRC=/workspace/work/dcp-n11-lean/energy/lean-core/$M.lean; OUT=/tmp/en/$M.olean
LOG=/workspace/work/dcp-n11-lean/energy/logs; mkdir -p $LOG $(dirname $OUT)
export LEAN_PATH=/tmp/en
mkdir -p $(dirname /tmp/en/$M.lean); cp $SRC /tmp/en/$M.lean; cd /tmp/en
s=$(date +%s.%N); /usr/bin/time -f "%M" -o /tmp/en/$M.mem nice -n 10 $LEAN -o $OUT.part $M.lean > /tmp/en/$M.out 2>&1; rc=$?
e=$(date +%s.%N); n=$(echo $M | tr / .)
[ $rc = 0 ] && mv $OUT.part $OUT || rm -f $OUT.part
echo "{\"module\":\"$n\",\"rc\":$rc,\"seconds\":$(python3 -c "print(round($e-$s,1))"),\"maxrss_kb\":$(cat /tmp/en/$M.mem 2>/dev/null | tail -1 || echo null),\"src_sha256\":\"$(sha256sum $SRC|cut -c1-64)\",\"utc\":\"$(date -u +%FT%TZ)\"}" >> $LOG/core-build.jsonl
cp /tmp/en/$M.out $LOG/$n.out
exit $rc
