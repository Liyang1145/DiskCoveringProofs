#!/bin/bash
. "$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)/_paths.sh"  # portable roots, see hark-archive/_paths.sh
# build one core module: $1 = EnergyReplay/... (no .lean). oleans in $DCP_TMP/en, log appended.
set -o pipefail
M=$1  # LEAN comes from _paths.sh
SRC=$DCP_N11_ROOT/energy/lean-core/$M.lean; OUT=$DCP_TMP/en/$M.olean
LOG=$DCP_N11_ROOT/energy/logs; mkdir -p $LOG $(dirname $OUT)
export LEAN_PATH=$DCP_TMP/en
mkdir -p $(dirname $DCP_TMP/en/$M.lean); cp $SRC $DCP_TMP/en/$M.lean; cd $DCP_TMP/en
s=$(date +%s.%N); /usr/bin/time -f "%M" -o $DCP_TMP/en/$M.mem nice -n 10 $LEAN -o $OUT.part $M.lean > $DCP_TMP/en/$M.out 2>&1; rc=$?
e=$(date +%s.%N); n=$(echo $M | tr / .)
[ $rc = 0 ] && mv $OUT.part $OUT || rm -f $OUT.part
echo "{\"module\":\"$n\",\"rc\":$rc,\"seconds\":$(python3 -c "print(round($e-$s,1))"),\"maxrss_kb\":$(cat $DCP_TMP/en/$M.mem 2>/dev/null | tail -1 || echo null),\"src_sha256\":\"$(sha256sum $SRC|cut -c1-64)\",\"utc\":\"$(date -u +%FT%TZ)\"}" >> $LOG/core-build.jsonl
cp $DCP_TMP/en/$M.out $LOG/$n.out
exit $rc
