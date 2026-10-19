#!/bin/bash
. "$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)/_paths.sh"  # portable roots, see hark-archive/_paths.sh
# core-Lean (no Mathlib) build of one class33 module; WIP toolchain v4.33.1 core (Init only).
set -o pipefail
M=$1; L=$LEAN
SRC=$DCP_N11_ROOT/class33/lean-core/$M.lean; B=$DCP_N11_ROOT/class33/sector-build; mkdir -p $B/$(dirname $M)
LOG=$DCP_N11_ROOT/class33/logs; mkdir -p $LOG
export LEAN_PATH=$LEAN_TOOLCHAIN/lib/lean:$B
cp $SRC $B/$M.lean; cd $B
s=$(date +%s); timeout 1100 nice -n 10 $L -o $B/$M.olean.part $M.lean > $B/$M.out 2>&1; rc=$?
e=$(date +%s); n=$(echo $M | tr / .)
[ $rc = 0 ] && mv $B/$M.olean.part $B/$M.olean || rm -f $B/$M.olean.part
cp $B/$M.out $LOG/$n.out
echo "{\"module\":\"$n\",\"rc\":$rc,\"seconds\":$((e-s)),\"toolchain\":\"v4.33.1-core\",\"src_sha256\":\"$(sha256sum $SRC|cut -c1-64)\",\"epoch\":$e}" | tee -a $DCP_N11_ROOT/class33/ledger.jsonl
exit $rc
