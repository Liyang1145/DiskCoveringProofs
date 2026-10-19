#!/bin/bash
# core-Lean (no Mathlib) build of one class33 module; WIP toolchain v4.33.1 core (Init only).
set -o pipefail
M=$1; L=/var/tmp/lean/lean-4.33.1-linux_aarch64/bin/lean
SRC=/workspace/work/dcp-n11-lean/class33/lean-core/$M.lean; B=/workspace/work/dcp-n11-lean/class33/sector-build; mkdir -p $B/$(dirname $M)
LOG=/workspace/work/dcp-n11-lean/class33/logs; mkdir -p $LOG
export LEAN_PATH=/var/tmp/lean/lean-4.33.1-linux_aarch64/lib/lean:$B
cp $SRC $B/$M.lean; cd $B
s=$(date +%s); timeout 1100 nice -n 10 $L -o $B/$M.olean.part $M.lean > $B/$M.out 2>&1; rc=$?
e=$(date +%s); n=$(echo $M | tr / .)
[ $rc = 0 ] && mv $B/$M.olean.part $B/$M.olean || rm -f $B/$M.olean.part
cp $B/$M.out $LOG/$n.out
echo "{\"module\":\"$n\",\"rc\":$rc,\"seconds\":$((e-s)),\"toolchain\":\"v4.33.1-core\",\"src_sha256\":\"$(sha256sum $SRC|cut -c1-64)\",\"epoch\":$e}" | tee -a /workspace/work/dcp-n11-lean/class33/ledger.jsonl
exit $rc
