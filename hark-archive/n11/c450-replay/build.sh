#!/bin/bash
# Build one module: $1 = module path relative to lean-core (e.g. DCPN11Core/C450Replay/Seg14/Cells1)
# Sources on /workspace (FUSE); oleans in RAM (/tmp/lc); logs appended on /workspace.
set -o pipefail
M=$1; SRC=/workspace/work/dcp-n11-lean/lean-core/$M.lean; OUT=/tmp/lc/$M.olean
LOG=/workspace/work/dcp-n11-lean/c450-replay/logs; mkdir -p $LOG $(dirname $OUT)
[ -s $OUT ] && exit 0
export LEAN_PATH=/tmp/slim/lib/lean:/tmp/lc
cp $SRC /tmp/lc/$M.lean; cd /tmp/lc
s=$(date +%s); /tmp/slim/bin/lean -o $OUT.part $M.lean > /tmp/lc/$M.out 2>&1; rc=$?
e=$(date +%s); n=$(echo $M | tr / .)
[ $rc = 0 ] && mv $OUT.part $OUT || rm -f $OUT.part
echo "{\"module\":\"$n\",\"rc\":$rc,\"seconds\":$((e-s)),\"src_sha256\":\"$(sha256sum $SRC|cut -c1-64)\",\"utc\":\"$(python3 -c "import time;print(time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()))")\"}" >> $LOG/build.jsonl
cp /tmp/lc/$M.out $LOG/$n.out
exit $rc
