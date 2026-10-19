#!/bin/bash
. "$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)/_paths.sh"  # portable roots, see hark-archive/_paths.sh
C450_TC=${C450_LEAN_TOOLCHAIN:-$LEAN_TOOLCHAIN}
# Build one module: $1 = module path relative to lean-core (e.g. DCPN11Core/C450Replay/Seg14/Cells1)
# Sources in $DCP_N11_ROOT/lean-core; oleans in $DCP_TMP/lc; logs appended to $DCP_N11_ROOT/c450-replay/logs.
# Toolchain: the original replay used a slim core-only Lean v4.35.0 (Init only); override with
# C450_LEAN_TOOLCHAIN, otherwise $LEAN_TOOLCHAIN (v4.33.1) is used.
set -o pipefail
M=$1; SRC=$DCP_N11_ROOT/lean-core/$M.lean; OUT=$DCP_TMP/lc/$M.olean
LOG=$DCP_N11_ROOT/c450-replay/logs; mkdir -p $LOG $(dirname $OUT)
[ -s $OUT ] && exit 0
export LEAN_PATH=$C450_TC/lib/lean:$DCP_TMP/lc
cp $SRC $DCP_TMP/lc/$M.lean; cd $DCP_TMP/lc
s=$(date +%s); $C450_TC/bin/lean -o $OUT.part $M.lean > $DCP_TMP/lc/$M.out 2>&1; rc=$?
e=$(date +%s); n=$(echo $M | tr / .)
[ $rc = 0 ] && mv $OUT.part $OUT || rm -f $OUT.part
echo "{\"module\":\"$n\",\"rc\":$rc,\"seconds\":$((e-s)),\"src_sha256\":\"$(sha256sum $SRC|cut -c1-64)\",\"utc\":\"$(python3 -c "import time;print(time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()))")\"}" >> $LOG/build.jsonl
cp $DCP_TMP/lc/$M.out $LOG/$n.out
exit $rc
