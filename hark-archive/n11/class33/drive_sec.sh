#!/bin/bash
. "$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)/_paths.sh"  # portable roots, see hark-archive/_paths.sh
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# usage: drive_sec.sh <modlist> <budget_s>; builds missing modules in order, resumable (olean exists => skip)
LIST=$1; BUD=${2:-100}; S=$(date +%s); n=0
while read m; do
  p=$(echo $m | tr . /)
  [ -f $DCP_N11_ROOT/class33/sector-build/$p.olean ] && continue
  [ $(( $(date +%s) - S )) -gt $BUD ] && { echo "BUDGET stop before $m"; exit 3; }
  "$HERE/build_core.sh" $p >/dev/null || "$HERE/build_core.sh" $p >/dev/null || { echo "FAIL $m"; head -c 800 $DCP_N11_ROOT/class33/sector-build/$p.out; exit 1; }
  n=$((n+1))
done < $LIST
echo "ALLDONE built=$n"
