#!/bin/bash
. "$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)/_paths.sh"  # portable roots, see hark-archive/_paths.sh
cd "$DCP_N26_ROOT/v3replay"
B=${1:-95}
for sh in 0 1; do (timeout $((B+12)) python3 certB_lite.py $B $sh 2 > bl_$sh.out 2>&1; echo "rc=$?" >> bl_$sh.out) & done
sleep 30; ps -o rss= -C python3 | awk '{s+=$1} END {print "rss", s/1024 " MB"}'
wait
for sh in 0 1; do tail -c 400 bl_$sh.out; done
