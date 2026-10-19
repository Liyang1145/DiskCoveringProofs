#!/bin/bash
. "$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)/_paths.sh"  # portable roots, see hark-archive/_paths.sh
# run both B shards in parallel within one shell command (<=110s)
cd "$DCP_N26_ROOT/v3replay"
B=${1:-90}
for sh in 0 1; do (timeout $((B+18)) python3 certB_v3.py $B $sh 2 > bpar_$sh.out 2>&1; echo "rc=$?" >> bpar_$sh.out) & done
wait
for sh in 0 1; do tail -n 2 bpar_$sh.out | cut -c1-600; done
