#!/bin/bash
. "$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)/_paths.sh"  # portable roots, see hark-archive/_paths.sh
cd "$DCP_N11_ROOT/c450-replay"
while true; do
  python3 drive.py $(seq 23 36) $(seq 12 22) 11 >> logs/bg-driver.log 2>&1
  n=$(python3 -c "
import os
D=os.environ['DCP_TMP']
k=list(range(11,37));m=[f'{D}/lc/DCPN11Core/C450Replay/Seg{s}/All.olean' for s in k]
print(sum(not os.path.exists(x) for x in m))")
  [ "$n" = 0 ] && break
done
echo ALLDONE >> logs/bg-driver.log
