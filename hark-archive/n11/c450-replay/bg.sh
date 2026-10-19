#!/bin/bash
cd /workspace/work/dcp-n11-lean/c450-replay
while true; do
  python3 drive.py $(seq 23 36) $(seq 12 22) 11 >> logs/bg-driver.log 2>&1
  n=$(python3 -c "
import os
k=list(range(11,37));m=[f'/tmp/lc/DCPN11Core/C450Replay/Seg{s}/All.olean' for s in k]
print(sum(not os.path.exists(x) for x in m))")
  [ "$n" = 0 ] && break
done
echo ALLDONE >> logs/bg-driver.log
