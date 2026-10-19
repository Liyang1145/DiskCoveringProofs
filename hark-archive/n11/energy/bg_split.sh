#!/bin/bash
# resumable segments of <=1100 s
cd /workspace/work/dcp-n11-lean/energy
for seg in 1 2 3; do
  MAXDEPTH=12 PERNODE=50 nice -n 10 timeout 1150 python3 split.py 1050 >> logs/split-seg.log 2>&1
done
