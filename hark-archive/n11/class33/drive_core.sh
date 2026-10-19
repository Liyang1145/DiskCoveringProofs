#!/bin/bash
# Resumable sequential driver: builds Class33Core.SwTrees modules listed in data/core_switch_modules.txt.
# Segment cap 1100 s. Writes progress to logs/drive.progress (atomic append).
cd /workspace/work/dcp-n11-lean/class33
START=$(date +%s)
for m in $(cat data/core_switch_modules.txt); do
  [ -s /tmp/c33/Class33Core/SwTrees/$m.olean ] && continue
  now=$(date +%s); [ $((now-START)) -gt 1000 ] && { echo "SEGMENT-CAP $(date +%s)" >> logs/drive.progress; exit 0; }
  ./build_core.sh Class33Core/SwTrees/$m > /dev/null; rc=$?
  echo "$m rc=$rc $(date +%s)" >> logs/drive.progress
  [ $rc != 0 ] && { echo "FAIL $m" >> logs/drive.progress; }
done
echo "ALLDONE $(date +%s)" >> logs/drive.progress
