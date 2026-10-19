#!/bin/bash
# Resumable driver v2 (full module paths, data/core_modules_v2.txt). Segment cap ~1000 s; waits for MemAvailable>=1.5GB.
cd /workspace/work/dcp-n11-lean/class33
START=$(date +%s)
for m in $(cat data/core_modules_v2.txt); do
  [ -s /tmp/c33/$m.olean ] && continue
  while [ $(awk '/MemAvailable/{print int($2/1024)}' /proc/meminfo) -lt 1500 ]; do sleep 20; [ $(( $(date +%s)-START )) -gt 1000 ] && { echo "SEGMENT-CAP-MEMWAIT $(date +%s)" >> logs/drive2.progress; exit 0; }; done
  now=$(date +%s); [ $((now-START)) -gt 1000 ] && { echo "SEGMENT-CAP $(date +%s)" >> logs/drive2.progress; exit 0; }
  ./build_core.sh $m > /dev/null; rc=$?
  echo "$m rc=$rc $(date +%s)" >> logs/drive2.progress
  [ $rc != 0 ] && { echo "FAIL $m" >> logs/drive2.progress; exit 3; }
done
echo "ALLDONE $(date +%s)" >> logs/drive2.progress
