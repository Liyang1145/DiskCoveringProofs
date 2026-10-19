#!/bin/bash
. "$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)/_paths.sh"  # portable roots, see hark-archive/_paths.sh
# sequential, resumable: skips chunks whose olean exists or that already have an rc=0 row
cd "$DCP_N11_ROOT/energy"
end=$(( $(python3 -c "import time;print(int(time.time()))") + ${1:-1100} ))
for nm in $(python3 -c "import json;print(' '.join(json.load(open('lean-core/chunks.json'))))"); do
  [ $(python3 -c "import time;print(int(time.time()))") -gt $end ] && break
  grep -q "\"EnergyReplay.Grp.$nm\", \"rc\": 0" logs/core-build.jsonl && continue
  [ -f $DCP_TMP/en/EnergyReplay/Weights.olean ] || { python3 runlean.py EnergyReplay/Kernel; python3 runlean.py EnergyReplay/Weights; }
  TMO=600 python3 runlean.py EnergyReplay/Grp/$nm >> logs/bg_core2.log 2>&1
done
