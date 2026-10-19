#!/bin/bash
cd /workspace/work/dcp-n26
DEADLINE=$(python3 -c "import time;print(time.time()+100)") timeout 115 python3 bnb.py "$@" 2>&1 | grep -v skipped | tail -3
ls certs | grep -c json
