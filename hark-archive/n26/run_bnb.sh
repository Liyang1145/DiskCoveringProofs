#!/bin/bash
. "$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)/_paths.sh"  # portable roots, see hark-archive/_paths.sh
cd "$DCP_N26_ROOT"
DEADLINE=$(python3 -c "import time;print(time.time()+100)") timeout 115 python3 bnb.py "$@" 2>&1 | grep -v skipped | tail -3
ls certs | grep -c json
