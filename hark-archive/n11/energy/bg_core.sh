#!/bin/bash
. "$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)/_paths.sh"  # portable roots, see hark-archive/_paths.sh
cd "$DCP_N11_ROOT/energy"
TMO=1140 python3 runlean.py EnergyReplay/Controls > logs/bg_core.log 2>&1
TMO=1140 python3 runlean.py EnergyReplay/Grp/NewTight4 >> logs/bg_core.log 2>&1
