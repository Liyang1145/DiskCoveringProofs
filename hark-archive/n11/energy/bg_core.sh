#!/bin/bash
cd /workspace/work/dcp-n11-lean/energy
TMO=1140 python3 runlean.py EnergyReplay/Controls > logs/bg_core.log 2>&1
TMO=1140 python3 runlean.py EnergyReplay/Grp/NewTight4 >> logs/bg_core.log 2>&1
