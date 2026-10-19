#!/bin/bash
cd /workspace/work/dcp-n26/v3replay
for sh in 0 1; do (BSUF=${BSUF:-_n1} timeout 108 python3 certB_lite.py ${1:-100} $sh 2 2>&1 | tail -c 300 | sed "s/^/[$sh] /") & done; wait
