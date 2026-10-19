#!/bin/bash
. "$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)/_paths.sh"  # portable roots, see hark-archive/_paths.sh
TC=$LEAN_TOOLCHAIN
export LEAN_PATH=$TC/lib/lean:$DCP_N11_ROOT/wip-build/mlib LEAN_NUM_THREADS=1
mkdir -p "$DCP_TMP/wb" && cd "$DCP_TMP/wb"
s=$(date +%s.%N)
nice -n 10 $TC/bin/lean -j1 -M 3500 "$1" > "$1.out" 2>&1 &
pid=$!; peak=0
while kill -0 $pid 2>/dev/null; do h=$(awk '/VmHWM/{print $2}' /proc/$pid/status 2>/dev/null); r=$(awk '/VmRSS/{print $2}' /proc/$pid/status 2>/dev/null); [ -n "$h" ] && echo "$(date +%T) hwm=$h rss=$r memavail=$(awk '/MemAvailable/{print $2}' /proc/meminfo)" >> "$1.mon"; sleep 5; done
wait $pid; echo "rc=$? secs=$(echo "$(date +%s.%N)-$s"|bc)" >> "$1.out"
