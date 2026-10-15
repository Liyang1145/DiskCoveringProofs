#!/usr/bin/env bash
# One resumable build chunk for a track.
# usage: tools/chunk.sh <track> <stages-csv> <deadline-epoch> <chunk-index>
# Writes results/<track>-c<k>.jsonl (per-module rows), results/<track>-c<k>-audit.jsonl,
# results/logs/*.log.gz, and sets GITHUB_OUTPUT done=true|false.
set -uo pipefail
TRACK=$1; STAGES=",$2,"; DEADLINE=$3; K=$4
ROOT=$(pwd); RES=$ROOT/results; mkdir -p $RES/logs
case $TRACK in
  main)   GRPS="A B C D";            AUDITS="A BC D" ;;
  energy) GRPS="energy-matrix energy-paid16 energy-refine"; AUDITS="energy" ;;
  class)  GRPS="class-core class-switch class-face class-asm class-other"; AUDITS="class" ;;
  *) echo "unknown track $TRACK"; exit 2 ;;
esac
# inject drafts as added files (team files are never overwritten)
for d in drafts/*/N11Formalization; do
  for f in $d/*.lean; do
    b=$(basename $f)
    if [ -e lean/N11Formalization/$b ] && ! cmp -s $f lean/N11Formalization/$b; then
      echo "::error::draft $b collides with a team file; not copied"; continue
    fi
    cp $f lean/N11Formalization/$b
  done
done
done_all=true
cd lean
args=()
for G in $GRPS; do
  stage=${G%%-*}
  if [[ "$STAGES" != *",$G,"* && "$STAGES" != *",$stage,"* && "$STAGES" != *",all,"* ]]; then
    echo "skip group $G (not selected)"; continue
  fi
  tf=$ROOT/tools/targets/$G.txt
  [ -f $tf ] && args+=("$G=$tf")
done
t0=$(date +%s)
python3 -u $ROOT/tools/sched.py $TRACK $K $DEADLINE $RES "${args[@]}" 2>&1 | tee $RES/logs/$TRACK-c$K-sched.log | grep -v '"status": "cached"'
rc=${PIPESTATUS[0]}
echo "{\"groups\":\"${args[*]}\",\"sched_rc\":$rc,\"seconds\":$(( $(date +%s)-t0 )),\"chunk\":$K,\"track\":\"$TRACK\"}" >> $RES/$TRACK-c$K-groups.jsonl
[ $rc -eq 0 ] || done_all=false
# audit whatever compiled
for a in $AUDITS; do
  timeout 1500 python3 $ROOT/tools/audit.py $ROOT/tools/audit/$a.txt $RES/$TRACK-c$K-audit.jsonl $TRACK-$a-c$K || true
  cp /tmp/audit_$TRACK-$a-c$K.out $RES/logs/ 2>/dev/null || true
done
cd $ROOT
bash $ROOT/tools/report.sh $TRACK $K once || true
gzip -f $RES/logs/*.log 2>/dev/null || true
du -sh lean/.lake/build 2>/dev/null || true
echo "done=$done_all" >> "${GITHUB_OUTPUT:-/dev/null}"
echo "TRACK $TRACK chunk $K done=$done_all"
