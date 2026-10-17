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
for G in $GRPS; do
  stage=${G%%-*}
  if [[ "$STAGES" != *",$G,"* && "$STAGES" != *",$stage,"* && "$STAGES" != *",all,"* ]]; then
    echo "skip group $G (not selected)"; continue
  fi
  tf=$ROOT/tools/targets/$G.txt
  [ -f $tf ] || { echo "no targets for $G"; continue; }
  now=$(date +%s); left=$((DEADLINE-now))
  if [ $left -lt 300 ]; then echo "deadline reached before $G"; done_all=false; break; fi
  echo "::group::lake build $G ($(wc -l <$tf) targets, ${left}s left)"
  t0=$(date +%s)
  timeout --signal=INT --kill-after=180 $left lake build $(cat $tf) > $RES/logs/$TRACK-c$K-$G.log 2>&1
  rc=$?
  echo "::endgroup::"
  dt=$(( $(date +%s)-t0 ))
  grep -E "^(✖|error)" $RES/logs/$TRACK-c$K-$G.log | head -50
  tail -5 $RES/logs/$TRACK-c$K-$G.log
  python3 $ROOT/tools/parse_lake_log.py $RES/logs/$TRACK-c$K-$G.log $G $RES/$TRACK-c$K.jsonl $tf
  echo "{\"group\":\"$G\",\"lake_rc\":$rc,\"seconds\":$dt,\"chunk\":$K,\"track\":\"$TRACK\"}" >> $RES/$TRACK-c$K-groups.jsonl
  echo "GROUP $G rc=$rc ${dt}s"
  if [ $rc -eq 124 ] || [ $rc -eq 130 ] || [ $rc -eq 137 ]; then done_all=false; break; fi
done
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
