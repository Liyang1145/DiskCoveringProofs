#!/usr/bin/env bash
# Progress reporter via commit statuses on $GITHUB_SHA (no branch writes). Reads results/progress-<track>.json
# written by sched.py. Contexts: n11/<track> (counts, failures) and n11/<track>/diag (memory, running modules).
# usage: tools/report.sh <track> <chunk> [once]     (cwd ci-n11/, GH_TOKEN with statuses:write)
TRACK=$1; K=$2; INTERVAL=${INTERVAL:-600}
post() {  # state context description
  gh api -X POST "repos/$GITHUB_REPOSITORY/statuses/$GITHUB_SHA" -f state="$1" -f context="$2" -f description="$3" \
     -f target_url="$GITHUB_SERVER_URL/$GITHUB_REPOSITORY/actions/runs/$GITHUB_RUN_ID" >/dev/null 2>&1 || echo "status push failed"
  echo "STATUS $2 $1 $3"
}
push() {
  python3 - "$TRACK" "$K" "${1:-pending}" > /tmp/rep.txt <<'EOF'
import sys, json, os
track, k, final = sys.argv[1:4]
p = f'results/progress-{track}.json'
if not os.path.exists(p):
    print('pending'); print(f'c{k}: starting'); print('-'); sys.exit()
d = json.load(open(p)); c = d['counts']
ok = c.get('built', 0) + c.get('cached', 0); bad = c.get('failed', 0); blk = c.get('blocked', 0)
state = 'pending' if final != 'final' else ('failure' if bad else 'success')
desc = f"c{k}: {ok}/{d['total']} ok (new {c.get('built',0)}), {bad} failed, {blk} blocked" + (f" [{','.join(d['failed'][:3])}]" if bad else '')
diag = f"avail {d['memavail']}G | " + ', '.join(f'{m}({t//60}m,{r}G)' for m, t, r in sorted(d['running'], key=lambda x: -x[1])[:4])
print(state); print(desc[:139]); print(diag[:139])
EOF
  { read -r STATE; read -r DESC; read -r DIAG; } < /tmp/rep.txt
  post "$STATE" "n11/$TRACK" "$DESC"
  post pending "n11/$TRACK/diag" "$DIAG"
}
if [ "${3:-}" = "once" ]; then push final; exit 0; fi
sleep 120; push
while true; do sleep $INTERVAL; push; done
