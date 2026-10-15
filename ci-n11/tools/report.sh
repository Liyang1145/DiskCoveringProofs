#!/usr/bin/env bash
# Progress reporter via commit statuses (context n11/<track>) on $GITHUB_SHA — no branch writes.
# usage: tools/report.sh <track> <chunk> [once]     (run from ci-n11/, needs GH_TOKEN with statuses:write)
TRACK=$1; K=$2; INTERVAL=${INTERVAL:-600}
push() {
  read -r STATE DESC < <(python3 - "$TRACK" "$K" "${1:-pending}" <<'EOF'
import sys, glob, os, re
track, k, final = sys.argv[1], sys.argv[2], sys.argv[3]
logs = sorted(glob.glob(f'results/logs/{track}-c{k}-*.log'), key=os.path.getmtime)
ok = 0; bad = []; grp = '-'
for L in logs:
    grp = os.path.basename(L)[len(f'{track}-c{k}-'):-4]
    for l in open(L, errors='replace'):
        if re.match(r'^(✔|⚠)\s*\[', l): ok += 1
        elif l.startswith('✖'):
            m = re.search(r'\]\s+\S+\s+(\S+)', l); bad.append(m.group(1).replace('N11Formalization.', '') if m else '?')
state = 'pending'
if final == 'final': state = 'failure' if bad else 'success'
d = f'c{k} {grp}: {ok} ok, {len(bad)} failed' + (f' [{",".join(bad[:3])}]' if bad else '')
print(state, d[:139])
EOF
)
  gh api -X POST "repos/$GITHUB_REPOSITORY/statuses/$GITHUB_SHA" -f state="$STATE" -f context="n11/$TRACK" \
     -f description="$DESC" -f target_url="$GITHUB_SERVER_URL/$GITHUB_REPOSITORY/actions/runs/$GITHUB_RUN_ID" >/dev/null 2>&1 \
     || echo "status push failed"
  echo "STATUS n11/$TRACK $STATE $DESC"
}
if [ "${3:-}" = "once" ]; then push final; exit 0; fi
sleep 120; push
while true; do sleep $INTERVAL; push; done
