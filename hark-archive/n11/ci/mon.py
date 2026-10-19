#!/usr/bin/env python3
"""Monitor n11 CI on Liyang1145/DiskCoveringProofs branch ci/n11-build (run in shell with github credentials).
usage: mon.py            -> runs + jobs (with failed step) + commit statuses of branch head
       mon.py log <job>  -> print tail of a finished job's log
       mon.py art <run>  -> download all artifacts of a run into ci/artifacts/<run>/"""
import os as _os, sys as _sys  # hark-archive portable paths (see hark-archive/_paths.py)
_hd = _os.path.dirname(_os.path.abspath(__file__))
while _os.path.basename(_hd) != 'hark-archive' and _os.path.dirname(_hd) != _hd: _hd = _os.path.dirname(_hd)
_sys.path.append(_hd); from _paths import DCP_N11
import json, subprocess, sys, os
API = 'https://api.github.com/repos/Liyang1145/DiskCoveringProofs'
def get(u, raw=False):
    out = subprocess.run(['curl', '-sL', u if u.startswith('http') else API + u], capture_output=True).stdout
    return out if raw else json.loads(out)
if len(sys.argv) > 2 and sys.argv[1] == 'log':
    txt = get(f'/actions/jobs/{sys.argv[2]}/logs', raw=True).decode(errors='replace')
    n = int(sys.argv[3]) if len(sys.argv) > 3 else 120
    print('\n'.join(txt.splitlines()[-n:])); sys.exit()
if len(sys.argv) > 2 and sys.argv[1] == 'art':
    run = sys.argv[2]; d = f'{DCP_N11}/ci/artifacts/{run}'; os.makedirs(d, exist_ok=True)
    for a in get(f'/actions/runs/{run}/artifacts?per_page=100')['artifacts']:
        z = f'{d}/{a["name"]}.zip'
        open(z, 'wb').write(get(a['archive_download_url'], raw=True))
        subprocess.run(['unzip', '-oq', z, '-d', f'{d}/{a["name"]}']); print('got', a['name'], a['size_in_bytes'])
    sys.exit()
runs = get('/actions/runs?branch=ci/n11-build&per_page=15')['workflow_runs']
for r in runs:
    if not r['name'].startswith('n11-'): continue
    print(f"RUN {r['id']} {r['name']} {r['status']} {r['conclusion']} {r['head_sha'][:7]} {r['created_at']}")
    if r['status'] == 'completed' and r is not runs[0] and len(sys.argv) < 2: pass
    for j in get(f"/actions/runs/{r['id']}/jobs?per_page=50")['jobs']:
        if j['status'] == 'completed' and j['conclusion'] == 'skipped': continue
        cur = [s['name'] for s in j.get('steps', []) if s['status'] == 'in_progress']
        bad = [s['name'] for s in j.get('steps', []) if s.get('conclusion') == 'failure']
        print(f"   job {j['id']} {j['name']} {j['status']} {j['conclusion']} start={j['started_at']} now={cur} failed={bad}")
shas = []
for r in runs:
    if r['name'].startswith('n11-') and r['head_sha'] not in shas: shas.append(r['head_sha'])
for head in shas[:3]:
    seen = set()
    for s in get(f'/commits/{head}/statuses?per_page=100'):
        if s['context'] in seen: continue
        seen.add(s['context']); print('STATUS', head[:7], s['context'], s['state'], s['description'], s['updated_at'])
