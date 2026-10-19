#!/usr/bin/env python3
# build one core module: argv[1] = EnergyReplay/X ; oleans in $DCP_TMP/en; append logs/core-build.jsonl
import os as _os, sys as _sys  # hark-archive portable paths (see hark-archive/_paths.py)
_hd = _os.path.dirname(_os.path.abspath(__file__))
while _os.path.basename(_hd) != 'hark-archive' and _os.path.dirname(_hd) != _hd: _hd = _os.path.dirname(_hd)
_sys.path.append(_hd); from _paths import DCP_N11, DCP_TMP, LEAN
import sys, os, subprocess, time, resource, hashlib, json, shutil
M = sys.argv[1]
H = DCP_N11+'/energy'; SRC = f'{H}/lean-core/{M}.lean'; OUT = f'{DCP_TMP}/en/{M}.olean'
os.makedirs(os.path.dirname(OUT), exist_ok=True); os.makedirs(f'{H}/logs', exist_ok=True)
shutil.copy(SRC, f'{DCP_TMP}/en/{M}.lean')
t = time.time()
p = subprocess.run(['nice', '-n', '10', LEAN, '-o', OUT + '.part', M + '.lean'], cwd=DCP_TMP+'/en',
                   env=dict(os.environ, LEAN_PATH=DCP_TMP+'/en'), capture_output=True, text=True,
                   timeout=float(os.environ.get('TMO', '1100')))
rc = p.returncode; dt = round(time.time() - t, 1)
rss = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
if rc == 0: os.replace(OUT + '.part', OUT)
n = M.replace('/', '.')
open(f'{H}/logs/{n}.out', 'w').write(p.stdout + p.stderr)
row = dict(module=n, rc=rc, seconds=dt, maxrss_kb=rss, src_sha256=hashlib.sha256(open(SRC, 'rb').read()).hexdigest(),
           utc=time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()))
open(f'{H}/logs/core-build.jsonl', 'a').write(json.dumps(row) + '\n'); print(json.dumps(row)); print((p.stdout + p.stderr)[:1500])
sys.exit(rc)
