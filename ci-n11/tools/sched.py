#!/usr/bin/env python3
"""Memory-aware parallel builder for the N11Formalization tree (replaces `lake build`, which OOM-killed
the 16 GB runner with 4 parallel heavy Lean processes).
usage (cwd = ci-n11/lean, after `lake exe cache get` and draft injection):
  sched.py <track> <chunk> <deadline-epoch> <results-dir> <group>=<targets.txt> [...]
Compiles each needed module with `lean -R . -o .lake/build/lib/lean/<p>.olean -i <p>.ilean <p>.lean`
(LEAN_PATH from `lake env`), so `lake env lean` (audit) sees the outputs. Up-to-date check: stamp =
sha256(source + stamps of N11 imports), stored next to the olean (.n11stamp). Writes <results>/<track>-c<k>.jsonl
rows {group,module,status,seconds,peak_rss_mb,sorry,errors,warnings}, progress JSON for report.sh,
per-module logs for failures/sorry. Exit code 0 = everything reached a final state, 3 = deadline/unfinished."""
import os, sys, json, time, hashlib, subprocess, re, signal
track, chunk, deadline, RES = sys.argv[1], sys.argv[2], float(sys.argv[3]), sys.argv[4]
groups = [(a.split('=', 1)[0], open(a.split('=', 1)[1]).read().split()) for a in sys.argv[5:]]
OUT = '.lake/build/lib/lean'
os.makedirs(f'{RES}/logs/mod', exist_ok=True)
LEAN_PATH = subprocess.run(['lake', 'env', 'printenv', 'LEAN_PATH'], capture_output=True, text=True).stdout.strip()
env = dict(os.environ, LEAN_PATH=LEAN_PATH)
MAXW = int(os.environ.get('N11_WORKERS', '4'))
PEAKS_F = f'{OUT}/n11-peaks.json'
peaks = json.load(open(PEAKS_F)) if os.path.exists(PEAKS_F) else {}
src = lambda m: m.replace('.', '/') + '.lean'
imports = {}
def imps(m):
    if m not in imports:
        imports[m] = [l.split()[1] for l in open(src(m), errors='replace') if l.startswith('import ')
                      and l.split()[1].startswith('N11Formalization') and os.path.exists(src(l.split()[1]))] \
            if os.path.exists(src(m)) else []
    return imports[m]
stamps = {}
def stamp(m):
    if m not in stamps:
        h = hashlib.sha256(open(src(m), 'rb').read())
        for i in sorted(imps(m)): h.update(stamp(i).encode())
        stamps[m] = h.hexdigest()
    return stamps[m]
owner = {}; order = []
for g, tg in groups:
    st = [t for t in tg if os.path.exists(src(t))]
    for t in tg:
        if not os.path.exists(src(t)): print('missing source for target', t)
    seen = set()
    def visit(m):
        if m in seen: return
        seen.add(m)
        for i in imps(m): visit(i)
        if m not in owner: owner[m] = g; order.append(m)
    for t in st: visit(t)
prio = {m: i for i, m in enumerate(order)}
state = {}  # module -> cached|built|failed|blocked|killed
for m in order:
    o = f'{OUT}/{m.replace(".", "/")}'
    if os.path.exists(o + '.olean') and os.path.exists(o + '.n11stamp') and open(o + '.n11stamp').read() == stamp(m):
        state[m] = 'cached'
    elif os.path.exists(o + '.n11fail') and open(o + '.n11fail').read() == stamp(m):
        state[m] = 'failed_cached'
rows = open(f'{RES}/{track}-c{chunk}.jsonl', 'a')
def emit(m, st, **kw):
    state[m] = st
    r = dict(group=owner[m], module=m, status=st, **kw); rows.write(json.dumps(r) + '\n'); rows.flush()
    if st != 'cached': print(json.dumps(r), flush=True)
for m in order:
    if state.get(m) == 'cached': emit(m, 'cached')
    elif state.get(m) == 'failed_cached': emit(m, 'failed', note='same stamp failed in an earlier chunk; not retried')
def memavail():
    for l in open('/proc/meminfo'):
        if l.startswith('MemAvailable'): return int(l.split()[1]) / 2**20
running = {}  # m -> (Popen, t0, logfile, peak)
solo = set()
def ready(m):
    return m not in state and m not in running and all(state.get(i) in ('cached', 'built') for i in imps(m))
def propagate_block():
    ch = True
    while ch:
        ch = False
        for m in order:
            if m not in state and m not in running and any(state.get(i) in ('failed', 'blocked') for i in imps(m)):
                emit(m, 'blocked', blocked_by=[i for i in imps(m) if state.get(i) in ('failed', 'blocked')][:3]); ch = True
def progress():
    c = {}
    for m in order: c[state.get(m, 'running' if m in running else 'todo')] = c.get(state.get(m, 'running' if m in running else 'todo'), 0) + 1
    p = dict(track=track, chunk=chunk, ts=time.time(), counts=c, total=len(order),
             running=[(m.replace('N11Formalization.', ''), int(time.time() - v[1]), round(v[3] / 1024, 1)) for m, v in running.items()],
             failed=[m.replace('N11Formalization.', '') for m in order if state.get(m) == 'failed'][:20],
             memavail=round(memavail(), 1))
    json.dump(p, open(f'{RES}/progress-{track}.json.tmp', 'w')); os.replace(f'{RES}/progress-{track}.json.tmp', f'{RES}/progress-{track}.json')
def start(m):
    o = f'{OUT}/{m.replace(".", "/")}'
    os.makedirs(os.path.dirname(o), exist_ok=True)
    for ext in ('.olean', '.ilean', '.n11stamp'):
        if os.path.exists(o + ext): os.remove(o + ext)
    lf = open(f'{RES}/logs/mod/{m}.out', 'w')
    p = subprocess.Popen(['lean', '-R', '.', '-o', o + '.olean', '-i', o + '.ilean', src(m)], stdout=lf, stderr=subprocess.STDOUT, env=env)
    running[m] = [p, time.time(), lf, 0]
def finish(m, killed=False):
    p, t0, lf, peak = running.pop(m); lf.close()
    dt = round(time.time() - t0, 1)
    logp = f'{RES}/logs/mod/{m}.out'; txt = open(logp, errors='replace').read()
    sorry = "declaration uses 'sorry'" in txt
    errs = len(re.findall(r'(^|: )error:', txt, re.M)); warns = len(re.findall(r'(^|: )warning:', txt, re.M))
    peaks[m] = max(peaks.get(m, 0), peak)
    if killed:
        state.pop(m, None); print(f'KILLED (memory) {m} after {dt}s, peak {peak/1024:.1f} GB; requeued solo', flush=True)
        solo.add(m); return
    if p.returncode == 0:
        o = f'{OUT}/{m.replace(".", "/")}'
        open(o + '.n11stamp', 'w').write(stamp(m))
        emit(m, 'built', seconds=dt, peak_rss_mb=peak, sorry=sorry, errors=errs, warnings=warns)
        if not sorry and warns == 0 and not re.search(r'#print|info:', txt): os.remove(logp)
    else:
        emit(m, 'failed', seconds=dt, peak_rss_mb=peak, sorry=sorry, errors=errs, warnings=warns, rc=p.returncode)
        if p.returncode > 0: open(f'{OUT}/{m.replace(".", "/")}.n11fail', 'w').write(stamp(m))
        print(txt[-2500:], flush=True)
last_prog = 0; unfinished = False
while True:
    propagate_block()
    for m in list(running):
        p = running[m][0]
        try:
            for l in open(f'/proc/{p.pid}/status'):
                if l.startswith('VmRSS'): running[m][3] = max(running[m][3], int(l.split()[1]) // 1024)
        except Exception: pass
        if p.poll() is not None: finish(m)
    if time.time() > deadline:
        for m in list(running):
            running[m][0].kill(); running[m][0].wait(); finish(m, killed=True)
        unfinished = any(m not in state for m in order); break
    av = memavail()
    if av < 1.5 and len(running) > 1:  # memory emergency: kill the youngest
        y = max(running, key=lambda k: running[k][1]); running[y][0].kill(); running[y][0].wait(); finish(y, killed=True)
    rd = sorted([m for m in order if ready(m)], key=lambda m: prio[m])
    if rd and len(running) < MAXW:
        m = rd[0]
        need = max(2.5, peaks.get(m, 2500) / 1024 * 1.15)
        if (m in solo and not running) or (m not in solo and not any(r in solo for r in running) and (not running or av > need + 1.0)):
            start(m); time.sleep(1); continue
        # a solo module waits until the machine is empty; let others drain
    if not running and not rd:
        propagate_block(); break
    if time.time() - last_prog > 30: progress(); last_prog = time.time()
    time.sleep(2)
progress()
json.dump(peaks, open(PEAKS_F, 'w'))
c = {}
for m in order: c[state.get(m, 'todo')] = c.get(state.get(m, 'todo'), 0) + 1
print('SCHED', track, 'chunk', chunk, json.dumps(c), 'unfinished' if unfinished else 'complete', flush=True)
sys.exit(3 if unfinished else 0)
