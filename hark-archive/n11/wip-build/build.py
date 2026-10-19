#!/usr/bin/env python3
"""Resumable serial builder for the team WIP (Lean v4.33.1 + Mathlib cache on JuiceFS).
usage: build.py <phase|module-list-file|MOD=name> [budget_seconds]
phases: a25, pilot12_13, src14_36, all"""
import os as _os, sys as _sys  # hark-archive portable paths (see hark-archive/_paths.py)
_hd = _os.path.dirname(_os.path.abspath(__file__))
while _os.path.basename(_hd) != 'hark-archive' and _os.path.dirname(_hd) != _hd: _hd = _os.path.dirname(_hd)
_sys.path.append(_hd); from _paths import DCP_N11, LEAN_TOOLCHAIN
import json,os,sys,time,subprocess,hashlib
W=DCP_N11
SRC=W+'/wip/lean'; WB=W+'/wip-build'; OUT=WB+'/out'
TC=LEAN_TOOLCHAIN
LEDGER=WB+'/ledger.jsonl'; LOGD=WB+'/logs/mod'
os.makedirs(OUT,exist_ok=True); os.makedirs(LOGD,exist_ok=True)
env=dict(os.environ, LEAN_PATH=':'.join([TC+'/lib/lean',WB+'/mlib',OUT]), LEAN_NUM_THREADS='1', PATH=TC+'/bin:'+os.environ['PATH'])
plan=json.load(open(WB+'/plan.json'))
arg=sys.argv[1]; budget=float(sys.argv[2]) if len(sys.argv)>2 else 1100
if arg=='all': mods=plan['a25']+plan['pilot12_13']+plan['src14_36']
elif arg in plan: mods=plan[arg]
elif arg.startswith('MOD='): mods=arg[4:].split(',')
else: mods=open(arg).read().split()
def sha(p): return hashlib.sha256(open(p,'rb').read()).hexdigest()
green={}
if os.path.exists(LEDGER):
    for l in open(LEDGER):
        r=json.loads(l)
        if r.get('rc')==0: green[r['module']]=r['sha256']
def memavail():
    for l in open('/proc/meminfo'):
        if l.startswith('MemAvailable'): return int(l.split()[1])//1024
t0=time.time()
for m in mods:
    rel=m.replace('.','/'); src=f'{SRC}/{rel}.lean'; s=sha(src)
    olean=f'{OUT}/{rel}.olean'
    if green.get(m)==s and os.path.exists(olean): continue
    if time.time()-t0>budget: print('BUDGET STOP before',m); break
    while memavail()<1800: print('waiting for RAM',memavail(),flush=True); time.sleep(15)
    os.makedirs(os.path.dirname(olean),exist_ok=True)
    st=time.time(); peak=0
    with open(f'{LOGD}/{m}.out','w') as lf:
        p=subprocess.Popen(['nice','-n','10','lean','-j1','-M','3500','-R',SRC,'-o',olean,src],stdout=lf,stderr=subprocess.STDOUT,env=env,cwd=SRC)
        while p.poll() is None:
            try:
                for l in open(f'/proc/{p.pid}/task/{p.pid}/../../status'): pass
            except Exception: pass
            try:
                # child of nice is lean (exec), same pid
                for l in open(f'/proc/{p.pid}/status'):
                    if l.startswith('VmHWM'): peak=max(peak,int(l.split()[1])//1024)
            except Exception: pass
            time.sleep(1)
    rc=p.returncode; dt=round(time.time()-st,1)
    out=open(f'{LOGD}/{m}.out').read()
    errs=out.count('error')
    sorry='declaration uses \'sorry\'' in out
    row=dict(module=m,sha256=s,rc=rc,seconds=dt,peak_rss_mb=peak,errors_in_log=errs,sorry_warning=sorry,ts=time.strftime('%Y-%m-%d %H:%M:%S'),toolchain='v4.33.1-aarch64',mathlib='0df444a3')
    if rc==0 and sorry: row['rc_note']='compiled but sorry warning'
    open(LEDGER,'a').write(json.dumps(row)+'\n')
    print(json.dumps(row),flush=True)
    if rc!=0: print('FAIL',m); print(out[-3000:]); sys.exit(1)
print('phase done' if all(green.get(m) for m in []) else 'loop end', round(time.time()-t0))
