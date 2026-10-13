"""Bounded no-window research process pool; only explicit branch commands."""
import os,sys,subprocess,json,time
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
ROOT=Path(__file__).resolve().parents[3]
P=ROOT/'research-2026/n12-global'
env=os.environ.copy();env['OPENBLAS_NUM_THREADS']='1';env['OMP_NUM_THREADS']='1'
def work(i):
    d=P/f'evidence/parallel-domain/branch-{i}.json'
    if d.exists() and not json.loads(d.read_bytes())['pending']:return (i,'already complete')
    with open(d.with_suffix('.hidden.log'),'a') as out,open(d.with_suffix('.hidden.err'),'a') as err:
        cmd=[sys.executable,'-B',str(P/'lead/run_domain_branch.py'),str(i)]
        p=subprocess.run(cmd,cwd=ROOT,env=env,stdout=out,stderr=err,creationflags=subprocess.CREATE_NO_WINDOW)
        return (i,p.returncode)
with ThreadPoolExecutor(max_workers=3) as pool:
    for result in pool.map(work,range(11)):print(result,flush=True)
