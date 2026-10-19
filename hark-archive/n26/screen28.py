"""Numerical screen (NOT proof) of the inferred root28 root box: 512 sub-boxes
(bisect the 9 wide axes once), model radius minimised by SLSQP (diag_open.solve,
no origin constraint) from centre + 2 random starts. Resumable: appends
screen28.jsonl per sub-box."""
import json, os, sys, itertools, numpy as np
from fractions import Fraction as F
from multiprocessing import Pool
import diag_open as dg
RS=0.2347000904004482396
B=json.load(open('/workspace/work/dcp-n26/root28_box_inferred.json'))
LO=np.array([float(F(x)) for x in B['lower']]); HI=np.array([float(F(x)) for x in B['upper']])
WIDE=[k for k in range(15) if HI[k]-LO[k]>1e-6]
OUT='/workspace/work/dcp-n26/screen28.jsonl'
def sub(code):
    lo=LO.copy(); hi=HI.copy()
    for bit,k in zip(code,WIDE):
        m=(LO[k]+HI[k])/2
        if bit: lo[k]=m
        else: hi[k]=m
    return lo,hi
def work(n):
    code=[(n>>i)&1 for i in range(len(WIDE))]; lo,hi=sub(code); rng=np.random.default_rng(n); best=None
    for s in range(3):
        th0=(lo+hi)/2 if s==0 else lo+(hi-lo)*rng.random(15)
        t,viol,z=dg.solve(lo,hi,None,th0)
        if viol<1e-10 and (best is None or t<best[0]): best=(t,z[:15].tolist())
    return {'n':n,'min_minus_Rstar':None if best is None else best[0]-RS,'theta':None if best is None else best[1]}
if __name__=='__main__':
    done=set()
    if os.path.exists(OUT):
        for l in open(OUT): done.add(json.loads(l)['n'])
    todo=[n for n in range(2**len(WIDE)) if n not in done]; print('todo',len(todo),flush=True)
    with Pool(int(os.environ.get('NP','2'))) as p, open(OUT,'a') as f:
        for r in p.imap_unordered(work,todo,chunksize=1): f.write(json.dumps(r)+'\n'); f.flush()
