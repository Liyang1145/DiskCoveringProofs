"""Independent certA recheck of sampled node-28 LOCAL-SLAB leaf pieces (energy bound > 0). Resumable; appends to recheck28_all.jsonl."""
import json,glob,sys,time,os
from fractions import Fraction as F
import prop,certA
T0=time.time();BUD=float(sys.argv[1]);OUT='/workspace/work/dcp-n26/local/recheck28_all.jsonl'
done=set()
if os.path.exists(OUT): done={tuple(json.loads(l)['k']) for l in open(OUT)}
fs=sorted(glob.glob('/workspace/work/dcp-n26/v3replay/lleaves/28/s*.json'))
for f in fs:
    d=json.load(open(f));lo=[F(x) for x in d['lower']];hi=[F(x) for x in d['upper']]
    for i,p in enumerate(d['pieces']):
        k=(d['slab'],i)
        if k in done: continue
        if time.time()-T0>BUD: sys.exit()
        pass
        ba,bb=F(p['ba']),F(p['bb']);kap=(ba+bb)/2/prop.AA
        r={'k':list(k),'keys':list(p)}
        try:
            bd,_=certA.leaf_bound(prop.weight(kap),lo,hi,prop.V,ba,bb,F(d['mu']))
            r['ok']=bool(bd is not None and bd>0);r['bound']=None if bd is None else float(bd)
        except Exception as e: r['ok']=False;r['err']=str(e)[:100]
        open(OUT,'a').write(json.dumps(r)+'\n')
