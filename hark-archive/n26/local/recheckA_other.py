"""Independent certA recheck of sampled node-28 LOCAL-SLAB leaf pieces (energy bound > 0). Resumable; appends to recheckA_other.jsonl."""
import os as _os, sys as _sys  # hark-archive portable paths (see hark-archive/_paths.py)
_hd = _os.path.dirname(_os.path.abspath(__file__))
while _os.path.basename(_hd) != 'hark-archive' and _os.path.dirname(_hd) != _hd: _hd = _os.path.dirname(_hd)
_sys.path.append(_hd); from _paths import DCP_N26
import json,glob,sys,time,os
from fractions import Fraction as F
import prop,certA
T0=time.time();BUD=float(sys.argv[1]);OUT=DCP_N26+'/local/recheckA_other.jsonl'
done=set()
if os.path.exists(OUT): done={tuple(json.loads(l)['k']) for l in open(OUT)}
fs=sorted(glob.glob(DCP_N26+'/v3replay/lleaves/*/s*.json'))
fs=[f for f in fs if '/lleaves/28/' not in f]
for f in fs:
    d=json.load(open(f));lo=[F(x) for x in d['lower']];hi=[F(x) for x in d['upper']]
    for i,p in enumerate(d['pieces']):
        k=(f.split('lleaves/')[1],i)
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
