import os as _os, sys as _sys  # hark-archive portable paths (see hark-archive/_paths.py)
_hd = _os.path.dirname(_os.path.abspath(__file__))
while _os.path.basename(_hd) != 'hark-archive' and _os.path.dirname(_hd) != _hd: _hd = _os.path.dirname(_hd)
_sys.path.append(_hd); from _paths import DCP_N26
import sys,os,json,time
import bnb, lgeom
os.makedirs('fleaves',exist_ok=True)
T0=time.time(); BUD=float(sys.argv[1])
for t in sys.argv[2:]:
    tr,sl=lgeom.tree(t)
    for n,(m,lo,hi) in enumerate(sl):
        if m>=0: continue
        p=f'fleaves/{t}_s{n}.json'
        if os.path.exists(p) and json.load(open(p))['done']: continue
        left=BUD-(time.time()-T0)
        if left<5: print('budget stop'); sys.exit(0)
        r=bnb.run(t,left,path=p,box=(lo,hi)); r['slab']=n
        print(json.dumps(r),flush=True)
        with open(DCP_N26+'/ledger.jsonl','a') as f: f.write(json.dumps({'event':'v3-outer-force',**r,'t':time.time()})+'\n')
print('ALL DONE')
