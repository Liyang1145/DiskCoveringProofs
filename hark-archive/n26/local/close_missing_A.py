"""certA closure of missing LOCAL-SLAB leaves (boxes from lleaf_boxes_missing.json). Resumable; usage: close_missing_A.py budget_s"""
import os as _os, sys as _sys  # hark-archive portable paths (see hark-archive/_paths.py)
_hd = _os.path.dirname(_os.path.abspath(__file__))
while _os.path.basename(_hd) != 'hark-archive' and _os.path.dirname(_hd) != _hd: _hd = _os.path.dirname(_hd)
_sys.path.append(_hd); from _paths import DCP_N26
import sys,os,json,time
sys.path.insert(0,DCP_N26+'/v3replay'); sys.path.insert(0,DCP_N26+'/local')
from fractions import Fraction as F
import prop, lgeom
from run_local import piece
OUT=DCP_N26+'/local/missing_closed'; os.makedirs(OUT,exist_ok=True)
d=json.load(open(DCP_N26+'/local/lleaf_boxes_missing.json'))['missing']
T0=time.time();B=float(sys.argv[1]);n=0;bad=0
for k in sorted(d,key=int):
    fn=f'{OUT}/L{k}.json'
    if os.path.exists(fn): continue
    if time.time()-T0>B: break
    lo=[F(x) for x in d[k]['lo']]; hi=[F(x) for x in d[k]['hi']]
    b1,b2=prop.brange(lo,hi); rho=lgeom.RHO0/F(2)**0  # rho scale only for K; refined by depth
    K=4; acc=[]; ok=True
    for i in range(K): ok&=piece(lo,hi,b1+(b2-b1)*i/K,b1+(b2-b1)*(i+1)/K,0,acc)
    mb=min((F(p['bound']) for p in acc if 'bound' in p),default=None)
    rec={'leaf':k,'closed':bool(ok),'npieces':len(acc),'min_bound':str(mb),'pieces':acc}
    json.dump(rec,open(fn+'.tmp','w')); os.replace(fn+'.tmp',fn); n+=1; bad+=(not ok)
    open(DCP_N26+'/ledger.jsonl','a').write(json.dumps({'event':'missA','leaf':k,'closed':bool(ok),'np':len(acc),'t':time.time()})+'\n')
print(json.dumps({'done_now':n,'bad_now':bad,'have':len(os.listdir(OUT)),'of':len(d)}))
