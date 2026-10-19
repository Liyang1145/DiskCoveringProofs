"""certB independent recheck of close_missing_A pieces. Resumable. usage: recheckB_missing.py budget"""
import os as _os, sys as _sys  # hark-archive portable paths (see hark-archive/_paths.py)
_hd = _os.path.dirname(_os.path.abspath(__file__))
while _os.path.basename(_hd) != 'hark-archive' and _os.path.dirname(_hd) != _hd: _hd = _os.path.dirname(_hd)
_sys.path.append(_hd); from _paths import DCP_N26
import sys,os,json,time
sys.path.insert(0,DCP_N26+'/v3replay'); sys.path.insert(0,DCP_N26+'/local')
from fractions import Fraction as F
import prop,certB
D=DCP_N26+'/local/'; OUT=D+'recheckB_missing.jsonl'
d=json.load(open(D+'lleaf_boxes_missing.json'))['missing']
done=set()
if os.path.exists(OUT): done={json.loads(l)['leaf'] for l in open(OUT)}
T0=time.time();B=float(sys.argv[1]);n=0
for k in sorted(d,key=int):
    if k in done: continue
    if time.time()-T0>B: break
    rec=json.load(open(D+f'missing_closed/L{k}.json'))
    lo=[F(x) for x in d[k]['lo']];hi=[F(x) for x in d[k]['hi']];ok=rec['closed'];mb=None
    for p in rec['pieces']:
        if 'bound' not in p: ok=False;continue
        ba,bb=F(p['ba']),F(p['bb'])
        try: bd=certB.check_leaf(prop.weight((ba+bb)/2/prop.AA),lo,hi,ba,bb,prop.MU)
        except Exception as e: bd=None
        if bd is None or bd<=0: ok=False
        else: mb=bd if mb is None else min(mb,bd)
    open(OUT,'a').write(json.dumps({'leaf':k,'okB':bool(ok),'minB':None if mb is None else float(mb)})+'\n');n+=1
print(n,len(done)+n,len(d))
