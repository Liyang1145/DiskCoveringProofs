"""Exact-rational structural check of node-28's 218 LOCAL-SLAB leaves: box nonempty, closed,
pieces contiguous & span b_range, all bounds>0. Does not redo energy bounds."""
import os as _os, sys as _sys  # hark-archive portable paths (see hark-archive/_paths.py)
_hd = _os.path.dirname(_os.path.abspath(__file__))
while _os.path.basename(_hd) != 'hark-archive' and _os.path.dirname(_hd) != _hd: _hd = _os.path.dirname(_hd)
_sys.path.append(_hd); from _paths import DCP_N26
import json,glob
from fractions import Fraction as F
bad=[];n=0;np_=0;mn=None
for f in sorted(glob.glob(DCP_N26+'/v3replay/lleaves/*/s*.json')):
    s=json.load(open(f));n+=1;t=s['slab']
    lo=[F(x) for x in s['lower']];hi=[F(x) for x in s['upper']]
    if not all(a<b for a,b in zip(lo,hi)):bad.append((t,'box'))
    if s['closed'] not in (True,'True'):bad.append((t,'open'))
    P=s['pieces'];np_+=len(P);a0,b0=[F(x) for x in s['b_range']]
    if F(P[0]['ba'])!=a0 or F(P[-1]['bb'])!=b0:bad.append((t,'span'))
    for p,q in zip(P,P[1:]):
        if F(p['bb'])!=F(q['ba']):bad.append((t,'gap'))
    for p in P:
        if not F(p['ba'])<F(p['bb']):bad.append((t,'empty'))
        b=F(p['bound'])
        if b<=0:bad.append((t,'nonpos'))
        mn=b if mn is None else min(mn,b)
print('ALL-SUBTREES leaves',n,'pieces',np_,'min',float(mn));print('PASS' if not bad else 'FAIL %s'%bad[:5])
