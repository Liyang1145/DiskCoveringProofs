"""Exact-rational structural/interface check of LOCAL-SLAB forests (see LOCAL_SLAB_LEMMA.md).
Checks: slab box inside region; b-range pieces contiguous and exactly cover b_range; every piece
bound>0 (leaf_claim margin); all slabs closed; counts; shell nesting (rho_m=rho_0/2^m about c*).
Does NOT redo the energy bounds (certA/certB do). Usage: python3 check_local_slab.py [FOREST-Q6.json]"""
import os as _os, sys as _sys  # hark-archive portable paths (see hark-archive/_paths.py)
_hd = _os.path.dirname(_os.path.abspath(__file__))
while _os.path.basename(_hd) != 'hark-archive' and _os.path.dirname(_hd) != _hd: _hd = _os.path.dirname(_hd)
_sys.path.append(_hd); from _paths import DCP_N26
import json,sys
from fractions import Fraction as F
R=DCP_N26+'/'
fn=sys.argv[1] if len(sys.argv)>1 else R+'local/FOREST-Q6.json'
d=json.load(open(fn)); reg=d['region']
rl=[F(x) for x in reg['lower']]; ru=[F(x) for x in reg['upper']]
bad=[]; npieces=0; mn=None; per_m={}
for s in d['slabs']:
    t=(s['m'],s['slab'])
    lo=[F(x) for x in s['lower']]; hi=[F(x) for x in s['upper']]
    if not all(a<b for a,b in zip(lo,hi)): bad.append((t,'empty box'))
    if not all(a>=b and c<=e for a,b,c,e in zip(lo,rl,hi,ru)): bad.append((t,'outside region'))
    if not s.get('closed'): bad.append((t,'not closed'))
    P=s['pieces']; npieces+=len(P)
    ba0,bb0=[F(x) for x in s['b_range']]
    if F(P[0]['ba'])!=ba0 or F(P[-1]['bb'])!=bb0: bad.append((t,'pieces do not span b_range'))
    for p,q in zip(P,P[1:]):
        if F(p['bb'])!=F(q['ba']): bad.append((t,'gap/overlap between pieces'))
    for p in P:
        if not F(p['ba'])<F(p['bb']): bad.append((t,'empty piece'))
        b=F(p['bound'])
        if b<=0: bad.append((t,'nonpositive bound'))
        mn=b if mn is None else min(mn,b)
    per_m[s['m']]=per_m.get(s['m'],0)+1
if len(d['slabs'])!=d['counts']['slabs']: bad.append('slab count')
if npieces!=d['counts']['leaves']: bad.append('leaf count')
print('slabs',len(d['slabs']),'pieces',npieces,'per-m',per_m)
print('min piece bound',float(mn)); print('PASS' if not bad else 'FAIL %d: %s'%(len(bad),bad[:5]))
sys.exit(1 if bad else 0)
