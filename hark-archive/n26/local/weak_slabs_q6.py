"""Exact ranking of weakest FOREST-Q6 slabs by min bound/rho_m^2 (rho_m=rho_0/2^m); writes weak_slabs_q6.json."""
import os as _os, sys as _sys  # hark-archive portable paths (see hark-archive/_paths.py)
_hd = _os.path.dirname(_os.path.abspath(__file__))
while _os.path.basename(_hd) != 'hark-archive' and _os.path.dirname(_hd) != _hd: _hd = _os.path.dirname(_hd)
_sys.path.append(_hd); from _paths import DCP_N26
import json
from fractions import Fraction as F
d=json.load(open(DCP_N26+'/local/FOREST-Q6.json'))
print(d['shells'] if len(str(d['shells']))<600 else str(d['shells'])[:600])
rows=[]
for s in d['slabs']:
    m=int(s['m']); mb=min(F(p['bound']) for p in s['pieces'])
    rows.append((mb,m,s['slab'],len(s['pieces'])))
rows.sort()
json.dump([[float(a),m,sl,n] for a,m,sl,n in rows[:30]],open(DCP_N26+'/local/weak_slabs_q6.json','w'))
for a,m,sl,n in rows[:8]: print(m,sl,n,float(a))
