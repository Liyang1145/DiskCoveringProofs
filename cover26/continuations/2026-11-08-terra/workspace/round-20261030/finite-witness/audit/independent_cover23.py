"""Recompute the 23 explicit finite-sample masks with rational radicals."""
from fractions import Fraction as F
from pathlib import Path
import json
from exact_masks import sign, dot, subtract

folder=Path(__file__).resolve().parents[1]/'geometry'
data=json.loads((folder/'five_ring_exact.json').read_text(encoding='utf8'))
sol=json.loads((folder/'finite_cover_23.json').read_text(encoding='utf8'))
pts=[tuple(map(F,p)) for p in data['points']];r=F('9/40')
if data['radius']!='9/40' or sol['radius']!='9/40' or len(pts)!=241:
    raise ValueError('invalid sample or radius')
if any(dot(p,p)>1 for p in pts):raise ValueError('outside unit disk')
records=sol['selected_witnesses']; claimed=sol['selected_masks']
if len(records)!=23 or len(claimed)!=23:raise ValueError('incomplete centers')
allmask=0
for expected,record in zip(claimed,records):
    i=record['i'];p=pts[i];mask=0
    if record['kind']=='point':
        for k,w in enumerate(pts):
            z=subtract(p,w)
            if dot(z,z)<=r*r:mask|=1<<k
    elif record['kind']=='pair':
        j=record['j']; orientation=record['sign'];q=pts[j]
        if i==j or orientation not in (-1,1):raise ValueError('invalid pair')
        v=subtract(q,p);L=dot(v,v)
        if L<=0 or L>4*r*r:raise ValueError('circles do not intersect')
        mid=((p[0]+q[0])/2,(p[1]+q[1])/2);perp=(-v[1],v[0]);D=r*r/L-F(1,4)
        for k,w in enumerate(pts):
            z=subtract(mid,w)
            if sign(dot(z,z)+D*L-r*r,orientation*2*dot(z,perp),D)<=0:mask|=1<<k
    else:raise ValueError('invalid kind')
    if mask!=int(expected,16):raise ValueError('claimed mask differs from exact mask')
    allmask |= mask
if allmask!=(1<<len(pts))-1:raise ValueError('not all sample points covered')
print('PASS 241 exact points covered by 23 explicit radius-9/40 disks')
