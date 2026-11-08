"""Exhibit an exact uncovered point for the smaller radius, same coordinates."""
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
import json

p=Path(__file__).resolve().parent / 'n26-origin-certificate.json'
data=json.loads(p.read_text(encoding='utf8'))
c=[tuple(map(F,xy)) for xy in data['centers']]
r=F('0.234700090')
def norm2(p): return p[0]*p[0]+p[1]*p[1]
def sub(a,b): return a[0]-b[0], a[1]-b[1]

for i,j,k in combinations(range(len(c)),3):
    a,b,z=c[i],c[j],c[k]
    u,v=sub(b,a),sub(z,a)
    determinant=2*(u[0]*v[1]-u[1]*v[0])
    if not determinant: continue
    h=norm2(b)-norm2(a); g=norm2(z)-norm2(a)
    x=((h*v[1]-g*u[1])/determinant,(u[0]*g-v[0]*h)/determinant)
    if norm2(x)>1: continue
    distances=[norm2(sub(x,q)) for q in c]
    if min(distances)>r*r:
        nearest=min(distances)
        print('indices, zero-based:',i,j,k)
        print('witness coordinates:',x[0],x[1])
        print('nearest center indices:',[i for i,d in enumerate(distances) if d==nearest])
        print('nearest distance squared minus r squared:',nearest-r*r)
        archived_upper=F('0.234700090400448239616790133776692127560495963654971391785925')
        if nearest <= archived_upper**2:
            raise RuntimeError('selected witness does not exceed archived root upper bound')
        print('nearest distance squared minus archived candidate upper squared:',nearest-archived_upper**2)
        print('witness radius squared:',norm2(x))
        break
else:
    raise RuntimeError('no strictly uncovered witness found')
