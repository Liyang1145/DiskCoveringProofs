"""Enumerate exact finite-witness capture masks; no set-cover claim.

Input JSON: {"radius":"9/40", "points":[["x","y"], ...]}.
All coordinates and the radius are exact rationals.  Output is a collection
of realizable masks, one for each witness-center and each equal-radius pair
intersection; duplicates and subset masks are allowed.  Python -O forbidden.
"""
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
import hashlib
import json
import sys

if not __debug__:
    raise RuntimeError('Assertions must be enabled')

def sign(a,b,d):
    """Exact sign of a+b*sqrt(d), d nonnegative rational."""
    if d<0: raise ValueError('negative radical')
    if b==0 or d==0: return (a>0)-(a<0)
    if a==0: return (b>0)-(b<0)
    sa=(a>0)-(a<0); sb=(b>0)-(b<0)
    if sa==sb: return sa
    delta=a*a-b*b*d
    return sa*((delta>0)-(delta<0))

def dot(a,b): return a[0]*b[0]+a[1]*b[1]
def subtract(a,b): return a[0]-b[0],a[1]-b[1]

def generate(data):
    r=F(data['radius'])
    if r<=0: raise ValueError('radius must be strictly positive')
    points=[tuple(F(v) for v in xy) for xy in data['points']]
    if not points or any(len(p)!=2 for p in points): raise ValueError('empty or malformed witness list')
    if len(set(points))!=len(points): raise ValueError('duplicate witness points')
    if any(dot(p,p)>1 for p in points): raise ValueError('witness outside unit disk')
    masks=set()
    point_count=pair_count=tangent_count=0
    for center in points:
        mask=sum(1<<k for k,w in enumerate(points) if dot(subtract(w,center),subtract(w,center))<=r*r)
        masks.add(mask);point_count+=1
    for i,j in combinations(range(len(points)),2):
        p,q=points[i],points[j]
        v=subtract(q,p);length2=dot(v,v)
        if length2>4*r*r: continue
        midpoint=((p[0]+q[0])/2,(p[1]+q[1])/2)
        perp=(-v[1],v[0]);radicand=r*r/length2-F(1,4)
        signs=(0,) if radicand==0 else (1,-1)
        if radicand==0:tangent_count+=1
        for orientation in signs:
            mask=0
            for k,w in enumerate(points):
                difference=subtract(midpoint,w)
                a=dot(difference,difference)+radicand*length2-r*r
                b=orientation*2*dot(difference,perp)
                if sign(a,b,radicand)<=0: mask|=1<<k
            if not ((mask>>i)&1 and (mask>>j)&1):
                raise ValueError('pair endpoint not contained in its own disks')
            masks.add(mask);pair_count+=1
    return {'point_count':len(points),'radius':str(r),'witness_center_candidates':point_count,
            'pair_center_candidates':pair_count,'tangent_pairs':tangent_count,
            'masks_hex':sorted(hex(m) for m in masks)}

def main():
    if len(sys.argv)!=2: raise SystemExit('usage: exact_masks.py WITNESSES.json')
    path=Path(sys.argv[1]); raw=path.read_bytes()
    data=json.loads(raw); result=generate(data)
    result['input_sha256']=hashlib.sha256(raw).hexdigest()
    result['schema']='n26-finite-witness-exact-masks-v1'
    result['global_lower_bound_proved']=False
    print(json.dumps(result,indent=2))

if __name__=='__main__': main()
