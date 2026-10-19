"""Shared LOCAL-SLAB annulus forest about c*=theta*: A_m = cube(c*,rho_m) minus cube(c*,rho_{m+1}), rho_m=RHO0/2^m,
carved axis 0..14 (low side, then high side) exactly like lgeom. Every lgeom shell slab of level m>=0 that is not a
terminal slab (Q(m+1) empty) lies inside one shared slab of level m (map_slab checks containment exactly)."""
import sys
sys.path.insert(0,'/workspace/work/dcp-n26/v3replay')
import lgeom
from fractions import Fraction as F
C=lgeom.C; RHO0=lgeom.RHO0
def slabs(m):
    r0=RHO0/2**m; r1=r0/2
    lo=[c-r0 for c in C]; hi=[c+r0 for c in C]; out=[]
    for k in range(15):
        h=list(hi); h[k]=C[k]-r1; out.append((list(lo),h)); lo[k]=C[k]-r1
        l=list(lo); l[k]=C[k]+r1; out.append((l,list(hi))); hi[k]=C[k]+r1
    return out
_cache={}
def map_slab(m,lo,hi):
    if m not in _cache: _cache[m]=slabs(m)
    for s,(a,b) in enumerate(_cache[m]):
        if all(x<=y for x,y in zip(a,lo)) and all(x<=y for x,y in zip(hi,b)): return s
    return None
if __name__=='__main__':
    need={}
    for t in sys.argv[1:] or lgeom.OPEN23:
        tr,sl=lgeom.tree(t); term=0; miss=0
        for n,(m,lo,hi) in enumerate(sl):
            if m<0: continue
            s=map_slab(m,lo,hi)
            if s is None: term+=1
            else: need.setdefault(m,set()).add(s)
        print(t,'unmapped(terminal)',term)
    print({m:len(v) for m,v in sorted(need.items())}, sum(len(v) for v in need.values()))
