"""Shell skeleton for box 1669 around the archive pinning cell C.
c = rational midpoint of C; Q_0 = C ∩ 1669 (LOCAL-PINNING-CELL leaf);
Q_j = ([c-rho_j, c+rho_j] ∩ 1669) on the 9 wide axes (thin axes 0..5 untouched),
rho_j = 2^j * 1e-7 for j>=1 until Q_J = 1669.  Q_{j+1} \\ Q_j is cut by exact
closed SPLITs axis by axis into slabs; each slab is an energy job."""
import os as _os, sys as _sys  # hark-archive portable paths (see hark-archive/_paths.py)
_hd = _os.path.dirname(_os.path.abspath(__file__))
while _os.path.basename(_hd) != 'hark-archive' and _os.path.dirname(_hd) != _hd: _hd = _os.path.dirname(_hd)
_sys.path.append(_hd); from _paths import DCP_N26
import json
from fractions import Fraction as F
ROOT=DCP_N26
PROP=ROOT+'/repo/cover26/proof_bundle/work/n26-refined-anchor-pinning-broad-proposal-v2.json'
CELL=[(F(a),F(b)) for a,b in json.load(open(PROP))['closed_anchor_angle_cells']]
B=[b for b in json.load(open(ROOT+'/pending.json'))['pending_closed_leaf_boxes'] if b['index']==1669][0]
LO=[F(x) for x in B['lower']]; HI=[F(x) for x in B['upper']]
C=[(a+b)/2 for a,b in CELL]
def Q(j):
    if j==0: return [max(l,a) for l,(a,b) in zip(LO,CELL)],[min(h,b) for h,(a,b) in zip(HI,CELL)]
    r=F(2**j,10**7)
    lo=[max(LO[k],C[k]-r) if k>=6 else LO[k] for k in range(15)]
    hi=[min(HI[k],C[k]+r) if k>=6 else HI[k] for k in range(15)]
    return lo,hi
def levels():
    J=1
    while Q(J)!=(LO,HI): J+=1
    return J
def skeleton(stop=0):
    J=levels(); slabs=[]
    for k in range(6):
        assert CELL[k][0]<=LO[k] and HI[k]<=CELL[k][1]
    for j in range(J):
        qi,qo=Q(j),Q(j+1)
        assert all(a<=b for a,b in zip(qo[0],qi[0])) and all(a>=b for a,b in zip(qo[1],qi[1]))
    def build(j,lo,hi,k):
        # lo,hi == current box (subset of Q_{j+1}); carve Q_j out of it
        if j<0: raise AssertionError
        ilo,ihi=Q(j)
        while k<15 and lo[k]>=ilo[k] and hi[k]<=ihi[k]: k+=1
        if k==15:
            if j==0: return {'kind':'LOCAL-PINNING-CELL'}
            if j-1<stop: return {'kind':'OPEN','reason':'inner box Q_%d (half-width 2^%d*1e-7 about the cell midpoint) not certified; needs LOCAL/pinning or high-precision energy'%(j,j)}
            return build(j-1,lo,hi,0)
        if lo[k]<ilo[k]:
            h1=list(hi);h1[k]=ilo[k]; l2=list(lo);l2[k]=ilo[k]; slabs.append((lo,h1,j))
            return {'kind':'SPLIT','axis':k,'mid':str(ilo[k]),'children':[{'kind':'SLAB','n':len(slabs)-1},build(j,l2,hi,k)]}
        h1=list(hi);h1[k]=ihi[k]; l2=list(lo);l2[k]=ihi[k]; slabs.append((l2,hi,j)); nslab=len(slabs)-1
        return {'kind':'SPLIT','axis':k,'mid':str(ihi[k]),'children':[build(j,lo,h1,k+1),{'kind':'SLAB','n':nslab}]}
    return build(J-1,LO,HI,0),slabs
if __name__=='__main__':
    t,s=skeleton(); print('levels',levels(),'slabs',len(s))
    for i,(lo,hi,j) in enumerate(s[-20:]): print(len(s)-20+i,j,['%.1e'%float(h-l) for l,h in zip(lo,hi)][6:])
