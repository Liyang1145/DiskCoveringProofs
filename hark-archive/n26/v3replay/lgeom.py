"""Carve a v3 OPEN box T (touching LOCAL cube 59) into: outer slabs (level -1, FORCE B&B)
and shell slabs about c*=theta* (level m>=0, LOCAL-SLAB energy leaves). Proposal-side (checker A side)."""
import os as _os, sys as _sys  # hark-archive portable paths (see hark-archive/_paths.py)
_hd = _os.path.dirname(_os.path.abspath(__file__))
while _os.path.basename(_hd) != 'hark-archive' and _os.path.dirname(_hd) != _hd: _hd = _os.path.dirname(_hd)
_sys.path.append(_hd); from _paths import DCP_N26
import sys, json
sys.path.insert(0,DCP_N26+'/local'); sys.path.insert(0,DCP_N26)
from fractions import Fraction as F
import hp
C=hp.THSTAR
RHO0=F(66,10**7)
KOUT={'304':12,'28':15}
OPEN23=['1','5','9','13','17','21','25','29','33','37','41','45','48','44','40','36','32','24','20','16','12','8','4']
for _t in OPEN23: KOUT[_t]=15   # outer doubling levels (force leaves) per target
B=json.load(open(DCP_N26+'/v3replay/boxes.json'))['boxes']
def T(t): return [F(x) for x in B[str(t)]['lo']],[F(x) for x in B[str(t)]['hi']]
def Qp(t,m):
    lo,hi=T(t)
    if m< -KOUT.get(str(t),0): return lo,hi
    r=RHO0/2**m
    return [max(l,c-r) for l,c in zip(lo,C)],[min(h,c+r) for h,c in zip(hi,C)]
def empty(lo,hi): return any(a>b for a,b in zip(lo,hi))
def tree(t):
    """returns (nested tree, slabs list[(level,lo,hi)])"""
    slabs=[]
    def build(m,lo,hi):
        ilo,ihi=Qp(t,m+1)
        if empty(ilo,ihi):
            slabs.append((m,lo,hi)); return {'kind':'SLAB','n':len(slabs)-1}
        for k in range(15):
            if lo[k]<ilo[k]:
                assert ilo[k]<hi[k]
                h1=list(hi);h1[k]=ilo[k]; l2=list(lo);l2[k]=ilo[k]
                slabs.append((m,lo,h1)); n=len(slabs)-1
                return {'kind':'SPLIT','axis':k,'mid':str(ilo[k]),'children':[{'kind':'SLAB','n':n},build(m,l2,hi)]}
            if hi[k]>ihi[k]:
                assert lo[k]<ihi[k]
                h1=list(hi);h1[k]=ihi[k]; l2=list(lo);l2[k]=ihi[k]
                slabs.append((m,l2,hi)); n=len(slabs)-1
                return {'kind':'SPLIT','axis':k,'mid':str(ihi[k]),'children':[build(m,lo,h1),{'kind':'SLAB','n':n}]}
        assert (lo,hi)==(ilo,ihi)
        return build(m+1,lo,hi)
    lo,hi=T(t)
    return build(-KOUT.get(str(t),0)-1,lo,hi),slabs
if __name__=='__main__':
    for t in sys.argv[1:]:
        tr,sl=tree(t)
        from collections import Counter
        print(t,len(sl),sorted(Counter(m for m,_,_ in sl).items()))
