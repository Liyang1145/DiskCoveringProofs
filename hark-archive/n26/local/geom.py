"""Region R = Q6 ∩ box1669 (the single OPEN node of certs/1669.json) and its shells about c*=THSTAR."""
import sys; sys.path.insert(0,'/workspace/work/dcp-n26')
from fractions import Fraction as F
import shells1669 as S, hp
LO6,HI6=S.Q(6)
C=hp.THSTAR
RHO0=F(66,10**7)
def Qp(m):
    r=RHO0/2**m
    return [max(LO6[k],C[k]-r) if k>=6 else LO6[k] for k in range(15)],[min(HI6[k],C[k]+r) if k>=6 else HI6[k] for k in range(15)]
assert Qp(0)==(LO6,HI6)
def empty(lo,hi): return any(a>b for a,b in zip(lo,hi))
def slabs(m):
    """closed boxes covering Qp(m) minus interior-relative Qp(m+1) (shell m)."""
    (lo,hi),(ilo,ihi)=Qp(m),Qp(m+1)
    out=[]; lo=list(lo); hi=list(hi)
    if empty(ilo,ihi): return [(lo,hi)]
    for k in range(6,15):
        if lo[k]<ilo[k]:
            h=list(hi); h[k]=ilo[k]; out.append((list(lo),h)); lo[k]=ilo[k]
        if hi[k]>ihi[k]:
            l=list(lo); l[k]=ihi[k]; out.append((l,list(hi))); hi[k]=ihi[k]
    return out
def mmax():
    m=0
    while not empty(*Qp(m)): m+=1
    return m   # Qp(mmax) empty -> shells 0..mmax-1 cover R
