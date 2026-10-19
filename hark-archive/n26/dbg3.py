import sys,numpy as np
from fractions import Fraction as F
import robust2 as r2, shells1669 as S, certify_box as cb, bnb1669 as B
t,sl=S.skeleton(); n=int(sys.argv[1]); lo,hi,j=sl[n]
lof=np.array([float(x) for x in lo]); hif=np.array([float(x) for x in hi])
Pst=r2.ref_positions(B.TH); lam,_=cb.fit_weights(B.TH)
def cbk(w):
    p,W=cb.exact_pairs([F(int(y*10**15),10**15) for y in cb.rationalize_weights(w,floor=1e-11,den=10**15)]); bd,_=cb.box_bound(p,W,lo,hi)
    print(' rig',float(bd/W)); return bd>0
print(r2.robust3(lof,hif,lam,Pst,iters=int(sys.argv[2]),callback=cbk,verbose=True)[1:])
