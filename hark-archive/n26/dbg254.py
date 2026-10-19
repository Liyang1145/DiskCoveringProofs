import numpy as np, sys
from fractions import Fraction as F
import shells1669 as S, robust as rb, diag_open as dg, certify_box as cb, bnb1669 as B
t,sl=S.skeleton(); n=int(sys.argv[1]); lo,hi,j=sl[n]
lof=np.array([float(x) for x in lo]); hif=np.array([float(x) for x in hi])
RS=0.2347000904004482396
best=None
for s in range(3):
    th0=(lof+hif)/2 if s==0 else lof+(hif-lof)*np.random.default_rng(s).random(15)
    tt,viol,z=dg.solve(lof,hif,None,th0); print('model min - R*', tt-RS, viol)
lam,_=cb.fit_weights(B.TH)
w,v=rb.robust_weights(lof,hif,lam,iters=int(sys.argv[2]),floor=1e-11,verbose=True,tol=1e-13,sc=float(sys.argv[3]),hp=True)
print('robust v',v)
p,W=cb.exact_pairs([F(x,B.DEN) for x in B.wint(w)]); bd,_=cb.box_bound(p,W,lo,hi); print('rig',float(bd/W))
