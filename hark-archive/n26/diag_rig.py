import numpy as np,sys,time
from fractions import Fraction as F
import robust as rb, certify_box as cb, bnb2
idx=int(sys.argv[1]); b=bnb2.BOX[idx]; lo=[F(x) for x in b['lower']]; hi=[F(x) for x in b['upper']]
lof=np.array([float(x) for x in lo]); hif=np.array([float(x) for x in hi])
lam,_=cb.fit_weights(np.array(bnb2.DIAG[idx]['None'][1]))
def cbk(w):
    p,W=cb.exact_pairs([F(x,bnb2.DEN) for x in bnb2.wint(w)]); bd,_=cb.box_bound(p,W,lo,hi); print(' rig',float(bd/W),flush=True); return bd>0
t=time.time(); w,v,ok=rb.robust_weights(lof,hif,lam,iters=int(sys.argv[2]),callback=cbk,every=25); print(v,ok,time.time()-t)
