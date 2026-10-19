import time,json,numpy as np
from fractions import Fraction as F
import certify_box as cb, bnb
idx=2164
b=bnb.BOX[idx]; lo=[F(x) for x in b['lower']]; hi=[F(x) for x in b['upper']]
t=time.time(); th=np.array(bnb.DIAG[idx]['None'][1]); lam,s=cb.fit_weights(th); print('fit',time.time()-t, s)
w=cb.rationalize_weights(lam); t=time.time(); pairs,W=cb.exact_pairs(w); print('exact',time.time()-t, len(pairs))
t=time.time(); bd,st=cb.box_bound(pairs,W,lo,hi); print('bound',time.time()-t, float(bd/W) if bd is not None else st)
t=time.time(); wp=bnb.worst_point(np.array(lo),np.array(hi)); print('worst',time.time()-t, wp[0]-0.2347000904)
S=sum(pairs.values()); print('sumc/W', float(S/W))
