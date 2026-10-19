import numpy as np, sys
from scipy.optimize import minimize
from fractions import Fraction as F
import fbb, bnb, certify_box as cb
RS2=float(cb.RUP2)
idx=int(sys.argv[1]); b=bnb.BOX[idx]
lo=np.array([float(F(x)) for x in b['lower']]); hi=np.array([float(F(x)) for x in b['upper']])
pairs,W=fbb.fw(np.array(bnb.DIAG[idx]['None'][1]))
P=list(pairs.items())
def phi(th):
    t=np.concatenate([[0],th]); return sum(2*c*(1-np.cos(2*np.pi*(t[j]-t[i]))) for (i,j),c in P)/W-RS2
rng=np.random.default_rng(0); best=1
for k in range(20):
    x0=lo+(hi-lo)*rng.random(15); r=minimize(phi,x0,bounds=list(zip(lo,hi)),method='L-BFGS-B'); best=min(best,r.fun)
print('true box min phi/W-R*2', best, 'taylor', fbb.fbound(pairs,W,lo,hi)[0])
# halve along each widest dims: what fraction of sub-boxes have true min>0
