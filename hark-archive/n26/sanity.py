import json,math,itertools
from fractions import Fraction as F
import numpy as np, certify_box as cb
R={r['index']:r for r in json.load(open('diag_merged.json'))}
d=json.load(open('dl/root25-slim.json'))
B={b['index']:b for b in d['pending_closed_leaf_boxes']}
i=1663
lo=np.array([float(F(x)) for x in B[i]['lower']]); hi=np.array([float(F(x)) for x in B[i]['upper']])
lam,s=cb.fit_weights(np.array(R[i]['None'][1])); wq=cb.rationalize_weights(lam); pairs,W=cb.exact_pairs(wq)
P=[(i_,j_,float(c)) for (i_,j_),c in pairs.items()]; Wf=float(W)
def phi(th):
    th=np.concatenate([[0.0],th]); return sum(2*c*(1-math.cos(2*math.pi*(th[j]-th[i]))) for i,j,c in P)
rng=np.random.default_rng(1); best=1
for k in range(3000):
    u=rng.random(15) if k%2 else (rng.random(15)>0.5).astype(float)
    best=min(best,phi(lo+(hi-lo)*u)/Wf-float(cb.RUP2))
x=np.array(R[i]['None'][1]); print('at diag minimizer', phi(x)/Wf-float(cb.RUP2))
print('sampled min (Phi-WR^2)/W', best)
# also numerically minimise phi over box
from scipy.optimize import minimize
r=minimize(lambda t: phi(t), x, bounds=list(zip(lo,hi)), method='L-BFGS-B'); print('local min', r.fun/Wf-float(cb.RUP2))
