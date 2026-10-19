import json, math, time
from fractions import Fraction as F
import numpy as np
from n26model import *
part=json.load(open('model_partial.json'))
E=build_edges(part)
json.dump({"edges":E,"faces":part["faces"]},open('model134.json','w'))
d=json.load(open('dl/root25-slim.json'))
L=json.load(open('dl/root25-ledger.json'))
t=time.time()
ks=[kernel(E,s['kernel_certificate']) for s in d['full134rod_supports']]
print('29 kernels exact-gated', time.time()-t)
row=[x for x in L if x['kind']=='FULL134-CORRELATED-ENERGY'][0]
k=ks[row['full_support_index']]
up=F(row['arithmetic_result']['NEW_full134rod_energy_upper_at_same_root'])
print('W*R^2 ratio check: up/W =', float(up/k['W']), 'Rup^2', float(RSTAR_UP**2), up==k['W']*RSTAR_UP**2)
def phi(k,th):
    th=np.concatenate([[0.0],th]); s=0
    for (i,j),c in k['pairs'].items(): s+=2*float(c)*(1-math.cos(2*math.pi*(th[j]-th[i])))
    return s
lo=np.array([float(F(x)) for x in row['lower']]); hi=np.array([float(F(x)) for x in row['upper']])
rng=np.random.default_rng(0)
vals=[phi(k,lo+(hi-lo)*rng.random(15)) for _ in range(2000)]
print('min sampled Phi/W', min(vals)/float(k['W']), 'claimed lower/W', float(F(row['arithmetic_result']['boundary_full134rod_correlated_energy_lower'])/k['W']), 'R*^2',float(RSTAR_UP**2))
