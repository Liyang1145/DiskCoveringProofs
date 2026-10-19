import numpy as np, json, sys
from fractions import Fraction as F
import diag_open as dg, robust as rb
RS=0.2347000904004482396
D={r['index']:r for r in json.load(open('diag_merged.json'))}
P={b['index']:b for b in json.load(open('pending.json'))['pending_closed_leaf_boxes']}
cells=json.load(open('repo/cover26/proof_bundle/work/n26-refined-anchor-pinning-broad-proposal-v2.json'))['closed_anchor_angle_cells']
cl=np.array([float(F(a)) for a,b in cells]); ch=np.array([float(F(b)) for a,b in cells])
thc=np.array(D[1669]['None'][1]); print('diag point in cell', np.all((thc>=cl)&(thc<=ch)), D[1669]['None'][0]-RS)
b=P[1669]; lo=np.array([float(F(x)) for x in b['lower']]); hi=np.array([float(F(x)) for x in b['upper']])
print('cand - lo', (thc-lo)[6:]); print('hi - cand',(hi-thc)[6:])
rng=np.random.default_rng(1)
for d in [1e-2,3e-3,1e-3,3e-4,1e-4,3e-5,1e-5]:
    vals=[]
    for s in range(3):
        u=np.zeros(15); u[6:]=rng.normal(size=9); u/=np.abs(u).max()
        th=np.clip(thc+d*u,lo,hi)
        t,viol,z=dg.solve(th,th,None,th); vals.append(t-RS)
    print('d=%.0e'%d, ['%.2e'%v for v in vals])
