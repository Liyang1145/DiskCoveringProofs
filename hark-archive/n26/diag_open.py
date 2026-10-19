"""Numerical (NOT proof) diagnostic: for each root25 OPEN box and each origin
owner branch v in {16,25}, minimise the 134-rod model radius
   t(theta,x) = max( max_rod |p_u-p_v| , |c_v| )
over theta in the closed box, free positions x unrestricted.
If min t < R* the energy+origin route CANNOT close that branch on that box
(weak duality: any energy certificate is <= the model optimum)."""
import json, sys, math, time
import numpy as np
from scipy.optimize import minimize
from multiprocessing import Pool
from fractions import Fraction as F
M=json.load(open('/workspace/work/dcp-n26/model134.json')); E=[tuple(e) for e in M['edges']]
RS=0.2347000904004482396
d=json.load(open('/workspace/work/dcp-n26/pending.json'))
boxes=d['pending_closed_leaf_boxes']
U=np.array([e[0] for e in E]); V=np.array([e[1] for e in E])

def pos(z):
    th=np.concatenate([[0.0],z[:15]])
    P=np.empty((76,2)); P[:16,0]=np.cos(2*np.pi*th); P[:16,1]=np.sin(2*np.pi*th)
    P[16:]=z[15:135].reshape(60,2); return P
def cons(z,owner):
    P=pos(z); t=z[135]; D=P[U]-P[V]; c=t*t-(D*D).sum(1)
    if owner is not None:
        c=np.append(c,t*t-(P[16+owner]**2).sum())
    return c
def init_x(th):
    # crude: iterative averaging (harmonic with unit weights)
    th=np.concatenate([[0.0],th]); P=np.zeros((76,2)); P[:16,0]=np.cos(2*np.pi*th); P[:16,1]=np.sin(2*np.pi*th)
    nb=[[] for _ in range(76)]
    for u,v in E: nb[u].append(v); nb[v].append(u)
    for _ in range(400):
        for i in range(16,76): P[i]=P[nb[i]].mean(0)
    return P[16:].ravel()
def solve(lo,hi,owner,th0):
    x0=init_x(th0); P=pos(np.concatenate([th0,x0,[0]]))
    D=P[U]-P[V]; t0=math.sqrt((D*D).sum(1).max())
    if owner is not None: t0=max(t0,math.sqrt((P[16+owner]**2).sum()))
    z0=np.concatenate([th0,x0,[t0*1.01]])
    bnds=[(a,b) for a,b in zip(lo,hi)]+[(None,None)]*120+[(0,1)]
    r=minimize(lambda z:z[135], z0, jac=lambda z: np.eye(136)[135], method='SLSQP',
               bounds=bnds, constraints=[{'type':'ineq','fun':cons,'args':(owner,)}],
               options={'maxiter':500,'ftol':1e-13})
    z=r.x; viol=-min(0,cons(z,owner).min())
    return float(z[135]), float(viol), z
def work(i):
    b=boxes[i]; lo=np.array([float(F(x)) for x in b['lower']]); hi=np.array([float(F(x)) for x in b['upper']])
    out={'index':b['index'],'width':(hi-lo).tolist()}
    rng=np.random.default_rng(b['index'])
    for owner in (None,16,25):
        if owner is not None and out['None'] is not None and out['None'][0]>RS+2e-4:
            out[str(owner)]='implied>=None'; continue
        best=None
        for s in range(3):
            th0=(lo+hi)/2 if s==0 else lo+(hi-lo)*rng.random(15)
            t,viol,z=solve(lo,hi,owner,th0)
            if viol<1e-10 and (best is None or t<best[0]): best=(t,z[:15].tolist())
        out[str(owner)]=best
    return out
if __name__=='__main__':
    import os
    done=set()
    for fn in [f for f in os.listdir('diag') if f.endswith('.jsonl')]:
        for line in open('diag/'+fn):
            done.add(json.loads(line)['index'])
    for f in os.listdir('diag'):
        if f.startswith('d_'):
            for r in json.load(open('diag/'+f)): done.add(r['index'])
    idx=[i for i,b in enumerate(boxes) if b['index'] not in done]
    print('todo',len(idx),flush=True)
    with Pool(2) as p, open('diag/run_%d.jsonl'%int(time.time()*1000),'w') as out:
        for r in p.imap_unordered(work, idx, chunksize=1):
            out.write(json.dumps(r)+'\n'); out.flush()
