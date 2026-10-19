"""FLOAT/high-precision PROPOSAL (not a proof): locate the unconstrained model-radius
minimiser theta* near box 1669 and its optimal rod weights w*."""
import json, numpy as np, sys
from scipy.optimize import minimize
import certify_box as cb
M=json.load(open('model134.json')); E=[tuple(e) for e in M['edges']]
U=np.array([e[0] for e in E]); V=np.array([e[1] for e in E])
th0=np.array({r['index']:r for r in json.load(open('diag_merged.json'))}[1669]['None'][1])
def harm(w,th):
    t=np.concatenate([[0.0],th]); A=np.stack([np.cos(2*np.pi*t),np.sin(2*np.pi*t)],1)
    L=np.zeros((76,76))
    for (u,v),x in zip(E,w): L[u,u]+=x;L[v,v]+=x;L[u,v]-=x;L[v,u]-=x
    X=-np.linalg.solve(L[16:,16:],L[16:,:16]@A); P=np.vstack([A,X]); D=P[U]-P[V]
    return P,(D*D).sum(1)
# alternating: fit weights at th, move th by gradient of Phi_w ... instead SLSQP on full primal
def pos(z):
    t=np.concatenate([[0.0],z[:15]]); P=np.empty((76,2)); P[:16,0]=np.cos(2*np.pi*t);P[:16,1]=np.sin(2*np.pi*t); P[16:]=z[15:135].reshape(60,2); return P
if __name__=='__main__':
  lam,s=cb.fit_weights(th0); P,l2=harm(lam,th0)
  z0=np.concatenate([th0,P[16:].ravel(),[np.sqrt(l2.max())]])
  cons=lambda z:z[135]**2-((pos(z)[U]-pos(z)[V])**2).sum(1)
  r=minimize(lambda z:z[135],z0,jac=lambda z:np.eye(136)[135],method='SLSQP',constraints=[{'type':'ineq','fun':cons}],options={'maxiter':2000,'ftol':1e-16})
  z=r.x; th=z[:15]
  print('t',repr(z[135]),'Rstar',0.2347000904004482396,'viol',cons(z).min())
  print('th',th.tolist())
  t=np.concatenate([[0],th]); print('D2 check', [t[k+8]-t[k]-0.5 for k in range(8)])
  lam,s=cb.fit_weights(th); print('sqrt s',np.sqrt(s)); print('lam sorted small', np.sort(lam)[:12]); print('#lam<1e-6',(lam<1e-6).sum())
  np.save('kkt1669_float.npy',np.concatenate([th,lam])); np.save('slsqp_z.npy',z)
  