import numpy as np, json, kkt_active as KA
from hess_probe import phi_g_H
E=KA.E
lam=np.load('lam_joint.npy'); w=np.zeros(134); w[KA.A]=lam
th=KA.z0[:15]
def schur(w,eps=0.0):
    w=w+eps
    L=np.zeros((76,76))
    for (u,v),x in zip(E,w): L[u,u]+=x;L[v,v]+=x;L[u,v]-=x;L[v,u]-=x
    keep=[i for i in range(16,76) if L[i,i]>0]
    S=L[:16,:16]-L[:16,keep]@np.linalg.solve(L[np.ix_(keep,keep)],L[keep,:16]); return -S
for eps in (0,1e-12,1e-9):
    C=schur(w,eps); phi,g,H=phi_g_H(C,th); ev=np.linalg.eigvalsh(H)
    print(eps,'phi/W-R*^2 %.3e'%(phi/(w+eps).sum()-0.2347000904004482396**2),'|g| %.3e'%np.abs(g).max(),'eig',ev[:6])
