import numpy as np, kkt_active as KA, json
from scipy.optimize import nnls
nA=KA.nA; N=KA.N
z=np.concatenate([KA.z0[:135],np.ones(nA)/nA,[KA.z0[135]**2]])
Jm=KA.J(z); f=np.array(KA.F(z))
Ar=Jm[nA:,135:135+nA]; b=-(f[nA:]-Ar@z[135:135+nA])
Aa=np.vstack([Ar,1e3*np.ones(nA)]); bb=np.concatenate([b,[1e3*0+0]])
# rows: stationarity (135) and sum row (last of F is sum-1)
lam,res=nnls(Aa[:-1],b[:]) if False else (None,None)
A2=Ar.copy(); b2=b.copy()
lam,res=nnls(A2,b2); print('nnls res',res,'sum',lam.sum(),'#zero',(lam<1e-12).sum(), 'min pos', lam[lam>1e-12].min())
np.save('lam_joint.npy',lam)
U,S,Vt=np.linalg.svd(Jm); nul=Vt[-10:]
for v in nul[:4]:
    idx=np.argsort(-np.abs(v))[:8]; print([(int(i),round(float(v[i]),3)) for i in idx])
M=json.load(open('model134.json')); deg=np.zeros(76,int)
for e in [M['edges'][i] for i in KA.A]: deg[e[0]]+=1; deg[e[1]]+=1
print('active degree of free vertices', deg[16:].tolist())
