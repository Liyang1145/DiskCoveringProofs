import numpy as np, kkt_active as KA
nA=KA.nA; N=KA.N
lam=np.load('lam_joint.npy')
z=np.concatenate([KA.z0[:135],lam,[KA.z0[135]**2]])
Jm=KA.J(z)
dead=[]
import json
deg=np.zeros(76,int)
for i in KA.A: u,v=KA.E[i]; deg[u]+=1; deg[v]+=1
dv=[i for i in range(16,76) if deg[i]==0]; print('dead vertices',dv)
dcols=[15+2*(i-16)+c for i in dv for c in (0,1)]; drows=[nA+2*(i-16)+c for i in dv for c in (0,1)]
keepc=[k for k in range(N) if k not in dcols]; keepr=[k for k in range(N) if k not in drows]
J2=Jm[np.ix_(keepr,keepc)]; U,S,Vt=np.linalg.svd(J2); print('sv tail',S[-6:])
for v in Vt[-3:]:
    full=np.zeros(N); full[keepc]=v
    print('theta part',np.round(full[:15],3),'|theta| %.3f'%np.linalg.norm(full[:15]),'lam part norm %.3f'%np.linalg.norm(full[135:135+nA]))
print('lam small', sorted([(float(l),i) for l,i in zip(lam,KA.A)])[:14])
