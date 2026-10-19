import numpy as np, json, kkt_active as KA
z0=KA.z0; sl=KA.sl
print(np.sort(sl)[100:125])
z=np.concatenate([z0[:135],np.ones(KA.nA)/KA.nA,[z0[135]**2]])
Jm=KA.J(z); N=KA.N; nA=KA.nA
sv=np.linalg.svd(Jm,compute_uv=False); print('J sv tail',sv[-6:])
Ar=Jm[nA:,135:135+nA]; print('stationarity-in-lam rank',np.linalg.matrix_rank(Ar,1e-9),'of',nA, 'sv tail',np.linalg.svd(Ar,compute_uv=False)[-4:])
G=Jm[:nA,:135]; print('constraint grad rank',np.linalg.matrix_rank(G,1e-9))
