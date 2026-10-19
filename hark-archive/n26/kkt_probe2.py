import numpy as np, kkt_active as KA
z=np.concatenate([KA.z0[:135],np.ones(KA.nA)/KA.nA,[KA.z0[135]**2]])
Jm=KA.J(z); sv=np.linalg.svd(Jm,compute_uv=False); print(KA.nA,'J sv tail',sv[-12:])
