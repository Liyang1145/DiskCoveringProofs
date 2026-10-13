import json,numpy as np
from pathlib import Path
p=Path(__file__).resolve().parents[2]/'r20-alternative/socp_anchor_export.json'; d=json.loads(p.read_text())
a=np.array(d['alpha_all_51_norm_form_2r_lambda'],float); U=np.array(d['U'],float)
# nodes switches0:8 sites9:19 aux20:30, incidence map gives face index and site
edges=[]
for k,e in enumerate(d['incidence_map']):
 kind,site,q=e
 if kind=='endpoint': v,w=9+site,q
 else: v,w=9+site,20+q
 edges.append((v,w,a[k]))
L=np.zeros((31,31))
for v,w,x in edges:
 if x>1e-10: L[v,v]+=x;L[w,w]+=x;L[v,w]-=x;L[w,v]-=x
bb=L[:9,:9];bf=L[:9,9:];ff=L[9:,9:];Lam=bb-bf@np.linalg.pinv(ff,rcond=1e-12)@bf.T
E=np.sum(Lam*(U@U.T)); R=d['r_solution']
th=np.arctan2(U[:,1],U[:,0]); cs=np.cos(th[:,None]-th[None,:]);H=np.zeros((9,9))
for i in range(9):
 for j in range(9):
  if i!=j:H[i,j]=2*Lam[i,j]*cs[i,j]
 H[i,i]=-sum(H[i,j] for j in range(9) if j!=i)
ev=np.linalg.eigvalsh(H)
print('sum',a.sum(),'nz',sum(a>1e-10),'E',repr(E),'R2',repr(R*R),'diff',E-R*R)
print('offdiag',Lam[~np.eye(9,dtype=bool)].max())
print('ev',ev,'rot',np.ones(9)@H@np.ones(9))
print('Lam',Lam)
