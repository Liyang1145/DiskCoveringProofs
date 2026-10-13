"""Independent numeric scatter assembly; not a certificate."""
import json
from pathlib import Path
import numpy as np
from scipy.optimize import linprog
P=Path(__file__).resolve().parent
D=json.loads((P.parent/'r20-alternative/socp_anchor_export.json').read_text())
U=np.array(D['U']); C=np.array(D['C_sites']); Z=np.array(D['Z_aux']); X=np.vstack((U,C,Z));r=D['r_solution']
edges=[]
for kind,s,k in D['incidence_map']: edges.append((9+s,k if kind=='endpoint' else 20+k))
active=[i for i,(kind,s,k) in enumerate(D['incidence_map']) if kind=='endpoint' or k not in (5,7)]
A=np.zeros((54,45))
for j,e in enumerate(active):
 v,w=edges[e]; d=X[v]-X[w];d=d/np.linalg.norm(d)
 for node,force in ((v,d),(w,-d)):
  if node>=9:A[2*(node-9):2*(node-9)+2,j]+=force
  else:A[44+node,j]+=force@np.array([-U[node,1],U[node,0]])
 A[-1,j]=1
b=np.zeros(54);b[-1]=1
res=linprog(np.r_[np.zeros(45),-1],A_ub=np.c_[-np.eye(45),np.ones(45)],b_ub=np.zeros(45),A_eq=np.c_[A,np.zeros(54)],b_eq=b,bounds=[(0,None)]*46,method='highs')
sol=np.linalg.lstsq(A,b,rcond=None)[0]
alpha=np.zeros(51);alpha[active]=sol;alpha/=alpha.sum()
print('LP success',res.success,'LS used; nonzero residual not a certificate')
L=np.zeros((31,31))
for (v,w),a in zip(edges,alpha): L[v,v]+=a;L[w,w]+=a;L[v,w]-=a;L[w,v]-=a
Lam=L[:9,:9]-L[:9,9:]@np.linalg.pinv(L[9:,9:])@L[9:,:9]
th=np.arctan2(U[:,1],U[:,0]);diff=th[:,None]-th[None,:]
H=2*Lam*np.cos(diff);np.fill_diagonal(H,0);np.fill_diagonal(H,-H.sum(axis=1))
g=-2*np.sum(Lam*np.sin(diff),axis=1)
ev,Q=np.linalg.eigh(H)
report={'scope':'numeric independent scatter / LP / Schur; not certified','min_alpha':float(alpha[active].min()),'balance_max':float(abs(A@alpha[active]-b).max()),'free_LX_max':float(abs((L@X)[9:]).max()),'gradient':g.tolist(),'E':float(np.sum(Lam*(U@U.T))),'r_squared':r*r,'H_eigenvalues':ev.tolist(),'min_eigenvector':Q[:,0].tolist(),'alpha51':alpha.tolist(),'Lambda':Lam.tolist(),'H':H.tolist()}
(P/'radial_network_check.json').write_text(json.dumps(report,indent=2))
print({k:v for k,v in report.items() if k not in ['alpha51','Lambda','H','min_eigenvector']})
