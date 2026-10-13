"""One calibrated candidate-local Schur Hessian diagnostic, not global bound."""
import numpy as np,json
from scipy.optimize import linprog
from pathlib import Path
P=Path(__file__).resolve().parent
D=np.load(P/'stress-barycentric-matrix.npz');A,rhs=D['A'],D['b'];U,S,V=np.linalg.svd(A,full_matrices=False);k=sum(S>1e-12);Q=V[:k];v=(U[:,:k].T@rhs)/S[:k];bounds=[(0,None)]*34+[(None,None)]+[(0,None)]*2
sol=[]
for j in range(34):
 c=np.zeros(37);c[j]=-1;R=linprog(c,A_eq=Q,b_eq=v,bounds=bounds,method='highs');assert R.success
 if R.x[j]>1e-9:sol.append(R.x)
x=np.mean(sol,axis=0)
g=json.loads((P/'stress-barycentric-result.json').read_text());theta=np.array([float(a['theta'])for a in g['anchors']]);edges=[]
# nodes: anchors0..9, sites10..23, surviving witness24+f
for f,face in enumerate(g['faces']):
 if x[f]<1e-9:continue
 for i,beta in zip(face['ids'],face['beta']):edges.append((10+i,24+f,x[f]*float(beta)))
e=14
for j,anc in enumerate(g['anchors']):
 for i in anc['owners']:edges.append((j,10+i,x[e]));e+=1
used=sorted({v for a,b,w in edges for v in(a,b)});remap={v:i for i,v in enumerate(used)}
L=np.zeros((len(used),len(used)))
for a,b,w in edges:
 a,b=remap[a],remap[b];L[a,a]+=w;L[b,b]+=w;L[a,b]-=w;L[b,a]-=w
B=L[:10,:10]-L[:10,10:]@np.linalg.solve(L[10:,10:],L[10:,:10])
W=-B;np.fill_diagonal(W,0)
def hes(th):
 M=2*W*np.cos(th[:,None]-th[None,:]);return np.diag(M.sum(axis=1))-M
H=hes(theta)
# theta0 fixed. Critical face: d gap4=d gap9=0; rotation removed.
T=np.tril(np.ones((10,9)),-1);G=np.zeros((2,9));G[0,4]=1;G[1,:]=1
_,_,vg=np.linalg.svd(G,full_matrices=True);Z=vg[2:].T
Hg=T.T@H@T;ev=np.linalg.eigvalsh(Hg);evc=np.linalg.eigvalsh(Z.T@Hg@Z)
xy=np.column_stack((np.cos(theta),np.sin(theta)));E=np.trace(xy.T@B@xy);r=float(json.loads((P/'root-scout.json').read_text())['z_c_r'][2])
out={'status':'numeric_only','averaged_support_points':len(sol),'active_face_weights':np.where(x[:14]>1e-9)[0].tolist(),'edge_count':len(edges),'equilibrium_residual':float(max(abs(A@x-rhs))),'mu':x[35:37].tolist(),'energy_minus_r_squared':float(E-r*r),'gap_hessian_eigenvalues':ev.tolist(),'cap_face_hessian_eigenvalues':evc.tolist(),'Schur':B.tolist(),'stress':x.tolist(),'scope':'one candidate stress local Hessian; not global convexity or optimality'}
(P/'stress-schur-probe.json').write_text(json.dumps(out,indent=2));print(json.dumps({k:v for k,v in out.items()if k not in('Schur','stress')},indent=2))
