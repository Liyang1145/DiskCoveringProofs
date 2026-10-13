"""Bounded Hessian mechanism test for explicit balanced affine flow; numeric only."""
import json,numpy as np
from pathlib import Path
P=Path(__file__).resolve().parent
jet=json.loads((P/'q10-adaptive-flow-jet.json').read_text());row=json.loads((P/'q10-relaxed-anchor-probe.json').read_text())['rows'][0]
z0=np.array(jet['baseflow']);T=np.array(jet['jet']).reshape(40,2,10);edges=jet['edges'];th=np.arctan2(np.array(row['anchors'])[:,1],np.array(row['anchors'])[:,0]);r=row['radius']
from scipy.linalg import null_space
B=null_space(np.ones((1,10)))
def hess(d):
 z=z0+np.einsum('ekj,j->ek',T,d);theta=th+d;H=np.zeros((10,10));v=np.zeros(10)
 for e in range(40):
  te=T[e];norm=np.linalg.norm(z[e]);u=z[e]/norm;H-=r*te.T@(np.eye(2)-np.outer(u,u))@te/norm
  if edges[e]>=24:
   j=(edges[e]-24)//2;A=np.array([np.cos(theta[j]),np.sin(theta[j])]);der=np.array([A[1],-A[0]])
   H[j,j]+=A@z[e];a=der@te;H[j,:]+=a;H[:,j]+=a
 return H
rng=np.random.default_rng(140879);out=[]
for eps in[0,1e-5,1e-4,1e-3,.003,.01]:
 vals=[]
 for k in range(20):
  d=rng.uniform(-eps,eps,10);d-=d.mean();vals.append(float(np.linalg.eigvalsh(B.T@hess(d)@B)[0]))
 out.append(dict(eps=eps,min_eigen_sample=min(vals),max_eigen_sample=max(vals)))
(P/'q10-adaptive-hessian-control.json').write_text(json.dumps(dict(status='numeric_only_not_continuum',tests=out),indent=2));print(out)
