"""Bounded mechanism check: damping may avoid affineflow zeros; numeric only."""
import json,numpy as np
from pathlib import Path
from scipy.linalg import null_space
P=Path(__file__).resolve().parent
jet=json.loads((P/'q10-adaptive-flow-jet.json').read_text());row=json.loads((P/'q10-relaxed-anchor-probe.json').read_text())['rows'][0]
z0=np.array(jet['baseflow']);T0=np.array(jet['jet']).reshape(40,2,10);edges=jet['edges'];th=np.arctan2(np.array(row['anchors'])[:,1],np.array(row['anchors'])[:,0]);r=row['radius'];B=null_space(np.ones((1,10)));C=np.array([np.eye(10)[5]-np.eye(10)[4],np.eye(10)[0]-np.eye(10)[9]])
def hess(d,T):
 z=z0+np.einsum('ekj,j->ek',T,d);theta=th+d;H=3*C.T@C
 for e in range(40):
  te=T[e];norm=np.linalg.norm(z[e]);u=z[e]/norm;H-=r*te.T@(np.eye(2)-np.outer(u,u))@te/norm
  if edges[e]>=24:
   j=(edges[e]-24)//2;A=np.array([np.cos(theta[j]),np.sin(theta[j])]);der=np.array([A[1],-A[0]])
   H[j,j]+=A@z[e];a=der@te;H[j,:]+=a;H[:,j]+=a
 return H
rng=np.random.default_rng(87914);directions=[rng.uniform(-1,1,10)for _ in range(30)];directions=[d-d.mean()for d in directions];out=[]
for alpha in[.25,.5,.75,1.]:
 for eps in[.001,.003,.005]:
  vals=[float(np.linalg.eigvalsh(B.T@hess(eps*d,alpha*T0)@B)[0])for d in directions];out.append(dict(alpha=alpha,eps=eps,min_sample=min(vals),max_sample=max(vals)))
(P/'q10-damped-jet-control.json').write_text(json.dumps(dict(status='numeric_only',tests=out),indent=2));print(out)
