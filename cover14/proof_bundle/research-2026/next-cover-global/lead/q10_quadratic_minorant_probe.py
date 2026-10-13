"""Numeric diagnostic for GLOBAL box quadratic minorant, not sampling Hessian."""
import json,numpy as np
from pathlib import Path
from scipy.linalg import null_space
P=Path(__file__).resolve().parent
jet=json.loads((P/'q10-adaptive-flow-jet.json').read_text());row=json.loads((P/'q10-relaxed-anchor-probe.json').read_text())['rows'][0];z=np.array(jet['baseflow']);T0=np.array(jet['jet']).reshape(40,2,10);edges=jet['edges'];A=np.array(row['anchors']);U=.33173203427623414;B=null_space(np.ones((1,10)));C=np.array([np.eye(10)[5]-np.eye(10)[4],np.eye(10)[0]-np.eye(10)[9]])
# sqrt((n+u.w)^2+(Ju.w)^2)<=n+u.w+(Ju.w)^2/(2 radiallower)
# -A(theta+d).(z+Td) >= -A.z-A.Td-A'.z*d-A'.Td*d +(A.z)d²/2
#   -||z|| |d|³/6 -||Td|| d²/2; latter from order1 Taylor for cross term.
out=[]
for alpha in[.0625,.125,.25,.5]:
 for eps in[.001,.003,.005]:
  T=alpha*T0;H=3*C.T@C;rad=[]
  for e in range(40):
   n=np.linalg.norm(z[e]);u=z[e]/n;radial=n-eps*np.abs(u@T[e]).sum();rad.append(radial/n)
   if radial<=0:break
   cross=np.array([-u[1],u[0]])@T[e];H-=U*np.outer(cross,cross)/radial
   if edges[e]>=24:
    j=(edges[e]-24)//2;der=np.array([A[j,1],-A[j,0]]);v=der@T[e];H[j,:]+=v;H[:,j]+=v;H[j,j]+=A[j]@z[e]-n*eps/3-eps*np.linalg.norm(np.abs(T[e]).sum(axis=1))
  out.append(dict(alpha=alpha,eps=eps,min_radial_ratio=min(rad),min_eigen=float(np.linalg.eigvalsh(B.T@H@B)[0])if min(rad)>0 else None))
(P/'q10-quadratic-minorant-probe.json').write_text(json.dumps(dict(status='numeric_only_proposed_box_bound',tests=out),indent=2));print(out)
