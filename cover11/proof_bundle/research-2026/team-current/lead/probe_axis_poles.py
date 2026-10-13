from pathlib import Path
import numpy as np,json
from scipy.optimize import root
from probe_lowbearing_stationary import z,R
P=Path(__file__).parent

def gh(X,d):
 x,y=X;gx=d/2;gy=0;H=np.zeros((2,2))
 for u,a,b,c,sg in [(y-d/2,z[1]-z[9],-z[16]/(4*R*R),z[78]/(2*R),-1),(y+d/2,z[3]-z[9],z[20]/(4*R*R),-z[82]/(2*R),1)]:
  q=x*x+u*u;l=np.sqrt(q);w=2*b-c/l;gx+=w*x-a*sg*u/q;gy+=w*u+a*sg*x/q
  H+=w*np.eye(2)+c*np.outer([x,u],[x,u])/l**3+a*sg*np.array([[2*x*u,u*u-x*x],[u*u-x*x,-2*x*u]])/q**2
 return np.array([gx,gy]),H
rows=[]
for d in [.46,.6,.68,.76,.9,1.04]:
 roots=[]
 for sg in [-1,1]:
  for rad in [.006,.012,.025,.05]:
   for th in np.linspace(0,2*np.pi,16,endpoint=False):
    X=[rad*np.cos(th),sg*d/2+rad*np.sin(th)];sol=root(lambda X:gh(X,d)[0],X,jac=lambda X:gh(X,d)[1]);X=sol.x
    if np.linalg.norm(gh(X,d)[0])>1e-8 or any(np.linalg.norm(X-Y)<1e-6 for Y in roots):continue
    roots.append(X)
    if max(np.hypot(X[0],X[1]-d/2),np.hypot(X[0],X[1]+d/2))>.76:continue
    rows.append({'d':d,'x':X.tolist(),'eigs':np.linalg.eigvalsh(gh(X,d)[1]).tolist()})
(P/'axis_pole_probe.json').write_text(json.dumps(rows,indent=2));print(rows)
