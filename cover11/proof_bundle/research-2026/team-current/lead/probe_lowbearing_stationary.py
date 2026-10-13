"""Bounded fixed-outer stationary root diagnostic. No completeness inference."""
from pathlib import Path
import numpy as np,json,math
from scipy.optimize import root
P=Path(__file__).parent;z=np.array(json.loads((P/'joint_nested_frozen.json').read_text())['z']);R=.38

def setup(r,b1,b2):
 Q=np.array([[r*np.sin(2*b1),2*r*np.sin(b1)**2],[r*np.sin(2*b2),-2*r*np.sin(b2)**2]])
 A=r*np.array([np.sin(b1)**2+np.sin(b2)**2,np.sin(b2)*np.cos(b2)-np.sin(b1)*np.cos(b1)])
 return Q,A

def gh(x,r,b1,b2):
 Q,A=setup(r,b1,b2);g=A.copy();h=np.zeros((2,2))
 for q,a,bb,c,sg in zip(Q,[z[1]-z[9],z[3]-z[9]],[-z[16]/(4*R*R),z[20]/(4*R*R)],[z[78]/(2*R),-z[82]/(2*R)],[-1,1]):
  dx,dy=x-q;l2=dx*dx+dy*dy;l=math.sqrt(l2)
  if l<1e-12:return np.full(2,1e10),np.eye(2)*1e10
  W=2*bb-c/l;g+=W*np.array([dx,dy])+a*sg*np.array([-dy,dx])/l2
  h+=W*np.eye(2)+c*np.outer([dx,dy],[dx,dy])/l**3+a*sg*np.array([[2*dx*dy,dy*dy-dx*dx],[dy*dy-dx*dx,-2*dx*dy]])/l2**2
 return g,h

def residuals(x,r,b1,b2):
 v,t=x;s=math.sqrt(1-r*r)
 return [(v-r*math.sin(2*b1))**2+(t+r*math.cos(2*b1))**2-r*r,(v-r*math.sin(2*b2))**2+(t-r*math.cos(2*b2))**2-r*r,(v-s)**2+t*t-(1-r)**2,-v,t-v*math.tan(b1),-t-v*math.tan(b2)]

if __name__=='__main__':
 rows=[];bvals=[.65,.75,.85,.95,1.05,1.16]
 for b1 in bvals:
  for b2 in bvals:
   if min(b1,b2)>=1:continue
   r=.3795;roots=[]
   for v in [.33,.48,.64,.75]:
    for t in [-.35,-.15,0,.15,.35]:
     sol=root(lambda x:gh(x,r,b1,b2)[0],[v,t],jac=lambda x:gh(x,r,b1,b2)[1])
     if np.linalg.norm(gh(sol.x,r,b1,b2)[0])>1e-8 or any(np.linalg.norm(sol.x-y)<1e-6 for y in roots):continue
     roots.append(sol.x);res=residuals(sol.x,r,b1,b2)
     if max(res)<=1e-8:rows.append({'b1':b1,'b2':b2,'r':r,'x':sol.x.tolist(),'residuals':res,'eigenvalues':np.linalg.eigvalsh(gh(sol.x,r,b1,b2)[1]).tolist()})
 out={'scope':'numeric fixed-outer roots only, no completeness','rows':rows};(P/'lowbearing_stationary_probe.json').write_text(json.dumps(out,indent=2));print('legal roots',len(rows),'negative definite',sum(row['eigenvalues'][-1]<0 for row in rows));print(rows[:3])
