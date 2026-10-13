"""Fixedouter bounded calibration of explicitdiskdual; numerical only."""
from pathlib import Path
import json,math,numpy as np
from scipy.optimize import minimize
P=Path(__file__).parent;z=json.loads((P/'joint_nested_frozen.json').read_text())['z'];R=.38

def run(r,b1,b2):
 s=math.sqrt(1-r*r);T=b1+b2;D=b1-b2;anchor=np.array([2*r*math.sin(T)*math.cos(D),2*r*math.sin(T)*math.sin(D)])
 disks=np.array([[r*math.sin(2*b1),-r*math.cos(2*b1)],[r*math.sin(2*b2),r*math.cos(2*b2)],[s,0]]);rad=np.array([r,r,1-r]);A=np.array([r*(math.sin(b1)**2+math.sin(b2)**2),r*(math.sin(b2)*math.cos(b2)-math.sin(b1)*math.cos(b1))]);B=A.copy();C=0.;kap=0.
 def obj(x):
  ans=A@x
  for b,sg,a,beta,gamma in [(b1,-1,z[1]-z[9],-z[16]/(4*R*R),-z[78]/(2*R)),(b2,1,z[3]-z[9],z[20]/(4*R*R),z[82]/(2*R))]:
   X=x[0]-r*math.sin(2*b);Y=2*r*math.sin(b)**2+sg*x[1];L=math.hypot(X,Y);ans+=a*math.atan2(Y,X)+beta*L*L+gamma*L
  return ans
 for b,sg,a,beta,gamma in [(b1,-1,z[1]-z[9],-z[16]/(4*R*R),-z[78]/(2*R)),(b2,1,z[3]-z[9],z[20]/(4*R*R),z[82]/(2*R))]:
  Q=np.array([r*math.sin(2*b),-sg*2*r*math.sin(b)**2]);w=anchor-Q;L=np.linalg.norm(w);n=w/L;X=w[0];Y=sg*w[1];theta=math.atan2(Y,X);grad=np.array([-Y,sg*X])/(L*L)
  ell=np.linalg.norm(Q-np.array([s,0]))-(1-r);assert ell>0
  kap+=beta+a/(2*ell*ell);B+=-2*beta*Q+gamma*n+a*grad-a*anchor/(ell*ell);C+=beta*(Q@Q)-gamma*(n@Q)+a*(theta-grad@anchor+(anchor@anchor)/(2*ell*ell))
 def upper(lam):
  h=sum(lam)-kap
  if h<=0:return 1e8-h
  d=B+2*lam@disks;e=C+lam@(rad*rad-np.sum(disks*disks,axis=1));return e+d@d/(4*h)
 opt=minimize(upper,np.ones(3)*(kap+1)/3,bounds=[(0,None)]*3,constraints={'type':'ineq','fun':lambda q:sum(q)-kap-1e-7},method='SLSQP',options={'maxiter':150,'ftol':1e-12})
 primal=minimize(lambda x:-obj(x),anchor,method='SLSQP',constraints={'type':'ineq','fun':lambda x:rad*rad-np.sum((disks-x)**2,axis=1)},options={'maxiter':150,'ftol':1e-12})
 return {'outer':[r,b1,b2],'kappa':kap,'dual_upper_numeric':upper(opt.x),'multipliers':opt.x.tolist(),'dual_success':bool(opt.success),'anchor_value':obj(anchor),'primal_numeric':-primal.fun,'primal_point':primal.x.tolist(),'margin':(rad*rad-np.sum((disks-primal.x)**2,axis=1)).tolist()}
rows=[run(.38,1.107,1.0695),run(.3750951887748506,.9471039318692589,.9148561742031202),run(.38,.75,1.1)];out={'scope':'fixedouterdualproposal notcertificate','rows':rows};(P/'quadratic_disk_dual_probe.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
