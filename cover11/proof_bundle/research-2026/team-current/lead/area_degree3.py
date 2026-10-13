"""Numeric concave-relaxation candidates for degree-three hub, all q<=1 graphs."""
import numpy as np, math, json
from scipy.optimize import minimize
from pathlib import Path
r=.38
F=lambda a: np.arcsin(r*np.sin(a/2))-.5*np.sin(2*np.arcsin(r*np.sin(a/2)))+.5*r*r*np.sin(a)
Fp=lambda a:r*r*(r*np.sin(a/2)**2*np.cos(a/2)/np.sqrt(1-r*r*np.sin(a/2)**2)+.5*np.cos(a))
fp=lambda a:r*np.cos(a/2)/np.sqrt(1-r*r*np.sin(a/2)**2)
results=[]
for q in (0,1):
 core=[i for i in range(9) if not(q and i==1)]
 for j in range(1 if not q else len(core)):
  cc=core[j:]+core[:j];u,v=cc[:2]
  edges=[(i,(i+1)%9) for i in range(9)]+([(0,2)] if q else [])
  edges +=[(9,u),(9,v)]+[(10,x) for x in cc]+[(9,10)]
  E=len(edges);mat=np.zeros((11,E+9))
  for k,(i,jj) in enumerate(edges):mat[i,k]=mat[jj,k]=1
  for i in range(9):mat[i,E+i]=1
  area=lambda x:r*r*np.sin(x[:E]).sum()+F(x[E:]).sum()
  cover=lambda x:2*np.arcsin(r*np.sin(x[E:]/2)).sum()-2*math.pi
  x0=np.ones(E+9)*1.1;x0[E:]=2.3
  sol=minimize(lambda x:-area(x),x0,method='SLSQP',bounds=[(1e-7,math.pi-1e-7)]*(E+9),constraints=[{'type':'eq','fun':lambda x:mat@x-2*math.pi},{'type':'ineq','fun':cover}],options={'ftol':1e-12,'maxiter':500})
  x=sol.x;grad=np.r_[r*r*np.cos(x[:E]),Fp(x[E:])];cg=np.r_[np.zeros(E),fp(x[E:])]
  # grad(area)+lambda grad(cover)=mat.T mu, lambda>=0
  MM=np.column_stack([mat.T,-cg]);mult=np.linalg.lstsq(MM,grad,rcond=None)[0]
  results.append({'q':q,'edge':[u,v],'area':float(area(x)),'cover':float(cover(x)),'angles':x.tolist(),'edges':edges,'lambda':float(mult[-1]),'mu':mult[:-1].tolist(),'stationarity':float(np.max(abs(MM@mult-grad))),'min_angle':float(min(x)),'max_angle':float(max(x)),'success':bool(sol.success)})
  print(q,(u,v),round(area(x),10),'lambda',round(mult[-1],8),'resid',round(results[-1]['stationarity'],8),flush=True)
Path(__file__).with_suffix('.json').write_text(json.dumps(results,indent=2))
