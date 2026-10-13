"""Numeric mechanism test: add positive triangle angles and hub winding to area relaxation.
No assertion of feasibility of geometric configurations. 11 q1 graph representatives; 1 solve each.
"""
import json,math,numpy as np
from pathlib import Path
from scipy.optimize import minimize,linprog
P=Path(__file__).parent;R=.38;pi=math.pi
J=json.loads((P/'area_triple_dual.json').read_text());out=[]
for row in J:
 if row['span']==2:continue
 start,span=row['start'],row['span'];core=[0,2,3,4,5,6,7,8];cc=core[start:]+core[:start];u,v=cc[0],cc[span]
 faces=[(0,1,2)]+[(9,cc[k],cc[k+1]) for k in range(span)]+[(10,cc[k],cc[(k+1)%8]) for k in range(span,8)]+[(9,10,u),(9,10,v)]
 edges=sorted({tuple(sorted((f[k],f[(k+1)%3]))) for f in faces for k in range(3)})
 nf=len(faces);nv=nf*3+9;theta=np.zeros((len(edges),nv));tc=np.zeros(len(edges));alpha=np.zeros((9,nv));ac=np.ones(9)*2*pi
 eq=np.zeros((nf+2,nv));rhs=np.r_[np.ones(nf)*pi,[2*pi,2*pi]]
 for t,f in enumerate(faces):
  eq[t,3*t:3*t+3]=1
  for k,i in enumerate(f):
   if i<9:alpha[i,3*t+k]=-1
   else:eq[nf+i-9,3*t+k]=1
 for e,(i,j) in enumerate(edges):
  adj=[(t,f.index(next(k for k in f if k not in (i,j)))) for t,f in enumerate(faces) if i in f and j in f]
  for t,k in adj:theta[e,3*t+k]=-1
  if len(adj)==2:tc[e]=pi
  else:
   bi=next(k for k in range(9) if set((k,(k+1)%9))==set((i,j)))
   tc[e]=pi/2;theta[e,3*nf+bi]=1
   alpha[i,3*nf+bi]=-1;alpha[j,3*nf+bi]=-1
 mat=np.r_[theta,alpha];const=np.r_[tc,ac]
 # initialize with linear feasible angles
 lp=linprog(np.zeros(nv),A_ub=np.r_[mat,-mat],b_ub=np.r_[pi-const,const],A_eq=eq,b_eq=rhs,bounds=[(0,pi)]*(3*nf)+[(-pi/2,pi/2)]*9,method='highs')
 assert lp.success
 def calc(x):
  t=tc+theta@x;a=ac+alpha@x;s=np.maximum(.5,np.sin(a/2));w=2*np.arcsin(R*s)
  wp=np.where(a>pi/3,R*np.cos(a/2)/np.sqrt(1-R*R*np.sin(a/2)**2),0)
  F=R*R*np.sin(a)/2+(w-np.sin(w))/2;Fp=R*R*np.cos(a)/2+(1-np.cos(w))*wp/2
  ang=x[:3*nf].reshape(nf,3);gam=x[3*nf:]
  sins=np.sin(ang);coss=np.cos(ang)
  val=2*R*R*np.prod(sins,axis=1).sum()+R*R*np.maximum(0,np.sin(2*gam)).sum()+F.sum()
  grad=Fp@alpha
  for k in range(3):grad[k:3*nf:3]+=2*R*R*coss[:,k]*sins[:,(k+1)%3]*sins[:,(k+2)%3]
  grad[3*nf:]+=np.where(gam>0,2*R*R*np.cos(2*gam),0)
  return val,grad,w,wp
 def con(x):
  z=mat@x+const;_,_,w,wp=calc(x)
  return np.r_[z,pi-z,sum(w)-2*pi,sum(w[3:])-(2*pi-2*math.asin(2*R))]
 def jac(x):
  _,_,w,wp=calc(x)
  return np.r_[mat,-mat,(wp@alpha)[None,:],(wp[3:]@alpha[3:])[None,:]]
 seed=next(j['x'] for j in json.loads((P/'area_face_angles.json').read_text()) if j['start']==start and j['span']==span)
 o=minimize(lambda x:-calc(x)[0],np.array(seed),jac=lambda x:-calc(x)[1],method='SLSQP',bounds=[(0,pi)]*(3*nf)+[(-pi/2,pi/2)]*9,constraints=[{'type':'eq','fun':lambda x:eq@x-rhs,'jac':lambda x:eq},{'type':'ineq','fun':con,'jac':jac}],options={'maxiter':700,'ftol':1e-10})
 res={'start':start,'span':span,'area':float(-o.fun),'success':bool(o.success),'min_constraint':float(min(con(o.x))),'equality_residual':float(max(abs(eq@o.x-rhs))),'min_face_angle':float(min(o.x[:3*nf])),'x':o.x.tolist(),'faces':faces,'edges':edges}
 out.append(res);(P/'area_triangle_angles.json').write_text(json.dumps(out,indent=2))
 print(start,span,'area',round(-o.fun,9),'min',round(min(con(o.x)),9),'ok',o.success,flush=True)
