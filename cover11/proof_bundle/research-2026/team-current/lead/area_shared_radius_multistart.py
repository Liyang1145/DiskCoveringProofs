"""Bounded diagnostic: enforce shared face/switch radii and exact boundary chord sectors.
Finite positive angle/log-radius domain here is NUMERIC ONLY, not full degeneracy coverage.
"""
import numpy as np,math,json
from pathlib import Path
from scipy.optimize import minimize
P=Path(__file__).parent;R=.38;pi=math.pi
J=[j for j in json.loads((P/'area_shared_radius.json').read_text()) if j['span']==4];out=[];rng=np.random.default_rng(8162)
for row in J*4:
 start,span=row['start'],row['span']
 if start==7:continue
 core=[0,2,3,4,5,6,7,8];cc=core[start:]+core[:start];faces=row['faces'];edges=row['edges'];nf=len(faces);na=3*nf+9;nv=na+nf+9
 eq=np.zeros((nf+2,nv));rhs=np.r_[np.ones(nf)*pi,[2*pi,2*pi]];alpha=np.zeros((9,nv));ac=np.ones(9)*2*pi
 A=np.zeros((len(edges),nv));B=np.zeros_like(A);bc=np.zeros(len(edges));U=np.zeros_like(A);V=np.zeros_like(A)
 for t,f in enumerate(faces):
  eq[t,3*t:3*t+3]=1
  for k,i in enumerate(f):
   if i<9:alpha[i,3*t+k]=-1
   else:eq[nf+i-9,3*t+k]=1
 for ee,(i,j) in enumerate(edges):
  adj=[(t,f.index(next(k for k in f if k not in (i,j)))) for t,f in enumerate(faces) if i in f and j in f];t,k=adj[0];A[ee,3*t+k]=1;U[ee,na+t]=1
  if len(adj)==2:t,k=adj[1];B[ee,3*t+k]=1;V[ee,na+t]=1
  else:
   bi=next(k for k in range(9) if set((k,(k+1)%9))=={i,j});B[ee,3*nf+bi]=-1;bc[ee]=pi/2;V[ee,na+nf+bi]=1
   alpha[i,3*nf+bi]=-1;alpha[j,3*nf+bi]=-1
 def calc(x):
  a=A@x;b=B@x+bc;al=ac+alpha@x;u=np.exp(U@x)*R;v=np.exp(V@x)*R
  y=R*np.exp(x[na+nf:]);yp=np.roll(y,1);ch2=yp*yp+y*y-2*yp*y*np.cos(al)
  w=2*np.arcsin(np.sqrt(np.clip(ch2,1e-16,3.99))/2)
  area=np.sum(u*v*np.sin(a+b))+np.sum(yp*y*np.sin(al)/2+(w-np.sin(w))/2)
  return area,w,a,b,al
 def ceq(x):return np.r_[eq@x-rhs,(U-V)@x+np.log(np.sin(A@x))-np.log(np.sin(B@x+bc))]
 def cineq(x):
  area,w,a,b,al=calc(x)
  return np.r_[al,pi-al,pi-a-b,sum(w)-2*pi,sum(w[3:])-2*pi+2*math.asin(2*R)]
 # best least-squares radius ratios; normalization no radius exceeds R
 x0=np.array(row['x'])+rng.normal(0,.07,nv)
 a=A@x0;b=B@x0+bc
 M=(U-V)[:,na:];rr=np.linalg.lstsq(M,np.log(np.sin(b))-np.log(np.sin(a)),rcond=None)[0];rr-=max(rr);x0[na:]=rr
 bounds=[(1e-5,pi-1e-5)]*(nf*3)+[(-pi/2+1e-5,pi/2-1e-5)]*9+[(-6,0)]*(nf+9)
 o=minimize(lambda x:-calc(x)[0],x0,method='SLSQP',bounds=bounds,constraints=[{'type':'eq','fun':ceq},{'type':'ineq','fun':cineq}],options={'maxiter':450,'ftol':1e-10})
 res={'start':start,'span':span,'area':float(-o.fun),'min_ineq':float(min(cineq(o.x))),'max_eq':float(max(abs(ceq(o.x)))),'success':bool(o.success),'message':str(o.message),'x':o.x.tolist(),'faces':faces,'edges':edges};out.append(res)
 (P/'area_shared_radius_multistart.json').write_text(json.dumps(out,indent=2));print(start,span,round(-o.fun,9),round(min(cineq(o.x)),9),round(max(abs(ceq(o.x))),9),o.success,flush=True)
