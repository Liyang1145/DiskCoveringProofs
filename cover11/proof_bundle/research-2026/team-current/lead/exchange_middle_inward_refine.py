"""Bounded five-round continuous separation exchange, proposal ONLY; all outputs isolated."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
from pathlib import Path
import numpy as np,math,json,time,sys
from scipy.optimize import linprog,differential_evolution,minimize,NonlinearConstraint,minimize_scalar
P=Path(__file__).parent;R=.38;pi=math.pi;tmin=75/76
src=(P/'propose_middle_sector_inward_dual.py').read_text();marker='\nK=len(factors);arows=[]';assert src.count(marker)==1
ns={'__file__':str(P/'propose_middle_sector_inward_dual.py')};exec(src.split(marker)[0],ns)
factors=ns['factors'];nz=ns['nz'];const=ns['const'];faces=ns['ns']['faces'];edges=[tuple(e) for e in ns['ns']['edges']];adj={e:[t for t,f in enumerate(faces) if all(i in f for i in e)] for e in edges}
qmin=4*math.sin(pi-8*math.asin(R))**2/R**2
# linear atom: exact modeled expression evaluated double, not certification
def atom(fi,x):
 m=np.zeros(nz)
 if fi<11:
  a,b,t=x;aa=[a,b,pi-a-b];sn=np.sin(aa);v=2*R*R*t*t*np.prod(sn)
  for k,i in enumerate(faces[fi]):
   e=tuple(sorted(j for j in faces[fi] if j!=i));ee=edges.index(e);sgn=1 if adj[e][0]==fi else -1;m[i]-=aa[k];m[50+ee]-=aa[k];m[11+ee]+=sgn*t*t*sn[k]**2;m[73+ee]+=sgn*t*sn[k]
 elif fi<20:
  bi=fi-11;b,t=x;i,j=bi,(bi+1)%9;ee=edges.index(tuple(sorted((i,j))));v=R*R*t*t*math.sin(2*b)/2
  m[i]+=b;m[j]+=b;m[50+ee]-=b;m[112+bi]+=2*b;m[11+ee]-=t*t*math.sin(b)**2;m[73+ee]-=t*math.sin(b);m[33+2*i]+=t*t;m[32+2*j]+=t*t;m[95+2*i]+=t;m[94+2*j]+=t
 else:
  i=fi-20;a,u,vv=x;Q=(u-vv)**2+4*u*vv*math.sin(a/2)**2;w=2*math.asin(R*math.sqrt(Q)/2);L=math.atan2(vv*math.sin(a),u-vv*math.cos(a));T=pi-a-L
  v=R*R*u*vv*math.sin(a)/2+(w-math.sin(w))/2;m[i]-=a;m[32+2*i]-=u*u;m[33+2*i]-=vv*vv;m[94+2*i]-=u;m[95+2*i]-=vv;m[71]+=w;m[112+(i-1)%9]+=L+w/2;m[112+i]+=T+w/2
 return float(v),m

def value(fi,x,z):v,m=atom(fi,x);return v+m@z

def radiusarg(fi,angles,z):
 c=value(fi,[*angles,0],z);f1=value(fi,[*angles,1],z)-c;fh=value(fi,[*angles,.5],z)-c;A=2*f1-4*fh;B=f1-A
 ts=[0.,1.]
 if A<0 and 0<-B/(2*A)<1:ts.append(-B/(2*A))
 return max(ts,key=lambda t:A*t*t+B*t)

def margin(x):
 a,u,v=x;Q=(u-v)**2+4*u*v*math.sin(a/2)**2;h=R*math.sqrt(Q)/2;k=math.sqrt(1-h*h)
 return np.r_[Q-qmin,u*v*(k*math.sin(a)-h*math.cos(a))-max(tmin*tmin,u*u,v*v)*h]

def oracle(fi,z,roundno,old=None):
 if fi<20:
  dim=2 if fi<11 else 1;bounds=[(0,pi)]*2 if fi<11 else [(0,pi/2)]
  def f(a):
   if fi<11 and sum(a)>pi:return 1e3+sum(a)-pi
   return -value(fi,[*a,radiusarg(fi,a,z)],z)
  s=differential_evolution(f,bounds,seed=900+fi+roundno*29,popsize=10,maxiter=90,tol=1e-9)
  x=[*s.x,radiusarg(fi,s.x,z)]
 elif fi==22:
  f=lambda t:-value(fi,[pi,t,t],z)
  s=minimize_scalar(f,bounds=(tmin,1),method='bounded');t=min([tmin,1,s.x],key=f);x=[pi,t,t]
 else:
  bounds=[(.0233,pi),(1e-5,1),(1e-5,1)]
  s=differential_evolution(lambda a:-value(fi,a,z),bounds,constraints=NonlinearConstraint(margin,0,np.inf),seed=1000+fi+roundno*29,popsize=10,maxiter=95,polish=False)
  choices=[]
  for x0 in [s.x,[1.,1.,1.],old if old is not None else [3.,1.,1.]]:
   t=minimize(lambda a:-value(fi,a,z),x0,method='SLSQP',bounds=bounds,constraints={'type':'ineq','fun':margin},options={'maxiter':130,'ftol':1e-11})
   if min(margin(t.x))>=-1e-8:choices.append(t.x)
  assert choices;x=max(choices,key=lambda a:value(fi,a,z))
 return np.array(x),float(value(fi,x,z))
# Finite LP planes include original samples plus everyoffgridatom. No sampledmax calledcertified.
arows=[];rhs=[];used=[set() for _ in factors]
def add(fi,v,m,key):
 if key in used[fi]:return
 used[fi].add(key);a=np.zeros(nz+29);a[:nz]=m;a[nz+fi]=-1;arows.append(a);rhs.append(-v)
def separate_grid(z):
 vals=[]
 for fi,(vv,mm) in enumerate(factors):
  f=vv+mm@z;idx=int(np.argmax(f));add(fi,vv[idx],mm[idx],('grid',idx));vals.append(float(f[idx]))
 return float(const@z+sum(vals))
bounds=[(-3,3)]*50+[(0,3)]*23+[(-3,3)]*48+[(None,None)]*29;bounds[72]=(0,0)
z=np.array(json.loads((P/'middle_sector_inward_dual_proposal.json').read_text())['z']);separate_grid(z);old=[None]*29;history=[];best=1e9
previous=json.loads((P/'middle_inward_exchange_history.json').read_text())
for r in previous:
 for fi,x in enumerate(r['atoms']):
  vv,mm=atom(fi,x);add(fi,vv,mm,('saved',r['round']))
old=[np.array(x) for x in previous[-1]['atoms']]
for roundno in range(5,15):
 # convergefiniteLP withcurrentplanes
 for it in range(120):
  sol=linprog(np.r_[const,np.ones(29)],A_ub=np.array(arows),b_ub=rhs,bounds=bounds,method='highs');assert sol.success
  z=sol.x[:nz];grid=separate_grid(z)
  if grid<=sol.fun+1e-7:break
 vals=[];atoms=[]
 for fi in range(29):
  x,v=oracle(fi,z,roundno,old[fi]);old[fi]=x;vv,mm=atom(fi,x);add(fi,vv,mm,('off',roundno));vals.append(v);atoms.append(x.tolist())
 total=float(const@z+sum(vals));history.append({'round':roundno,'finiteLP':float(sol.fun),'continuous_numeric':total,'z':z.tolist(),'atoms':atoms,'factor_values':vals})
 print(roundno,'finite',sol.fun,'continuous',total,flush=True)
 if total<best:
  best=total;(P/'middle_inward_exchange_refined_best.json').write_text(json.dumps({'start':0,'span':4,'faces':faces,'edges':edges,'z':z.tolist(),'numeric_total':total,'scope':'proposal only,5rounds continuousnumericalexchange; notrigorousupper'},indent=2))
 (P/'middle_inward_exchange_refined_history.json').write_text(json.dumps(history,indent=2))
print('BEST',best,flush=True)
