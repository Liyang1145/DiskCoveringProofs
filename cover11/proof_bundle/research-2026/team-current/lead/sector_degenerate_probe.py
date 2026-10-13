"""Bounded factor diagnostic: can one degenerate sector be excluded by EXISTING fixed dual?
29 unconstrained factors plus9alpha=pi boundary tests, numerical maxima only.
"""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
from pathlib import Path
import numpy as np,math,json
from scipy.optimize import differential_evolution, minimize_scalar
P=Path(__file__).parent;J=json.loads((P/'q0_closure_dual_0_4.json').read_text());z=np.array(J['z']);R=.38;pi=math.pi
faces=J['faces'];edges=[tuple(e) for e in J['edges']];adj={e:[t for t,f in enumerate(faces) if e[0] in f and e[1] in f] for e in edges}
qmin=4*math.sin(pi-8*math.asin(R))**2/R**2
const=pi*(sum(z[:9])+2*sum(z[9:11])+sum(z[50:71])-2*z[71])-pi*sum(z[112:])
def quad(A,B):
 vals=[0,A+B]
 if A<0 and 0<-B/(2*A)<1:vals.append(-B*B/(4*A))
 return max(vals)
vals=[]
for t,f in enumerate(faces):
 co=[];dd=[];ll=[]
 for k,i in enumerate(f):
  e=tuple(sorted(j for j in f if j!=i));j=edges.index(e);sgn=1 if adj[e][0]==t else -1;co.append(-z[i]-z[50+j]);dd.append(sgn*z[11+j]);ll.append(sgn*z[73+j])
 def fun(v):
  a,b=v;c=pi-a-b
  if c<0:return 1000+100*(-c)
  a=np.array([a,b,c]);sn=np.sin(a)
  return -(np.array(co)@a+quad(2*R*R*np.prod(sn)+np.array(dd)@(sn*sn),np.array(ll)@sn))
 sol=differential_evolution(fun,[(0,pi),(0,pi)],seed=845+t,popsize=12,maxiter=150,tol=1e-10);vals.append(-sol.fun)
for i in range(9):
 j=(i+1)%9;e=edges.index(tuple(sorted((i,j))));c=z[i]+z[j]-z[50+e]+2*z[112+i];d=z[11+e];e0=z[32+2*i+1]+z[32+2*j];g=-z[73+e];h=z[94+2*i+1]+z[94+2*j]
 fun=lambda b:-(c*b+quad(R*R*math.sin(2*b)/2-d*math.sin(b)**2+e0,g*math.sin(b)+h))
 sol=differential_evolution(lambda v:fun(v[0]),[(0,pi/2)],seed=850+i,maxiter=100,tol=1e-10);vals.append(-sol.fun)
rows=[]
for i in range(9):
 def fun(v):
  a,u,vv=v;q=(u-vv)**2+4*u*vv*math.sin(a/2)**2
  if q<qmin:return 1000+100*(qmin-q)
  w=2*math.asin(R*math.sqrt(q)/2);L=math.atan2(vv*math.sin(a),u-vv*math.cos(a));T=pi-a-L
  f=R*R*u*vv*math.sin(a)/2+(w-math.sin(w))/2-z[i]*a-z[32+2*i]*u*u-z[33+2*i]*vv*vv-z[94+2*i]*u-z[95+2*i]*vv+z[71]*w+z[112+(i-1)%9]*(L+w/2)+z[112+i]*(T+w/2)
  return -f
 sol=differential_evolution(fun,[(0,pi),(0,1),(0,1)],seed=860+i,popsize=15,maxiter=250,tol=1e-10);vals.append(-sol.fun)
 ss=differential_evolution(lambda v:fun([pi,*v]),[(0,1),(0,1)],seed=870+i,maxiter=200,tol=1e-10)
 rows.append({'sector':i,'unrestricted_max_numeric':-sol.fun,'alpha_pi_max_numeric':-ss.fun,'loss_numeric':ss.fun-sol.fun,'degenerate_endpoint_radii':ss.x.tolist()})
total=float(const+sum(vals))
for row in rows:row['conditional_full_dual_numeric']=total-row['loss_numeric']
out={'scope':'finite numerical maximization, NOT uppercertificate; tests fixedexistingdual sufficiency fordegeneratesector exclusion','R':R,'full_dual_numeric':total,'factors':vals,'sectors':rows}
(P/'sector_degenerate_probe.json').write_text(json.dumps(out,indent=2));print('total',total);print([(r['sector'],r['conditional_full_dual_numeric']) for r in rows])
