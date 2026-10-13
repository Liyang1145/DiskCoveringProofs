"""Independent Euclidean-coordinate calibration of compatible-edge/angle identities.
Numeric calibration, NOT global certificate. 20 perturbed two-hub nine-ring diagrams.
"""
import numpy as np,math,json
from scipy.spatial import Voronoi,Delaunay
from pathlib import Path
P=Path(__file__).parent;rng=np.random.default_rng(813);records=[]
for trial in range(20):
 ang=np.arange(9)*2*math.pi/9+rng.normal(0,.015,9);rad=.8+rng.normal(0,.01,9)
 c=np.r_[np.c_[rad*np.cos(ang),rad*np.sin(ang)],np.array([[-.18,.01],[.2,-.02]])+rng.normal(0,.015,(2,2))]
 de=Delaunay(c);faces=de.simplices.tolist();A=[];V=[]
 for f in faces:
  p=c[f];v=np.linalg.solve(2*(p[1:]-p[0]),np.sum(p[1:]**2,axis=1)-np.sum(p[0]**2));V.append(v)
  assert np.linalg.norm(v)<1
  aa=[]
  for k in range(3):
   x=p[(k+1)%3]-p[k];y=p[(k+2)%3]-p[k];aa.append(math.acos(np.clip(x@y/np.linalg.norm(x)/np.linalg.norm(y),-1,1)))
  A.append(aa)
 edges=sorted({tuple(sorted((f[k],f[(k+1)%3]))) for f in faces for k in range(3)})
 switches={};Bs={};direct=0;old=0;bound=0;R=max(np.linalg.norm(V[t]-c[f[0]]) for t,f in enumerate(faces))
 E=[]
 for i,j in edges:
  adj=[(t,f.index(next(k for k in f if k not in (i,j)))) for t,f in enumerate(faces) if i in f and j in f]
  d=np.linalg.norm(c[i]-c[j]);mid=(c[i]+c[j])/2;t,k=adj[0];a=A[t][k];v=V[t]
  if len(adj)==2:
   tt,kk=adj[1];b=A[tt][kk];w=V[tt]
  else:
   tangent=(c[j]-c[i])/d;n=np.array([tangent[1],-tangent[0]])
   if n@(c[next(k for k in faces[t] if k not in (i,j))]-mid)>0:n=-n
   lam=-mid@n+math.sqrt((mid@n)**2+1-mid@mid);w=mid+lam*n
   b=math.atan2(d/2,lam);switches[(i,j)]=w;Bs[(i,j)]=b
  R=max(R,np.linalg.norm(w-c[i]));E.append((i,j,a,b,d,v,w))
 errs=[]
 for i,j,a,b,d,v,w in E:
  ex=d*np.linalg.norm(v-w)/2;formula=d*d/4*(1/math.tan(a)+1/math.tan(b))
  assert a+b<=math.pi+1e-10
  errs.append(abs(ex-formula));direct+=ex
  G=R*R*math.sin(a+b)*min(math.sin(a)/math.sin(b),math.sin(b)/math.sin(a))
  assert ex<=G+1e-10
  bound+=G;old+=R*R*math.sin(a+b)
 alpha=[];sector=0;ringerr=[]
 for i in range(9):
  e1=tuple(sorted(((i-1)%9,i)));e2=tuple(sorted((i,(i+1)%9)));p=switches[e1];q=switches[e2];x=p-c[i];y=q-c[i]
  a=math.atan2(np.linalg.det(np.stack([x,y])),x@y);assert 0<a<math.pi
  w=math.atan2(np.linalg.det(np.stack([p,q])),p@q);assert 0<w<math.pi
  sector+=np.linalg.norm(x)*np.linalg.norm(y)*math.sin(a)/2+(w-math.sin(w))/2
  asum=sum(A[t][f.index(i)] for t,f in enumerate(faces) if i in f)
  ringerr.append(abs(a+asum-Bs[e1]-Bs[e2]-math.pi))
 huberr=[abs(sum(A[t][f.index(i)] for t,f in enumerate(faces) if i in f)-2*math.pi) for i in [9,10]]
 assert max(errs+ringerr+huberr+[abs(direct+sector-math.pi)])<1e-10
 records.append({'trial':trial,'edge_identity_error':max(errs),'ring_equation_error':max(ringerr),'hub_error':max(huberr),'total_area_error':abs(direct+sector-math.pi),'G_bound':bound,'old_bound':old})
(P/'edge_interface_calibration.json').write_text(json.dumps(records,indent=2));print('20 coordinate calibrations passed; max error',max(max(r[k] for k in ['edge_identity_error','ring_equation_error','hub_error','total_area_error']) for r in records))
