"""Independent coordinate reconstruction and spanning-tree radius check.
Includes saved certified upper candidate + 20 perturbed test diagrams. Numerical calibration only.
"""
import numpy as np,math,json
from scipy.spatial import Delaunay
from pathlib import Path
P=Path(__file__).parent;rng=np.random.default_rng(816);out=[]
raw=json.loads(Path('n11/upper/certified_object.json').read_text(encoding='utf-8-sig'));saved=np.array([[int(x)/1e17 for x in row] for row in raw['centers_scaled_1e17']])
hubs=[0,2];rings=sorted([i for i in range(11) if i not in hubs],key=lambda i:math.atan2(saved[i,1],saved[i,0]));saved=saved[rings+hubs]
for trial in range(21):
 if trial==0:c=saved
 else:
  ang=np.arange(9)*2*math.pi/9+rng.normal(0,.015,9);rad=.8+rng.normal(0,.01,9);c=np.r_[np.c_[rad*np.cos(ang),rad*np.sin(ang)],np.array([[-.18,.01],[.2,-.02]])+rng.normal(0,.015,(2,2))]
 faces=Delaunay(c).simplices.tolist();nf=len(faces);assert nf==11
 verts=[];rho=[];angs=[]
 for f in faces:
  p=c[f];v=np.linalg.solve(2*(p[1:]-p[0]),np.sum(p[1:]**2,axis=1)-np.sum(p[0]**2));verts.append(v);rho.append(np.linalg.norm(v-p[0]));assert np.linalg.norm(v)<1
  aa=[]
  for k in range(3):
   x=p[(k+1)%3]-p[k];y=p[(k+2)%3]-p[k];aa.append(math.acos(np.clip(x@y/np.linalg.norm(x)/np.linalg.norm(y),-1,1)))
  angs.append(aa)
 edges=sorted({tuple(sorted((f[k],f[(k+1)%3]))) for f in faces for k in range(3)});hedges=[];switches={};yr={}
 for i,j in edges:
  adj=[(t,f.index(next(k for k in f if k not in (i,j)))) for t,f in enumerate(faces) if i in f and j in f];t,k=adj[0];a=angs[t][k];v=t
  if len(adj)==2:w,k2=adj[1];b=angs[w][k2]
  else:
   d=np.linalg.norm(c[i]-c[j]);mid=(c[i]+c[j])/2;n=np.array([(c[j]-c[i])[1],-(c[j]-c[i])[0]])/d
   if n@(c[next(k for k in faces[t] if k not in (i,j))]-mid)>0:n=-n
   ll=-mid@n+math.sqrt((mid@n)**2+1-mid@mid);p=mid+ll*n;b=math.atan2(d/2,ll);w=len(verts);verts.append(p);rho.append(np.linalg.norm(p-c[i]));switches[(i,j)]=p;yr[(i,j)]=w
  hedges.append((v,w,a,b))
 assert len(verts)==20 and len(hedges)==21
 logs=np.full(20,np.nan);logs[0]=0;todo=[0];used=set()
 while todo:
  v=todo.pop()
  for e,(i,j,a,b) in enumerate(hedges):
   if v not in (i,j):continue
   w=j if i==v else i
   if not np.isnan(logs[w]):continue
   logs[w]=logs[v]+(math.log(math.sin(a)/math.sin(b)) if i==v else math.log(math.sin(b)/math.sin(a)));used.add(e);todo.append(w)
 assert len(used)==19
 cycles=[logs[j]-logs[i]-math.log(math.sin(a)/math.sin(b)) for e,(i,j,a,b) in enumerate(hedges) if e not in used];assert len(cycles)==2
 k=np.exp(logs-max(logs));rmax=max(rho);err=max(abs(k-np.array(rho)/rmax))
 area=sum(rmax*rmax*k[i]*k[j]*math.sin(a+b) for i,j,a,b in hedges);ww=[]
 triangle_area=sum(2*rho[t]**2*np.prod(np.sin(angs[t])) for t in range(nf))
 switch_area=sum(rho[j]**2*math.sin(2*b)/2 for i,j,a,b in hedges if j>=nf)
 assert abs(triangle_area+switch_area-area)<1e-10
 if trial==0:
  assert max(np.linalg.norm(c[:9],axis=1))**2<=1-rmax*rmax
  assert all(0<b<math.pi/2 and rho[j]<=math.cos(b)+1e-12 for i,j,a,b in hedges if j>=nf)
 for i in range(9):
  e1=tuple(sorted(((i-1)%9,i)));e2=tuple(sorted((i,(i+1)%9)));x=switches[e1]-c[i];y=switches[e2]-c[i]
  alpha=math.atan2(np.linalg.det(np.stack([x,y])),x@y);assert alpha>=0
  yp=rmax*k[yr[e1]];yn=rmax*k[yr[e2]];ch2=yp*yp+yn*yn-2*yp*yn*math.cos(alpha);w=2*math.asin(math.sqrt(max(0,ch2))/2);ww.append(w)
  area+=yp*yn*math.sin(alpha)/2+(w-math.sin(w))/2
 assert max([err,abs(area-math.pi),abs(sum(ww)-2*math.pi)]+[abs(v) for v in cycles])<1e-9
 out.append({'trial':trial,'source':'saved upper candidate' if trial==0 else 'perturbed diagram','radius':rmax,'two_cycle_residuals':cycles,'radius_ratio_error':err,'area_error':abs(area-math.pi),'width_sum_error':abs(sum(ww)-2*math.pi)})
(P/'radius_tree_calibration.json').write_text(json.dumps(out,indent=2));print('21 coordinate/tree checks passed; saved candidate radius',out[0]['radius'],'errors',out[0])
