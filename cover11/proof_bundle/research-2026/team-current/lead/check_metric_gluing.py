"""Independent coordinate/topology controls for analytic gluing lemma; numeric calibration only."""
from pathlib import Path
import numpy as np,json,math,collections
P=Path(__file__).parent
ns={'__file__':str(P/'q0_exact_closure_radius.py')};exec((P/'q0_exact_closure_radius.py').read_text().split('res=ceq(x0)')[0],ns)
C=ns['c'];F0=ns['faces'];F=F0+[[i,(i+1)%9,11+i] for i in range(9)]+[[11+(i-1)%9,i,11+i] for i in range(9)]
E=collections.Counter(tuple(sorted((f[k],f[(k+1)%3]))) for f in F for k in range(3));assert len(F)==29 and len(E)==48 and 20-len(E)+len(F)==1
bd={tuple(sorted((11+(i-1)%9,11+i))) for i in range(9)};assert {e for e,n in E.items() if n==1}==bd and set(E.values())=={1,2}
# Link of every interior vertex is one simple cycle; boundary vertex link one path.
for v in range(20):
 adj=collections.defaultdict(list)
 for f in F:
  if v in f:
   a,b=[x for x in f if x!=v];adj[a].append(b);adj[b].append(a)
 deg=sorted(map(len,adj.values()));assert (set(deg)=={2} if v<11 else deg.count(1)==2 and set(deg)<= {1,2})
 seen=set();todo=[next(iter(adj))]
 while todo:
  a=todo.pop()
  if a in seen:continue
  seen.add(a);todo.extend(adj[a])
 assert seen==set(adj)
rng=np.random.default_rng(843);out=[]
for trial in range(21):
 c=C.copy() if trial==0 else C+rng.uniform(-1e-7,1e-7,C.shape)
 ps=[]
 for i in range(9):
  j=(i+1)%9;d=c[j]-c[i];mid=(c[j]+c[i])/2;u=np.array([d[1],-d[0]])/np.linalg.norm(d);lam=-mid@u+math.sqrt((mid@u)**2+1-mid@mid);ps.append(mid+lam*u)
 ps=np.array(ps);verts=np.vstack([c,ps]);angles=np.zeros(20);tri_area=0.;rhos=[];oriented=[]
 for f in F:
  p=verts[f];det=np.linalg.det(np.array([p[1]-p[0],p[2]-p[0]]));assert abs(det)>1e-9
  fo=f if det>0 else [f[0],f[2],f[1]];oriented.append(fo);tri_area+=abs(det)/2
  for k,v in enumerate(f):
   a=p[(k+1)%3]-p[k];b=p[(k+2)%3]-p[k];angles[v]+=math.acos(np.clip(a@b/np.linalg.norm(a)/np.linalg.norm(b),-1,1))
  if len(rhos)<11:
   cc=np.linalg.solve(2*(p[1:]-p[0]),np.sum(p[1:]**2,axis=1)-sum(p[0]**2));rhos.append(float(np.linalg.norm(cc-p[0])))
 directed=collections.Counter((f[k],f[(k+1)%3]) for f in oriented for k in range(3))
 for e,n in E.items():
  if n==2:assert directed[e]==directed[e[::-1]]==1
 w=np.mod(np.arctan2(ps[:,1],ps[:,0])-np.roll(np.arctan2(ps[:,1],ps[:,0]),1),2*math.pi);assert max(w)<math.pi and abs(sum(w)-2*math.pi)<1e-13
 er_in=float(max(abs(angles[:11]-2*math.pi)));er_bd=float(max(abs(angles[11:]-(math.pi-(w+np.roll(w,-1))/2))))
 cap_area=float(np.sum((w-np.sin(w))/2));er_area=abs(tri_area+cap_area-math.pi)
 er_chord=max(abs(np.linalg.norm(ps[i]-ps[(i-1)%9])-2*math.sin(w[i]/2)) for i in range(9))
 rho=max(rhos+[float(np.linalg.norm(ps[i]-c[j])) for i in range(9) for j in [i,(i+1)%9]])
 assert max(er_in,er_bd,er_area,er_chord)<2e-13 and rho<.38
 out.append({'trial':trial,'max_face_and_endpoint_radius':rho,'interior_angle_error':er_in,'boundary_angle_error':er_bd,'area_error':er_area,'chord_error':er_chord})
(P/'metric_gluing_control.json').write_text(json.dumps({'scope':'21 actual coordinate examples; topology exact integer incidence, geometry numeric calibration only','V':20,'E':48,'F':29,'examples':out},indent=2));print('topology V20 E48 F29; 21 coordinate controls; max error',max(max(r[k] for k in ['interior_angle_error','boundary_angle_error','area_error','chord_error']) for r in out))
