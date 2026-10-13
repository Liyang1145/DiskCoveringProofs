"""Independent Cartesian development of numeric reduced q11 closure; NOT rigorous proof."""
from q11_reduced_closure_probe import *
D=json.loads((P/'q11-closure-repair.json').read_text());z=np.array(D['runs'][0]['solution']);d=metric(z);beta=z[:ne];R=d['real_radii'];a=d['anchor_radii'];scale=float(d['chords']@d['lengths']/(d['lengths']@d['lengths']))
cross=lambda a,b:float(a[0]*b[1]-a[1]*b[0])
# Orient face complex by reverse shared-edge directions (not candidate coordinates).
ori={0:tuple(faces[0])}
def direction(f,u,v):
 for i in range(3):
  if f[i]==u and f[(i+1)%3]==v:return 1
  if f[i]==v and f[(i+1)%3]==u:return -1
for _ in faces:
 for k,fs in enumerate(ef):
  if len(fs)!=2:continue
  f,g=fs;u,v=edges[k]
  if f not in ori and g in ori:f,g=g,f
  if f in ori and g not in ori:
   t=tuple(faces[g]);ori[g]=t if direction(t,u,v)==-direction(ori[f],u,v)else (t[0],t[2],t[1])
assert len(ori)==nf
length={}
for k,fs in enumerate(ef):
 f=fs[0];t=R[fs[1]]if len(fs)==2 else a[ai[k]];gamma=math.atan2(t*math.sin(beta[k]),R[f]-t*math.cos(beta[k]));length[edges[k]]=2*R[f]*math.sin(gamma)
first=ori[0];V={first[0]:np.array([0.,0.]),first[1]:np.array([length[tuple(sorted(first[:2]))],0.])}
for _ in faces:
 for f in ori.values():
  for j in range(3):
   u,v,w=f[j],f[(j+1)%3],f[(j+2)%3]
   if u not in V or v not in V or w in V:continue
   e=(V[v]-V[u]);ll=np.linalg.norm(e);e/=ll;lu=length[tuple(sorted((u,w)))];lv=length[tuple(sorted((v,w)))];x=(lu*lu-lv*lv+ll*ll)/(2*ll);h=math.sqrt(max(0,lu*lu-x*x));V[w]=V[u]+x*e+h*np.array([-e[1],e[0]])
assert len(V)==14
VV=np.array([V[i]for i in range(14)]);edgeerr=max(abs(np.linalg.norm(V[u]-V[v])-ll)for (u,v),ll in length.items());A=[]
for k in cy:
 u,v=edges[k];f=ori[ef[k][0]]
 if direction(f,u,v)<0:u,v=v,u
 vec=V[v]-V[u];ll=np.linalg.norm(vec);vec/=ll;h=math.sqrt(max(0,a[ai[k]]**2-ll*ll/4));A.append((V[u]+V[v])/2-h*np.array([-vec[1],vec[0]]))
A=np.array(A);fit=np.linalg.lstsq(np.c_[2*A,np.ones(q)],np.sum(A*A,axis=1),rcond=None)[0];O=fit[:2];cr=math.sqrt(fit[2]+O@O);VV=scale*(VV-O);AA=scale*(A-O)
# independent continuous coverage maxima: boundary pair equal-distance crossings + stationary distances;
# interior Voronoi vertices from every triple (non-nearest triples harmless if evaluated min).
points=[]
for i,c in enumerate(VV):
 n=np.linalg.norm(c)
 if n>0:points.extend([c/n,-c/n])
 for j in range(i):
  v=c-VV[j];rhs=(c@c-VV[j]@VV[j])/2;nv=np.linalg.norm(v)
  if nv>0 and abs(rhs)<=nv:
   x=rhs/nv;unit=v/nv;perp=np.array([-unit[1],unit[0]]);points.extend([x*unit+math.sqrt(max(0,1-x*x))*perp,x*unit-math.sqrt(max(0,1-x*x))*perp])
for i,j,k in combinations(range(14),3):
 M=2*np.array([VV[j]-VV[i],VV[k]-VV[i]])
 if abs(np.linalg.det(M))<1e-12:continue
 O1=np.linalg.solve(M,np.array([VV[j]@VV[j]-VV[i]@VV[i],VV[k]@VV[k]-VV[i]@VV[i]]))
 if O1@O1<=1:points.append(O1)
points.append(np.zeros(2));actual=max(math.sqrt(min(np.sum((VV-p)**2,axis=1)))for p in points)
out={'status':'numeric_independent_cartesian_interface_control','graph':58,'edge_length_error':float(edgeerr),'unit_circle_radius_error':float(abs(scale*cr-1)),'anchor_radial_error':float(max(abs(np.linalg.norm(AA,axis=1)-1))),'predicted_radius':float(scale*max(max(a),max(R))),'finite_geometric_cover_radius':actual,'centers':VV.tolist(),'anchors':AA.tolist(),'source_closure_residual':D['runs'][0]['closure_residual']};assert edgeerr<1e-10 and out['anchor_radial_error']<1e-10 and actual<=out['predicted_radius']+1e-10;(P/'q11-cartesian-replay.json').write_text(json.dumps(out,indent=2));print({k:v for k,v in out.items()if k not in ['centers','anchors']})
