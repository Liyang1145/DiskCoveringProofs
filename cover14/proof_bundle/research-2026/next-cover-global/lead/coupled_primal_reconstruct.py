"""Numeric reconstruction audit; not cover certification."""
from coupled_primal_probe import *
def cross(a,b):return float(a[0]*b[1]-a[1]*b[0])
def reconstruct(z):
 be=z[:ne];xr=z[ne:ne+nf];ya=z[ne+nf:];lengths={};gamma={}
 for k,e in enumerate(edges):
  for f in E[e]:
   other=[j for j in E[e]if j!=f];t=xr[other[0]]if other else ya[bedges.index(e)];g=math.atan2(t*math.sin(be[k]),xr[f]-t*math.cos(be[k]));gamma[f,e]=g;ll=2*U*xr[f]*math.sin(g)
   if e in lengths:assert abs(ll-lengths[e])<1e-9
   lengths[e]=ll
 V={};first=faces[0];V[first[0]]=np.array([0.,0.]);V[first[1]]=np.array([lengths[tuple(sorted(first[:2]))],0.])
 for _ in range(20):
  for f in faces:
   known=[i for i in f if i in V];unknown=[i for i in f if i not in V]
   if len(known)!=2 or len(unknown)!=1:continue
   a,b=known;c=unknown[0];u,v=V[a],V[b];ll=np.linalg.norm(v-u);ac=lengths[tuple(sorted((a,c)))];bc=lengths[tuple(sorted((b,c)))];s=(ac*ac-bc*bc+ll*ll)/(2*ll);height=math.sqrt(max(0,ac*ac-s*s));direction=(v-u)/ll;normal=np.array([-direction[1],direction[0]]);sign=1 if cross(C[b]-C[a],C[c]-C[a])>0 else -1;V[c]=u+s*direction+sign*height*normal
 assert len(V)==14;V=np.array([V[i]for i in range(14)]);res=max(abs(np.linalg.norm(V[u]-V[v])-lengths[u,v])for u,v in edges);A=[]
 for e in bedges:
  a,b=e;f=E[e][0];c=next(i for i in faces[f]if i not in e)
  if cross(V[b]-V[a],V[c]-V[a])<0:a,b=b,a
  u,v=V[a],V[b];ll=np.linalg.norm(v-u);direction=(v-u)/ll;normal=np.array([-direction[1],direction[0]]);phi=math.pi/2-gamma[f,e]-be[edges.index(e)];A.append((u+v)/2+ll/2*math.tan(phi)*normal)
 A=np.array(A);mat=np.c_[2*A,np.ones(len(A))];rhs=np.sum(A*A,axis=1);fit=np.linalg.lstsq(mat,rhs,rcond=None)[0];origin=fit[:2];radius=math.sqrt(fit[2]+origin@origin);anchor_rad=np.linalg.norm(A-origin,axis=1);vr=V-origin
 nearest=[]
 for k,e in enumerate(bedges):nearest.append(min(np.sum((V-A[k])**2,axis=1))-np.sum((V[e[0]]-A[k])**2))
 for f in faces:
  a,b,c=V[f];o=np.linalg.solve(2*np.array([b-a,c-a]),np.array([b@b-a@a,c@c-a@a]));nearest.append(min(np.sum((V-o)**2,axis=1))-np.sum((V[f[0]]-o)**2))
 return {'edge_closure_residual':float(res),'anchor_fitted_radius':float(radius),'anchor_radial_spread':float(max(anchor_rad)-min(anchor_rad)),'max_unit_anchor_error':float(max(abs(anchor_rad-1))),'worst_emptycircle_margin':float(min(nearest)),'boundary_innernorm_excess':float(max(np.linalg.norm(vr[v])for v in boundary)-math.sqrt(1-U*U)),'centers':vr.tolist(),'anchors':(A-origin).tolist()}
if __name__=='__main__':
 data=json.loads((P/'coupled-primal-probe.json').read_text())['runs'];out=[]
 for j,z in [(-1,x0)]+[(r['start'],np.array(r['solution']))for r in data]:
  rec=reconstruct(z);rec['start']=j;out.append(rec);print({k:v for k,v in rec.items()if k not in ['centers','anchors']},flush=True)
 (P/'coupled-primal-reconstruction.json').write_text(json.dumps({'status':'numeric_geometry_reconstruction_only','runs':out},indent=2))
