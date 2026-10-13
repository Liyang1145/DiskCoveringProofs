"""Numeric consistency diagnostic, fixed candidategraph and5 bounded starts."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
from boundary_radius_control import *
from scipy.optimize import minimize
edges=sorted(E);bedges=[e for e in edges if len(E[e])==1];ne=len(edges);nf=len(faces);nb=len(bedges);fedge=[[edges.index(tuple(sorted(e)))for e in combinations(f,2)]for f in faces];boundary=sorted(set(v for e in bedges for v in e));hidden=sorted(set(range(14))-set(boundary));inc=[[k for k,e in enumerate(edges)if v in e]for v in range(14)];bi=[[bedges.index(e)for e in bedges if v in e]for v in boundary];assert all(len(x)==2 for x in bi)
x0=np.r_[[beta[e]for e in edges],np.array(R)/U,[np.linalg.norm(anchors[e]-C[e[0]])/U for e in bedges]]
def unpack(z):
 be=z[:ne];xr=z[ne:ne+nf];ya=z[ne+nf:];al=np.array([2*math.pi-sum(be[k]for k in inc[v])for v in boundary]);theta=[];wedge=0
 for a,(i,j)in zip(al,bi):
  u,v=ya[i],ya[j];ch=U*np.sqrt(max(0,u*u+v*v-2*u*v*math.cos(a)));th=2*math.asin(min(1,ch/2));theta.append(th);wedge+=U*U*u*v*math.sin(a)/2+(th-math.sin(th))/2
 areas=[];fg=[]
 for k,e in enumerate(edges):
  f=E[e][0];t=xr[E[e][1]]if len(E[e])==2 else ya[bedges.index(e)];areas.append(U*U*xr[f]*t*math.sin(be[k]))
 for f in range(nf):
  total=0
  for k in fedge[f]:
   e=edges[k];other=[j for j in E[e]if j!=f];t=xr[other[0]]if other else ya[bedges.index(e)];total+=math.atan2(t*math.sin(be[k]),xr[f]-t*math.cos(be[k]))
  fg.append(total-math.pi)
 eq=np.r_[fg,[sum(be[k]for k in inc[v])-2*math.pi for v in hidden],sum(theta)-2*math.pi]
 return wedge+sum(areas)-math.pi,eq,al
v,eq,al=unpack(x0);assert abs(v)<1e-12 and max(abs(eq))<1e-12;print('candidate calibration',v,max(abs(eq)),flush=True)
if __name__=='__main__':
 rng=np.random.default_rng(1702);out=[];bounds=[(1e-5,math.pi-1e-5)]*ne+[(1e-3,1)]*(nf+nb)
 for j in range(5):
  z=x0.copy()if j==0 else x0+rng.normal(0,.005,len(x0));z=np.array([min(b,max(a,v))for v,(a,b)in zip(z,bounds)])
  res=minimize(lambda z:-unpack(z)[0],z,method='SLSQP',bounds=bounds,constraints=[{'type':'eq','fun':lambda z:unpack(z)[1]},{'type':'ineq','fun':lambda z:np.r_[unpack(z)[2],math.pi-unpack(z)[2]]}],options={'maxiter':800,'ftol':1e-11});v,eq,al=unpack(res.x);rec={'start':j,'success':bool(res.success),'message':res.message,'area_excess':float(v),'max_equality_residual':float(max(abs(eq))),'min_alpha_slack':float(min(min(al),min(math.pi-al))),'iterations':int(res.nit),'solution':res.x.tolist()};out.append(rec);print({k:v for k,v in rec.items()if k!='solution'},flush=True)
 (P/'coupled-primal-probe.json').write_text(json.dumps({'status':'numeric_only_shared_radii_full_boundary_interface','runs':out},indent=2))
