"""Bounded geometric control: guaranteed-cover perturbations, innerroot, outwardclip. Numeric, no sampling certificate."""
from boundary_radius_control import *
def cross(a,b):return a[0]*b[1]-a[1]*b[0]
def angle(a,b):return math.atan2(abs(cross(a,b)),float(a@b))
def check(C,r):
 norms=np.linalg.norm(C,axis=1);s=math.sqrt(1-r*r);N=C.copy()
 for i,t in enumerate(norms):
  if t>s:N[i]*=(1-r*r)/(t*t)
 eps=1e-6;N/=1+eps;rho=(r+eps)/(1+eps);s=math.sqrt(1-rho*rho);assert max(np.linalg.norm(N,axis=1))<s
 ans=[]
 for i,j in combinations(range(14),2):
  d=N[j]-N[i];l=np.linalg.norm(d);h=(N[j]@N[j]-N[i]@N[i])/(2*l)
  if abs(h)>=1:continue
  e=d/l;n=np.array([-e[1],e[0]])
  for sign in [-1,1]:
   A=h*e+sign*math.sqrt(1-h*h)*n;ds=np.sum((N-A)**2,axis=1)
   if ds[i]>min(ds)+1e-10:continue
   t=math.atan2(A[1],A[0])%(2*math.pi);ans.append((t,A,(i,j)))
 ans.sort(key=lambda z:z[0]);q=len(ans);worst=0.;mininner=10.;maxgap=0.
 for k,(t,A,ij)in enumerate(ans):
  tm,B,_=ans[k-1];tp,D,_=ans[(k+1)%q];thm=(t-tm)%(2*math.pi);thp=(tp-t)%(2*math.pi);pm=np.array([math.cos(t-thm/2),math.sin(t-thm/2)]);pp=np.array([math.cos(t+thp/2),math.sin(t+thp/2)]);u=int(np.argmin(np.sum((N-pm)**2,axis=1)));v=int(np.argmin(np.sum((N-pp)**2,axis=1)));assert set((u,v))==set(ij)
  middle=angle(N[u]-A,N[v]-A);res=angle(B-A,N[u]-A)+middle+angle(N[v]-A,D-A)+(thm+thp)/2-math.pi;worst=max(worst,abs(res));mininner=min(mininner,math.cos(thm/2)-N[u]@pm,math.cos(thp/2)-N[v]@pp);maxgap=max(maxgap,thm,thp)
 assert worst<1e-10 and mininner>0 and maxgap<2*math.asin(rho)+1e-10
 return {'q':q,'radius':rho,'max_residual':worst,'min_chord_inner_margin':mininner,'max_owned_arc':maxgap,'max_site_norm':float(max(np.linalg.norm(N,axis=1)))}
if __name__=='__main__':
 rng=np.random.default_rng(9027);out=[]
 for scale in[1e-6,1e-5,1e-4,5e-4]:
  for rep in range(5):
   delta=rng.normal(0,scale,C.shape);r=U+max(np.linalg.norm(delta,axis=1))+1e-12;assert r<1/3;row=check(C+delta,r);row.update(scale=scale,rep=rep);out.append(row)
 (P/'normalized-boundary-control.json').write_text(json.dumps({'status':'numeric_control_guaranteed_radius_by_triangle_inequality_then_innerroot','runs':out},indent=2));print('runs',len(out),'maxresidual',max(x['max_residual']for x in out),'mininner',min(x['min_chord_inner_margin']for x in out),flush=True)
