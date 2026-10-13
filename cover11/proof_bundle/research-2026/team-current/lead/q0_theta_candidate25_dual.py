"""Finite side-grid theta face coupling. Numeric proposer, NOT continuum certificate."""
import numpy as np,math,json,itertools,time
from pathlib import Path
from scipy.optimize import linprog
P=Path(__file__).parent
src=(P/'q0_closure_dual.py').read_text(encoding='utf-8-sig').split('\n K=len(factors)')[0]
src=src.replace('for row in J:',"for row in [r for r in J if r['start']==0 and r['span']==4]:")
exec(src)
m=25;grid=np.linspace(0,1,m);trip=[];angles=[]
for inds in itertools.product(range(m),repeat=3):
 sides=grid[list(inds)];x,y,z=sides;p=(x+y+z)/2;dd=p*(p-x)*(p-y)*(p-z)
 if min(sides)>0 and dd>1e-16:
  D=math.sqrt(dd)
  if x*y*z>2*D+1e-12:continue
  aa0=np.arccos(np.clip([(y*y+z*z-x*x)/(2*y*z),(z*z+x*x-y*y)/(2*z*x),(x*x+y*y-z*z)/(2*x*y)],-1,1))
  trip.append(inds);angles.append(aa0)
 elif np.count_nonzero(sides)==2:
  k=int(np.argmin(sides));j=(k+1)%3;l=(k+2)%3
  if sides[j]!=sides[l]:continue
  for a0 in np.linspace(math.asin(sides[j]),math.pi-math.asin(sides[j]),19):
   aa0=np.zeros(3);aa0[j]=a0;aa0[l]=math.pi-a0;trip.append(inds);angles.append(aa0)
 elif max(sides)==0:
  for a0 in aa:trip.append(inds);angles.append(a0)
trip=np.array(trip);angles=np.array(angles);ts=grid[trip];sp=ts.sum(axis=1)/2
areas=4*R*R*np.sqrt(np.maximum(0,sp*np.prod(sp[:,None]-ts,axis=1)))
# Local coordinate ordering: ordinary face incoming spoke,outgoing spoke,ring;
# terminal face A spoke,B spoke,AB. Opposite angle derived from exact graph edges.
localedges=[]
for i in range(9):
 h=9 if i<4 else 10;localedges.append([tuple(sorted((h,i))),tuple(sorted((h,(i+1)%9))),tuple(sorted((i,(i+1)%9)))])
localedges += [[(0,9),(0,10),(9,10)],[(4,9),(4,10),(9,10)]]
assert len(faces)==11
rowsF=[]
internal=[ei for ei,e in enumerate(edges) if len(adj[e])==2]
fixed=[side+ei for ei in internal]+[lin+ei for ei in internal]
for fi,f in enumerate(faces):
 E=localedges[fi];assert {tuple(sorted((f[j],f[(j+1)%3]))) for j in range(3)}==set(E)
 M=np.zeros((len(trip),nz))
 for k,e in enumerate(E):
  vertex=next(v for v in f if v not in e);ei=edges.index(e);sgn=1 if adj[e][0][0]==fi else -1
  M[:,vertex]-=angles[:,k];M[:,kap+ei]-=angles[:,k]
  M[:,side+ei]+=sgn*ts[:,k]**2;M[:,lin+ei]+=sgn*ts[:,k]
 rowsF.append(M)
# calibrated Heron/angle representation against actual saved candidate geometry, not sampled witness membership
raw=json.loads(Path('n11/upper/certified_object.json').read_text(encoding='utf-8-sig'));c=np.array(raw['centers_scaled_1e17'],dtype=float)/1e17
ring=sorted([i for i in range(11) if i not in [0,2]],key=lambda i:math.atan2(c[i,1],c[i,0]));c=c[ring+[0,2]]
# Actual graph labeling can differ by cyclic shift; geometric face formula calibrated on all Delaunay triangles instead.
from scipy.spatial import Delaunay
maxerr=0.
for ff in Delaunay(c).simplices:
 pp=c[ff];ss=np.array([np.linalg.norm(pp[(i+1)%3]-pp[(i+2)%3])/(2*R) for i in range(3)]);p=ss.sum()/2;her=4*R*R*math.sqrt(max(0,p*np.prod(p-ss)));cross=abs(np.linalg.det(np.stack([pp[1]-pp[0],pp[2]-pp[0]])))/2;maxerr=max(maxerr,abs(her-cross))
assert maxerr<1e-14
flatidx=np.ravel_multi_index(trip.T,(m,m,m));sort=np.argsort(flatidx,kind='stable');idxsort=flatidx[sort];starts=np.r_[0,np.flatnonzero(np.diff(idxsort))+1];keys=idxsort[starts]
def tensor(fi,z):
 v=areas+rowsF[fi]@z;T=np.full(m**3,-np.inf);I=np.full(m**3,-1,dtype=int)
 # Degenerate repeated tuples have varying legal limiting angles; maximize all.
 order=sort[np.argsort(v[sort],kind='stable')];T[flatidx[order]]=v[order];I[flatidx[order]]=order
 return T.reshape(m,m,m),I.reshape(m,m,m)
def path_transfer(mats):
 dp=np.full((m,m),-np.inf);np.fill_diagonal(dp,0);backs=[]
 for w in mats:
  v=dp[:,:,None]+w[None,:,:];backs.append(np.argmax(v,axis=1));dp=np.max(v,axis=1)
 return dp,backs
def path_recover(backs,start,end):
 out=[end]
 for bk in backs[::-1]:end=int(bk[start,end]);out.append(end)
 assert end==start
 return out[::-1]
def cycle(mats):
 dp,bk=path_transfer(mats);start=int(np.argmax(np.diag(dp)));return dp[start,start],path_recover(bk,start,start)
# Cycle contraction independent brute control (same grid dims but sparse random reduced3-state domain).
rng=np.random.default_rng(835);ww=[np.full((m,m),-np.inf) for _ in range(4)]
for w in ww:w[:3,:3]=rng.normal(size=(3,3))
cv,cp=cycle(ww);bv=max(sum(ww[i][p[i],p[(i+1)%4]] for i in range(4)) for p in itertools.product(range(3),repeat=4));assert abs(cv-bv)<1e-12

def separate(z):
 tensors=[tensor(i,z) for i in range(11)];W=[np.max(T,axis=2) for T,I in tensors[:9]];arg=[np.argmax(T,axis=2) for T,I in tensors[:9]]
 A,ba=path_transfer(W[:4]);B,bb=path_transfer(W[4:]);best=-np.inf
 for h in range(m):
  val,cp=cycle([tensors[9][0][:,:,h],B.T,tensors[10][0][:,:,h].T,A.T])
  if val>best:best=val;bestcp=cp;besth=h
 a0,b0,b4,a4,_=bestcp;h=besth
 pa=path_recover(ba,a0,a4);pb=path_recover(bb,b4,b0);inds=[]
 for i,(u,v) in enumerate(zip(pa[:-1]+pb[:-1],pa[1:]+pb[1:])):inds.append(int(tensors[i][1][u,v,arg[i][u,v]]))
 inds += [int(tensors[9][1][a0,b0,h]),int(tensors[10][1][a4,b4,h])]
 assert min(inds)>=0
 V=sum(areas[i] for i in inds);M=sum(rowsF[f][i] for f,i in enumerate(inds));assert np.max(np.abs(M[fixed]))<1e-12
 assert abs(V+M@z-best)<1e-9
 vals=[best];cuts=[(V,M)]
 for v,M in factors[11:]:
  q=v+M@z;i=int(np.argmax(q));vals.append(q[i]);cuts.append((v[i],M[i]))
 return vals,cuts,inds
# Insert genuine saved candidate as mandatory feasible control in all factor maximizations.
ns={'__file__':str(P/'q0_exact_closure_radius.py')};exec((P/'q0_exact_closure_radius.py').read_text().split('res=ceq(x0)')[0],ns)
xx=ns['x0'];ang0=xx[:33].reshape(11,3);bs=xx[33:42];ys=np.exp(xx[42:62]+xx[-1])/R;als,ws,cls,area0=ns['calc'](xx)
VC=0.;MC=np.zeros(nz)
for fi,f in enumerate(faces):
 VC+=2*R*R*ys[fi]**2*np.prod(np.sin(ang0[fi]))
 for k,i in enumerate(f):
  e=tuple(sorted(j for j in f if j!=i));ei=edges.index(e);sgn=1 if adj[e][0][0]==fi else -1;a=ang0[fi,k]
  MC[i]-=a;MC[kap+ei]-=a;MC[side+ei]+=sgn*(ys[fi]*np.sin(a))**2;MC[lin+ei]+=sgn*ys[fi]*np.sin(a)
assert np.max(np.abs(MC[fixed]))<1e-13
for i in range(9):
 j=(i+1)%9;ei=edges.index(tuple(sorted((i,j))));b=bs[i];y=ys[11+i];M=np.zeros(nz);v0=R*R*y*y*np.sin(2*b)/2
 M[i]+=b;M[j]+=b;M[kap+ei]-=b;M[cl+i]+=2*b;M[side+ei]-=(y*np.sin(b))**2;M[lin+ei]-=y*np.sin(b)
 for k in [2*i+1,2*j]:M[rr+k]+=y*y;M[lin+21+k]+=y
 v,MM=factors[11+i];factors[11+i]=(np.r_[v,v0],np.vstack([MM,M]))
 a=als[i];u=ys[11+(i-1)%9];v=ys[11+i];w=ws[i];L=math.atan2(v*math.sin(a),u-v*math.cos(a));T=pi-a-L;M=np.zeros(nz)
 v0=R*R*u*v*np.sin(a)/2+(w-np.sin(w))/2;M[i]-=a;M[lam]+=w;M[rr+2*i]-=u*u;M[rr+2*i+1]-=v*v;M[lin+21+2*i]-=u;M[lin+21+2*i+1]-=v
 M[cl+(i-1)%9]+=L+w/2;M[cl+i]+=T+w/2
 vv,MM=factors[20+i];factors[20+i]=(np.r_[vv,v0],np.vstack([MM,M]))
old_separate=separate
def separate(z):
 vals,cuts,inds=old_separate(z)
 if VC+MC@z>vals[0]:vals[0]=VC+MC@z;cuts[0]=(VC,MC)
 return vals,cuts,inds

K=19;arows=[];rhs=[]
def add(cuts):
 for fi,(v,M) in enumerate(cuts):
  a=np.zeros(nz+K);a[:nz]=M;a[nz+fi]=-1;arows.append(a);rhs.append(-v)
bounds=[(-3,3)]*kap+[(0,3)]*(ne+2)+[(-3,3)]*48+[(None,None)]*K;bounds[eta]=(0,0)
for k in fixed:bounds[k]=(0,0)
z0=np.array(json.loads((P/'q0_closure_dual_0_4.json').read_text())['z']);z0[fixed]=0
vals,cuts,inds=separate(z0);add(cuts);best=float(const@z0+sum(vals));bestz=z0.copy();t0=time.time()
print('THETA_CALIBRATED',best,'localrows',len(trip),'HeronError',maxerr,flush=True)
for it in range(500):
 sol=linprog(np.r_[const,np.ones(K)],A_ub=np.array(arows),b_ub=np.array(rhs),bounds=bounds,method='highs');assert sol.success,sol.message
 z=sol.x[:nz];vals,cuts,inds=separate(z);ub=float(const@z+sum(vals));add(cuts)
 if ub<best:best=ub;bestz=z.copy()
 if it%20==0:print('THETA',it,sol.fun,best,'seconds',time.time()-t0,flush=True)
 if ub-sol.fun<2e-6:break
out={'R':R,'sample_upper':best,'lp_lower':float(sol.fun),'iterations':it+1,'side_nodes':m,'localrows':len(trip),'z':bestz.tolist(),'scope':'finite side-grid theta graph only; not continuum certificate','Heron_error':maxerr}
(P/'q0_theta_candidate25_dual_0_4.json').write_text(json.dumps(out,indent=2));print('RESULT',best,flush=True)
