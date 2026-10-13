"""Finite-sample factor dual, diagnostic only: exact shared squared radii and side lengths.
Face and boundary radius maximizations linear (endpoints suffice). Ring radius grids are NOT global certificates.
"""
import numpy as np,json,math,sys
from pathlib import Path
from scipy.optimize import linprog
P=Path(__file__).parent;R=.38;pi=math.pi;N=90;NR=24;NA=180
J=json.loads((P/'area_edge_compatible.json').read_text());out=[]
for row in J:
 start,span=row['start'],row['span']
 if span!=4:continue
 if len(sys.argv)>1 and (start!=int(sys.argv[1]) or span!=int(sys.argv[2])):continue
 faces=row['faces'];edges=[tuple(e) for e in row['edges']];ne=len(edges);nf=len(faces)
 # multipliers: mu11, side21, endpoint18, nonnegative angle slack21, lambda,eta
 side=11;rr=side+ne;kap=rr+18;lam=kap+ne;eta=lam+1;lin=eta+1;nz=lin+39
 const=np.zeros(nz);const[:9]=pi;const[9:11]=2*pi;const[kap:lam]=pi;const[lam]=-2*pi;const[eta]=-2*pi+2*math.asin(2*R)
 factors=[];adj={e:[(t,next(k for k in f if k not in e)) for t,f in enumerate(faces) if e[0] in f and e[1] in f] for e in edges}
 aa=np.array([(i*pi/N,j*pi/N,(N-i-j)*pi/N) for i in range(N+1) for j in range(N+1-i)])
 for t,f in enumerate(faces):
  xx=np.linspace(0,1,31)**2;ang=np.tile(aa,(len(xx),1));x=np.repeat(xx,len(aa));v=2*R*R*x*np.prod(np.sin(ang),axis=1);M=np.zeros((len(v),nz))
  for k,i in enumerate(f):
   e=tuple(sorted(j for j in f if j!=i));ee=edges.index(e);sgn=1 if adj[e][0][0]==t else -1
   M[:,i]-=ang[:,k];M[:,kap+ee]-=ang[:,k];M[:,side+ee]+=sgn*x*np.sin(ang[:,k])**2;M[:,lin+ee]+=sgn*np.sqrt(x)*np.sin(ang[:,k])
  factors.append((v,M))
 for bi in range(9):
  i,j=bi,(bi+1)%9;e=tuple(sorted((i,j)));ee=edges.index(e);assert len(adj[e])==1
  b=np.tile(np.linspace(0,pi/2,4*N+1),31);x=np.repeat(np.linspace(0,1,31)**2,4*N+1);v=R*R*x*np.sin(2*b)/2;M=np.zeros((len(v),nz))
  M[:,i]+=b;M[:,j]+=b;M[:,kap+ee]-=b;M[:,side+ee]-=x*np.sin(b)**2;M[:,lin+ee]-=np.sqrt(x)*np.sin(b)
  # positive matching multiplier for switch, negative for copies in sectors
  M[:,rr+2*i+1]+=x;M[:,rr+2*j]+=x;M[:,lin+21+2*i+1]+=np.sqrt(x);M[:,lin+21+2*j]+=np.sqrt(x)
  factors.append((v,M))
 grid=np.array([(a,u,v) for a in np.linspace(0,pi,NA+1) for u in np.linspace(0,1,NR+1) for v in np.linspace(0,1,NR+1)])
 a,u,v=grid.T;ch=R*np.sqrt(np.maximum(0,u*u+v*v-2*u*v*np.cos(a)));w=2*np.arcsin(ch/2);S=R*R*u*v*np.sin(a)/2+(w-np.sin(w))/2
 for i in range(9):
  M=np.zeros((len(a),nz));M[:,i]=-a;M[:,rr+2*i]=-u*u;M[:,rr+2*i+1]=-v*v;M[:,lam]=w;M[:,lin+21+2*i]=-u;M[:,lin+21+2*i+1]=-v
  if i>=3:M[:,eta]=w
  factors.append((S,M))
 K=len(factors);rows=[];rhs=[];used=[set() for _ in factors]
 def add(fi,idx):
  if idx in used[fi]:return
  used[fi].add(idx);v,M=factors[fi];ar=np.zeros(nz+K);ar[:nz]=M[idx];ar[nz+fi]=-1;rows.append(ar);rhs.append(-v[idx])
 for fi,(v,M) in enumerate(factors):add(fi,int(np.argmax(v)))
 bounds=[(-3,3)]*kap+[(0,3)]*(ne+2)+[(-3,3)]*39+[(None,None)]*K;c=np.r_[const,np.ones(K)];best=1e9;bestz=None
 for it in range(500):
  sol=linprog(c,A_ub=np.array(rows),b_ub=np.array(rhs),bounds=bounds,method='highs');assert sol.success
  z=sol.x[:nz];mx=[]
  for fi,(v,M) in enumerate(factors):
   vals=v+M@z;idx=int(np.argmax(vals));mx.append(vals[idx]);add(fi,idx)
  ub=const@z+sum(mx)
  if ub<best:best=ub;bestz=z.copy()
  if it%25==0:print(start,span,it,round(sol.fun,8),round(best,8),flush=True)
  if ub-sol.fun<5e-7:break
 res={'start':start,'span':span,'sample_upper':best,'lp_value':sol.fun,'N':N,'NR':NR,'NA':NA,'z':bestz.tolist(),'iterations':it+1,'faces':faces,'edges':edges}
 out.append(res);(P/f'shared_moment_dense_{start}_{span}.json').write_text(json.dumps(res,indent=2));print('RESULT',start,span,round(best,10),flush=True)
