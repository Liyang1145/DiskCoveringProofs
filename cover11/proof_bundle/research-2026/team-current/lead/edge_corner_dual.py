"""Numeric cutting-plane dual for bivariate compatible edge bound; finite grids NOT certificate.
One representative test first. Optimizer merely proposes multipliers for later global sup certification.
"""
import numpy as np,math,json,sys
from pathlib import Path
from scipy.optimize import linprog
P=Path(__file__).parent;R=.38;pi=math.pi;N=160
J=json.loads((P/'area_face_angles.json').read_text());out=[]
for row in J:
 start,span=row['start'],row['span']
 if span==2:continue
 if len(sys.argv)>1 and start!=int(sys.argv[1]):continue
 faces=row['faces'];edges=row['edges'];nf=len(faces);nz=11+nf+2;lam=nz-2;eta=nz-1;K=len(edges)+9
 const=np.r_[np.ones(9)*pi,[2*pi]*2,np.ones(nf)*pi,-2*pi,-2*pi+2*math.asin(2*R)]
 aa=[];bb=[]
 for i in range(N+1):
  for k in range(N+1-i):aa.append(i*pi/N);bb.append(k*pi/N)
 a=np.array(aa);b=np.array(bb);sa=np.sin(a);sb=np.sin(b)
 G=R*R*np.maximum(0,np.sin(a+b))*np.minimum(sa,sb)/np.maximum(1e-15,np.maximum(sa,sb))
 al=np.linspace(0,pi,1201);w=2*np.arcsin(R*np.sin(al/2));F=R*R*np.sin(al)/2+(w-np.sin(w))/2
 w0=2*math.asin(R/2);al=np.r_[al,0,pi];w=np.r_[w,w0,w0];F=np.r_[F,(w0-math.sin(w0))/2,(w0-math.sin(w0))/2]
 factors=[]
 for i,j in edges:
  adj=[(t,next(k for k in f if k not in (i,j))) for t,f in enumerate(faces) if i in f and j in f]
  ca=np.zeros(nz);cb=np.zeros(nz);t,k=adj[0];ca[11+t]=-1;ca[k]=-1
  if len(adj)==2:
   t,k=adj[1];cb[11+t]=-1;cb[k]=-1
  else:cb[i]=1;cb[j]=1
  factors.append((G,a,b,ca,cb))
 for i in range(9):
  ca=np.zeros(nz);cb=np.zeros(nz);ca[i]=-1;cb[lam]=1
  if i>=3:cb[eta]=1
  factors.append((F,al,w,ca,cb))
 rows=[];rhs=[];used=[set() for _ in factors]
 def add(fi,idx):
  if idx in used[fi]:return
  used[fi].add(idx);f,x,y,c,d=factors[fi];ar=np.zeros(nz+K);ar[:nz]=x[idx]*c+y[idx]*d;ar[nz+fi]=-1
  rows.append(ar);rhs.append(-f[idx])
 for fi in range(K):add(fi,int(np.argmax(factors[fi][0])))
 c=np.r_[const,np.ones(K)];bound=[(-3,3)]*(nz-2)+[(0,3)]*2+[(None,None)]*K
 best=1e9;bestz=None
 for it in range(240):
  sol=linprog(c,A_ub=np.array(rows),b_ub=np.array(rhs),bounds=bound,method='highs');assert sol.success
  z=sol.x[:nz];mx=[]
  for fi,(f,x,y,ca,cb) in enumerate(factors):
   vals=f+x*np.dot(ca,z)+y*np.dot(cb,z);idx=int(np.argmax(vals));mx.append(vals[idx]);add(fi,idx)
  upper=const@z+sum(mx)
  if upper<best:best=upper;bestz=z.copy()
  if it%30==0:print('iter',start,span,it,round(sol.fun,7),round(best,7),flush=True)
  if upper-sol.fun<2e-7:break
 out.append({'start':start,'span':span,'grid_dual':float(best),'lp_lower':float(sol.fun),'z':bestz.tolist(),'faces':faces,'edges':edges,'N':N,'iterations':it+1})
 (P/('edge_corner_dual'+('args'+sys.argv[1] if len(sys.argv)>1 else '')+'.json')).write_text(json.dumps(out,indent=2))
 print('RESULT',start,span,round(best,9),flush=True)
