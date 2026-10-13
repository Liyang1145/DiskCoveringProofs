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
 if span!=3:continue
 if start!=int(sys.argv[1]):continue
 bins=int(sys.argv[2]);binid=int(sys.argv[3]);bin0=int(sys.argv[4])
 faces=row['faces'];edges=row['edges'];nf=len(faces);nz=11+nf+2;lam=nz-2;eta=nz-1;K=len(edges)+9
 const=np.r_[np.ones(9)*pi,[2*pi]*2,np.ones(nf)*pi,-2*pi,-2*pi+2*math.asin(2*R)]
 aa=[];bb=[]
 for i in range(N+1):
  for k in range(N+1-i):aa.append(i*pi/N);bb.append(k*pi/N)
 a=np.array(aa);b=np.array(bb);sa=np.sin(a);sb=np.sin(b)
 G=R*R*np.maximum(0,np.sin(a+b))*np.minimum(sa,sb)/np.maximum(1e-15,np.maximum(sa,sb))
 al=np.linspace(0,pi,1201);w=2*np.arcsin(R*np.maximum(.5,np.sin(al/2)));F=R*R*np.sin(al)/2+(w-np.sin(w))/2
 factors=[]
 for i,j in edges:
  adj=[(t,next(k for k in f if k not in (i,j))) for t,f in enumerate(faces) if i in f and j in f]
  ca=np.zeros(nz);cb=np.zeros(nz);t,k=adj[0];ca[11+t]=-1;ca[k]=-1
  if len(adj)==2:
   t,k=adj[1];cb[11+t]=-1;cb[k]=-1
  else:cb[i]=1;cb[j]=1
  mask=np.ones(len(a),dtype=bool)
  if adj[0][0]==0:
   vertex=adj[0][1]
   intervals=[(bin0/bins,(bin0+1)/bins),(binid/bins,(binid+1)/bins),(max(0,1-(bin0+binid+2)/bins),max(0,1-(bin0+binid)/bins))]
   lo,hi=intervals[vertex];mask=(a>=lo*pi-1e-12)&(a<=hi*pi+1e-12)
  factors.append((G[mask],a[mask],b[mask],ca,cb))
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
 out.append({'start':start,'span':span,'grid_dual':float(best),'lp_lower':float(sol.fun),'z':bestz.tolist(),'faces':faces,'edges':edges,'N':N,'bins':bins,'binid':binid,'bin0':bin0,'iterations':it+1})
 (P/f'edge_earbox_{start}_{bins}_{binid}_{bin0}.json').write_text(json.dumps(out,indent=2))
 print('RESULT',start,span,round(best,9),flush=True)
