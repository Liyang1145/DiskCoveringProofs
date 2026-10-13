"""Continuous dual certificate using exact bivariate support reduction.
Edge support supremum occurs on a=b, a=0, b=0, a+b=pi.
"""
from mpmath import iv
import json
from pathlib import Path
iv.dps=35;P=Path(__file__).parent;R=iv.mpf(19)/50;R2=R*R
row=next(j for j in json.loads((P/'edge_compatible_dual.json').read_text()) if j['start']==7 and j['span']==3)
z=[iv.mpf(f'{v:.10f}') for v in row['z']];faces=row['faces'];edges=row['edges'];nf=len(faces)
core=[8,0,2,3,4,5,6,7];span=3
expected=[(0,1,2)]+[(9,core[k],core[k+1]) for k in range(span)]+[(10,core[k],core[(k+1)%8]) for k in range(span,8)]+[(9,10,core[0]),(9,10,core[span])]
assert sorted(tuple(sorted(f)) for f in faces)==sorted(tuple(sorted(f)) for f in expected)
assert len(edges)==21 and nf==11
assert sorted(tuple(e) for e in edges)==sorted({tuple(sorted((f[k],f[(k+1)%3]))) for f in expected for k in range(3)})
mu=z[:11];nu=z[11:11+nf];lam,eta=z[-2:];assert lam.a>=0 and eta.a>=0
B=iv.atan2(2*R,iv.sqrt(1-4*R2))
ub=iv.pi*(sum(mu[:9])+2*sum(mu[9:])+sum(nu)-2*lam-2*eta)+2*eta*B
for i,j in edges:
 adj=[(t,next(k for k in f if k not in (i,j))) for t,f in enumerate(faces) if i in f and j in f]
 t,k=adj[0];p=-nu[t]-mu[k]
 if len(adj)==2:t,k=adj[1];q=-nu[t]-mu[k]
 else:q=mu[i]+mu[j]
 c=(p+q)/2
 if c.a>=R2.b:diag=c*iv.pi
 elif c.b<=-R2.a:diag=iv.mpf(0)
 else:
  assert c.a>-R2.a and c.b<R2.a
  co=-c/R2;t=iv.atan2(iv.sqrt(1-co*co),co)
  diag=R2*iv.sin(t)+c*t
 ub+=max(iv.mpf(0).b,(p*iv.pi).b,(q*iv.pi).b,diag.b)
N=65536;h=iv.mpf(22)/(7*N);mx=[iv.mpf('-inf') for _ in range(9)]
for k in range(N+1):
 a=h*k;s=iv.sin(a/2);half=iv.mpf(1)/2
 if s.b<=half.a:s=half
 elif s.a<half.b:s=iv.mpf([half.a,s.b])
 v=R*s;w=2*iv.atan2(v,iv.sqrt(1-v*v));F=R2*iv.sin(a)/2+(w-iv.sin(w))/2
 for i in range(9):
  C=lam+(eta if i>=3 else 0)
  val=F+C*w-mu[i]*a
  mx[i]=max(mx[i],val.b)
for i in range(9):ub+=mx[i]+(1+lam+(eta if i>=3 else 0)+abs(mu[i]))*h
assert ub.b<iv.pi.a,ub
result={'start':7,'span':3,'upper':str(ub),'pi':str(iv.pi),'N':N,'strict':True,'coefficients':[str(v) for v in z]}
(P/'compatible_position_certificate.json').write_text(json.dumps(result,indent=2));print(result,flush=True)
