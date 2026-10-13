"""Exact outward rational-grid interval verification of candidate stress/M.
Conditional on (a,t,r,w) being in input box, NOT root isolation.
Every primitive rounded outward on 10^-45 grid; no floating arithmetic in kernel.
"""
from fractions import Fraction as F
from pathlib import Path
import json
SCALE=10**45
class I:
 def __init__(self,a,b=None):
  if isinstance(a,I):self.lo,self.hi=a.lo,a.hi;return
  a=F(a);b=a if b is None else F(b)
  assert a<=b
  self.lo=F((a*SCALE).__floor__(),SCALE);self.hi=F((b*SCALE).__ceil__(),SCALE)
 def __add__(x,y):
  y=I(y);return I(x.lo+y.lo,x.hi+y.hi)
 __radd__=__add__
 def __neg__(x):return I(-x.hi,-x.lo)
 def __sub__(x,y):return x+-I(y)
 def __rsub__(x,y):return I(y)+-x
 def __mul__(x,y):
  y=I(y);v=[x.lo*y.lo,x.lo*y.hi,x.hi*y.lo,x.hi*y.hi];return I(min(v),max(v))
 __rmul__=__mul__
 def __truediv__(x,y):
  y=I(y);assert not y.lo<=0<=y.hi
  return x*I(1/y.hi,1/y.lo)
 def __rtruediv__(x,y):return I(y)/x
 def __pow__(x,n):
  assert isinstance(n,int) and n>=0
  y=I(1)
  for _ in range(n):y=y*x
  return y
 def dump(x):return [str(x.lo),str(x.hi)]

def verify(box):
 a,t,r,w=[I(*z) for z in box]
 b=(1+a+r)/2;ss=b*b+w*w/3
 x=-b*r*r/(ss-b);y=(b-1)*ss/(ss-b)
 p=I(1);q=2*(1-b)/r;u=q*r/(2*a-t+r)
 j=u*(2*t-2*r-a)/r;z=j*r*t/(1-t*t-r*r)
 weights={'x':x,'y':y,'z':z,'p':p,'q':q,'u':u,'j':j}
 assert all(v.lo>0 for v in weights.values())
 total=6*x+6*y+6*z+6*p+3*q+6*u+3*j
 edges=[]
 # site 0..8, hubs9..11, witnesses12..17, anchors18..26
 for i in range(9):
  for k in [i,(i+1)%9]:
   typ=k%3
   weight=z if typ==1 else (x if i%3==2 else y)
   edges.append((18+i,k,weight/total))
 faces=[(8,0,9),(2,3,10),(5,6,11),(9,10,1),(10,11,4),(11,9,7)]
 for i,face in enumerate(faces):
  for k in face:
   weight=(q if k>=9 else p) if i<3 else (u if k>=9 else j)
   edges.append((12+i,k,weight/total))
 L=[[I(0) for _ in range(27)] for _ in range(27)]
 for i,k,v in edges:
  L[i][i]+=v;L[k][k]+=v;L[i][k]-=v;L[k][i]-=v
 order=list(range(12,18))+list(range(12))+list(range(18,27))
 # interval Schur elimination, with Dirichlet positive pivots enforced
 pivots=[]
 for ii,k in enumerate(order[:18]):
  pivot=L[k][k];assert pivot.lo>0;pivots.append(pivot.dump())
  remain=order[ii+1:]
  for ix,i in enumerate(remain):
   for jx in range(ix,len(remain)):
    jj=remain[jx]
    val=L[i][jj]-L[i][k]*L[k][jj]/pivot
    L[i][jj]=val;L[jj][i]=val
 U=F('0.361102963744508672616920293904');c=1-2*U*U
 cos=[F(1),c]
 for d in range(2,5):cos.append(2*c*cos[-1]-cos[-2])
 M=[[I(0) for _ in range(9)] for _ in range(9)]
 minq=None
 for i in range(9):
  for jj in range(i+1,9):
   qq=-L[18+i][18+jj];assert qq.lo>=0
   minq=qq.lo if minq is None else min(minq,qq.lo)
   v=2*qq*I(cos[min(jj-i,9-(jj-i))])
   M[i][i]+=v;M[jj][jj]+=v;M[i][jj]-=v;M[jj][i]-=v
 # top-left8 minor; a positive minor plus exact M1=0 proves modulo-rotation positivity
 mp=[]
 for k in range(8):
  pivot=M[k][k];assert pivot.lo>0,('nonpositive LDL pivot',k,pivot.dump());mp.append(pivot.dump())
  for i in range(k+1,8):
   for jj in range(i,8):
    val=M[i][jj]-M[i][k]*M[k][jj]/pivot
    M[i][jj]=val;M[jj][i]=val
 return {'status':'certified conditional matrix inequalities','scope':'entire input box, no root existence asserted','box':box,'weight_bounds':{k:v.dump() for k,v in weights.items()},'normalization':total.dump(),'dirichlet_pivots':pivots,'hessian_minor_pivots':mp,'minimum_schur_conductance_lower':str(minq),'exact_cosine_constants':[str(x) for x in cos]}
if __name__=='__main__':
 root=Path(__file__).resolve().parents[1]
 j=json.loads((root/'evidence/d3-chart-calibration.json').read_text())
 eps=F(1,10**38)
 box=[[str(F(s)-eps),str(F(s)+eps)] for s in j['root']]
 out=verify(box)
 (root/'evidence/stress-interval.json').write_text(json.dumps(out,indent=2))
 print(json.dumps({'status':out['status'],'positive_weights':len(out['weight_bounds']),'positive_free_pivots':len(out['dirichlet_pivots']),'positive_minor_pivots':len(out['hessian_minor_pivots']),'scope':out['scope']}))
