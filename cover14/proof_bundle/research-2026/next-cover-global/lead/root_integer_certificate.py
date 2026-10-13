"""Independent rigorous fixed-dyadic interval/2nd-order AD Krawczyk for original F,G,H.
Integer directed rounding only. No member ivkernel reused; mpmath proposes Y only.
"""
from fractions import Fraction as Q
from math import isqrt
from pathlib import Path
import json,mpmath as mp
P=Path(__file__).resolve().parent
BITS=240;S=1<<BITS
def ceildiv(a,b):return -((-a)//b)
class I:
 def __init__(self,x=0,hi=None,raw=False):
  if raw:self.lo=x;self.hi=hi;return
  x=Q(x);self.lo=(x.numerator*S)//x.denominator;self.hi=ceildiv(x.numerator*S,x.denominator)
 def __add__(a,b):
  b=iv(b);return I(a.lo+b.lo,a.hi+b.hi,True)
 __radd__=__add__
 def __neg__(a):return I(-a.hi,-a.lo,True)
 def __sub__(a,b):return a+-iv(b)
 def __rsub__(a,b):return iv(b)+-a
 def __mul__(a,b):
  b=iv(b);v=[x*y for x in(a.lo,a.hi)for y in(b.lo,b.hi)];return I(min(v)//S,ceildiv(max(v),S),True)
 __rmul__=__mul__
 def inv(a):
  assert a.lo*a.hi>0,'zero denominator'
  return I((S*S)//a.hi,ceildiv(S*S,a.lo),True)
 def __truediv__(a,b):return a*iv(b).inv()
 def __rtruediv__(a,b):return iv(b)*a.inv()
 def sqrt(a):
  assert a.lo>0,'radicand not positive'
  low=isqrt(a.lo*S);high=isqrt(a.hi*S);high+=int(high*high<a.hi*S)
  return I(low,high,True)
 def __pow__(a,n):
  assert n>=0
  z=I(1)
  for _ in range(n):z=z*a
  return z
 def absmax(a):return max(abs(a.lo),abs(a.hi))
 def dec(a):return [str(Q(a.lo,S)),str(Q(a.hi,S))]
def iv(x):return x if isinstance(x,I)else I(x)
class J:
 def __init__(self,v,g=None,h=None):
  self.v=iv(v);self.g=g if g is not None else[I(0)for _ in range(3)];self.h=h if h is not None else[[I(0)for _ in range(3)]for _ in range(3)]
 @staticmethod
 def var(v,k):
  t=J(v);t.g[k]=I(1);return t
 def __add__(a,b):
  b=jet(b);return J(a.v+b.v,[a.g[i]+b.g[i]for i in range(3)],[[a.h[i][j]+b.h[i][j]for j in range(3)]for i in range(3)])
 __radd__=__add__
 def __neg__(a):return J(-a.v,[-x for x in a.g],[[-x for x in row]for row in a.h])
 def __sub__(a,b):return a+-jet(b)
 def __rsub__(a,b):return jet(b)+-a
 def __mul__(a,b):
  b=jet(b);return J(a.v*b.v,[a.g[i]*b.v+a.v*b.g[i]for i in range(3)],[[a.h[i][j]*b.v+a.g[i]*b.g[j]+a.g[j]*b.g[i]+a.v*b.h[i][j]for j in range(3)]for i in range(3)])
 __rmul__=__mul__
 def unary(a,v,d,dd):return J(v,[d*x for x in a.g],[[d*a.h[i][j]+dd*a.g[i]*a.g[j]for j in range(3)]for i in range(3)])
 def inv(a):
  v=a.v.inv();return a.unary(v,-v*v,2*v*v*v)
 def __truediv__(a,b):return a*jet(b).inv()
 def __rtruediv__(a,b):return jet(b)*a.inv()
 def sqrt(a):
  v=a.v.sqrt();return a.unary(v,1/(2*v),-1/(4*v*v*v))
 def __pow__(a,n):
  v=J(1)
  for _ in range(n):v=v*a
  return v

def jet(x):return x if isinstance(x,J)else J(x)
def expr(z,c,r):
 s=(1-r*r).sqrt();a=(s+z)/2;t=r+(r*r-z*z).sqrt();b=r+(r*r-(a-z)**2).sqrt();d=1-(r*r-c*c).sqrt()
 v1=(1+a*a+b*b-r*r)/2;v2=(1+c*c+d*d-r*r)/2;det=a*d-b*c
 F=(v1*d-v2*b)**2+(a*v2-c*v1)**2-det*det
 cross=(c-a)*(t-b)+(d-b)*a
 G=((a-c)**2+(b-d)**2)*(c*c+(d-t)**2)*(a*a+(b-t)**2)-4*r*r*cross*cross
 return F,G

def system(xs):
 F,G=expr(*(J.var(x,i)for i,x in enumerate(xs)))
 H=F.g[0]*G.g[1]-F.g[1]*G.g[0]
 dH=[F.h[0][k]*G.g[1]+F.g[0]*G.h[1][k]-F.h[1][k]*G.g[0]-F.g[1]*G.h[0][k]for k in range(3)]
 return [F.v,G.v,H],[F.g,G.g,dH]
def calibrate():
 # Exact polynomial and algebraic derivative controls, including mixed Hessian.
 x=J.var(I(2),0);y=J.var(I(3),1);z=J.var(I(4),2)
 f=x*x*y+1/z
 for val,target in [(f.v,Q(49,4)),(f.g[0],12),(f.g[1],4),(f.g[2],Q(-1,16)),(f.h[0][1],4),(f.h[2][2],Q(1,32))]:
  t=Q(target)*S;assert val.lo<=t<=val.hi
 f=(x*x+y*y+z*z).sqrt()
 assert f.v.lo*f.v.lo<=29*S*S<=f.v.hi*f.v.hi
 # Exact interval containment of arithmetic on endpoints (not a proof of kernel generality).
 A=I(-2*S,3*S,True);B=I(4*S,7*S,True)
 assert (A*B).lo==-14*S and(A*B).hi==21*S
 assert I(2).sqrt().lo**2<=2*S*S<=I(2).sqrt().hi**2
 return True
if __name__=='__main__':
 calibrate();mp.mp.dps=90
 roots=json.loads((P/'root-scout.json').read_text())['z_c_r']
 # decimal rational center and exact halfwidth; outer dyadic enclosure is reported explicitly.
 center=[Q(x)for x in roots];delta=Q(1,10**20)
 X=[I(I(x-delta).lo,I(x+delta).hi,True)for x in center];m=[I(x)for x in center]
 fm,Jm=system(m);_,M=system(X)
 pm=mp.matrix([[mp.mpf(q.lo+q.hi)/(2*S)for q in row]for row in Jm]);inv=pm**-1
 Y=[[I(Q(mp.nstr(inv[i,j],75)))for j in range(3)]for i in range(3)]
 # To keep Y a SINGLE exact matrix rather than interval family, select its lower dyadic endpoint.
 Y=[[I(y.lo,y.lo,True)for y in row]for row in Y]
 R=[[I(int(i==j))-sum((Y[i][k]*M[k][j]for k in range(3)),I(0))for j in range(3)]for i in range(3)]
 rho=max(sum(q.absmax()for q in row)for row in R)
 K=[m[i]-sum((Y[i][j]*fm[j]for j in range(3)),I(0))+sum((R[i][j]*(X[j]-m[j])for j in range(3)),I(0))for i in range(3)]
 margins=[min(K[i].lo-X[i].lo,X[i].hi-K[i].hi)for i in range(3)]
 assert rho<S and min(margins)>0
 out={'status':'certified_local_root','scope':'original lead F,G,H, positive radical branches; unique zero in dyadic box, NOT global optimum or coverage','bits':BITS,'center_decimal_rationals':list(map(str,center)),'halfwidth_rational':str(delta),'box_dyadic': [v.dec()for v in X],'Krawczyk_dyadic':[v.dec()for v in K],'rho_exact_upper':str(Q(rho,S)),'margins_exact_lower':[str(Q(x,S))for x in margins],'preconditioner_exact':[[str(Q(y.lo,S))for y in row]for row in Y],'kernel_controls_pass':True,'det_point_numeric':mp.nstr(mp.det(pm),50)}
 (P/'root-integer-certificate.json').write_text(json.dumps(out,indent=2))
 print('unique root certified within halfwidth 1e-20 dyadic box; rho=',float(Q(rho,S)),'minmargin',float(Q(min(margins),S)),'det proposal',out['det_point_numeric'])
