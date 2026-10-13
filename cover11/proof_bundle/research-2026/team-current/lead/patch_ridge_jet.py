"""First-order interval AD of smooth joint objective, physicalcoordinates(r,b1,b2,delta,w1,w3,H).
No physicalclip in analytic extension; refuses branch/sqrt singularity.
"""
import interval_joint_patch as k
from interval_joint_patch import I,iv,R,z,pi,lf,uf
class Unsafe(Exception):pass
class Jet:
 def __init__(self,v,d=None):self.v=v if hasattr(v,'_mpi_') else I(v);self.d=d if d is not None else [I(0)for _ in range(7)]
 def __add__(a,b):
  b=jet(b);return Jet(a.v+b.v,[x+y for x,y in zip(a.d,b.d)])
 __radd__=__add__
 def __neg__(a):return Jet(-a.v,[-x for x in a.d])
 def __sub__(a,b):return a+-jet(b)
 def __rsub__(a,b):return jet(b)+-a
 def __mul__(a,b):
  b=jet(b);return Jet(a.v*b.v,[x*b.v+a.v*y for x,y in zip(a.d,b.d)])
 __rmul__=__mul__
 def __truediv__(a,b):
  b=jet(b)
  if b.v.a<=0<=b.v.b:raise Unsafe('division throughzero')
  return Jet(a.v/b.v,[(x*b.v-a.v*y)/(b.v*b.v)for x,y in zip(a.d,b.d)])
 def __rtruediv__(a,b):return jet(b)/a
 def __pow__(a,n):
  if n==2:return Jet(a.v**2,[2*a.v*x for x in a.d])
  raise ValueError(n)
def jet(a):return a if isinstance(a,Jet)else Jet(a)
def sin(a):
 a=jet(a);return Jet(iv.sin(a.v),[iv.cos(a.v)*x for x in a.d])
def cos(a):
 a=jet(a);return Jet(iv.cos(a.v),[-iv.sin(a.v)*x for x in a.d])
def sqrt(a):
 a=jet(a)
 if a.v.a<=0:raise Unsafe('sqrt nonpositive')
 val=iv.sqrt(a.v);return Jet(val,[x/(2*val)for x in a.d])
def atan2(y,x):
 y,x=jet(y),jet(x)
 if not (y.v.a>0 or y.v.b<0 or x.v.a>0):raise Unsafe('atan2branch')
 den=x.v**2+y.v**2
 if den.a<=0:raise Unsafe('atan2origin')
 return Jet(iv.atan2(y.v,x.v),[(x.v*a-y.v*b)/den for a,b in zip(y.d,x.d)])
def asin(a):return atan2(a,sqrt(1-a*a))
def objective(box):
 js=[]
 for i,v in enumerate(box):
  d=[I(int(i==j))for j in range(7)];js.append(Jet(v,d))
 r,b1,b2,unused,w1,w3,unusedH=js;de=b1-b2;H=2*r*sin(b1+b2);s=sqrt(1-r*r);A=b2;B=b1;ar=asin(r)
 K=Jet(pi*(z[113]+z[114]-z[2])+pi/2*(z[112]+z[115]-z[1]-z[3]))+Jet(1-z[1]-z[3])*ar+Jet(z[3]-z[1])*de-r*s*(sin(b1)**2+sin(b2)**2)
 for b,w,mu,h,d,dl in [(b1,w1,z[1],z[112],z[34],z[96]),(b2,w3,z[3],z[115],z[39],z[101])]:
  cx=s-2*r*sin(b)*cos(b);cy=-2*r*sin(b)**2
  px=s*cos(w)-r*sin(w);py=-s*sin(w)-r*cos(w)
  cp=cx*px+cy*py;xx=cx*py-cy*px;den=1-cp
  if den.v.a<=0:raise Unsafe('eta denominator')
  eta=atan2(xx,den);eta1=2*b+ar-pi/2
  alpha=w+eta1-eta;u=sqrt((px-cx)**2+(py-cy)**2)/R
  X1=cx*(-r)-cy*s
  K+=Jet(I(1)/2-mu)*w+xx/2+Jet(mu+h)*eta-Jet(d)*u*u-Jet(dl)*u
 t=r/R
 K+=4*r*r*sin(b1+b2)*sin(b1)*sin(b2)+Jet(z[1]-z[9])*b1+Jet(z[3]-z[9])*b2-Jet(z[16])*t*t*sin(b2)**2-Jet(z[78])*t*sin(b2)+Jet(z[20])*t*t*sin(b1)**2+Jet(z[82])*t*sin(b1)

 return K

def mean_bound(box):
 f=objective(box);mid=[I((float(x.a)+float(x.b))/2)for x in box];fc=objective(mid).v
 bound=fc+sum((d*(x-m)for d,x,m in zip(f.d,box,mid)),I(0))
 return min(uf(f.v),uf(bound)),f,bound

