"""Independent second-order scalar interval AD on Cartesian face circles. No shared hand derivatives."""
from interval_joint_patch import I,iv,R,z,uf,lf
class Unsafe(Exception):pass
class J:
 def __init__(self,v,d=0,h=0):self.v=v if hasattr(v,'_mpi_')else I(v);self.d=d if hasattr(d,'_mpi_')else I(d);self.h=h if hasattr(h,'_mpi_')else I(h)
 def __add__(a,b):
  b=J.coerce(b);return J(a.v+b.v,a.d+b.d,a.h+b.h)
 __radd__=__add__
 def __neg__(a):return J(-a.v,-a.d,-a.h)
 def __sub__(a,b):return a+-J.coerce(b)
 def __rsub__(a,b):return J.coerce(b)+-a
 def __mul__(a,b):
  b=J.coerce(b);return J(a.v*b.v,a.d*b.v+a.v*b.d,a.h*b.v+2*a.d*b.d+a.v*b.h)
 __rmul__=__mul__
 def __truediv__(a,b):
  b=J.coerce(b)
  if b.v.a<=0<=b.v.b:raise Unsafe('zero divisor')
  return a*J(1/b.v,-b.d/b.v**2,2*b.d**2/b.v**3-b.h/b.v**2)
 def __rtruediv__(a,b):return J.coerce(b)/a
 @staticmethod
 def coerce(a):return a if isinstance(a,J)else J(a)
def sin(x):
 x=J.coerce(x);return J(iv.sin(x.v),iv.cos(x.v)*x.d,iv.cos(x.v)*x.h-iv.sin(x.v)*x.d**2)
def cos(x):
 x=J.coerce(x);return J(iv.cos(x.v),-iv.sin(x.v)*x.d,-iv.sin(x.v)*x.h-iv.cos(x.v)*x.d**2)
def sqrt(x):
 x=J.coerce(x)
 if x.v.a<=0:raise Unsafe('sqrt')
 v=iv.sqrt(x.v);return J(v,x.d/(2*v),x.h/(2*v)-x.d**2/(4*v**3))
def angle(y,x):
 x=J.coerce(x);y=J.coerce(y);q=x.v**2+y.v**2
 if q.a<=0 or not(y.v.a>0 or y.v.b<0 or x.v.a>0):raise Unsafe('angle')
 n=x.v*y.d-y.v*x.d;nd=x.v*y.h-y.v*x.h;qd=2*(x.v*x.d+y.v*y.d)
 return J(iv.atan2(y.v,x.v),n/q,nd/q-n*qd/q**2)
def coords(box,j):
 r,b1,b2,de=box;r,b1,b2=map(J,[r,b1,b2]);de=J(de,1);A=b1-de;B=b2+de
 if j==0:v=r*(sin(2*b1)+sin(2*A));t=r*(cos(2*A)-cos(2*b1))
 else:v=r*(sin(2*b2)+sin(2*B));t=r*(cos(2*b2)-cos(2*B))
 return r,b1,b2,v,t

def legal(box,j):
 r,b1,b2,d=box;s=iv.sqrt(1-r*r)
 if (iv.cos(b1)-r).b<0 or (iv.cos(b2)-r).b<0:return False
 if (b1-d).b<=0 or (b2+d).b<=0:return False
 if j==0 and (d-(b1-b2)).a>0:return False
 if j==1 and (d-(b1-b2)).b<0:return False
 H=2*r*iv.sin(2*(b1 if j==0 else b2)+(-d if j==0 else d))
 if H.b<=0:return False
 # Direct opposite-face cap; never invalid same-face subtraction.
 other=2*r*iv.sin(2*(b2 if j==0 else b1)+(d if j==0 else -d))-H
 if other.b<0:return False
 if (H*H-2*s*iv.cos(d)*H+2*r*(1-r)).a>0:return False
 return True

def objective(box,j):
 r,b1,b2,v,t=coords(box,j)
 ans=r*(sin(b1)*sin(b1)+sin(b2)*sin(b2))*v+r*(sin(b2)*cos(b2)-sin(b1)*cos(b1))*t
 for b,sg,a,bb,gg in [(b1,-1,z[1]-z[9],-z[16],-z[78]),(b2,1,z[3]-z[9],z[20],z[82])]:
  Y=2*r*sin(b)*sin(b)+sg*t;X=v-2*r*sin(b)*cos(b);e=sqrt(X*X+Y*Y)/(2*R)
  ans+=J(a)*angle(Y,X)+J(bb)*e*e+J(gg)*e
 return ans

def saturated(box,j):
 r,b1,b2,de=box;r,b1,b2=map(J,[r,b1,b2]);de=J(de,1);A=b1-de;B=b2+de
 H=2*r*sin(2*b1-de)if j==0 else 2*r*sin(2*b2+de)
 ans=J(z[3]-z[1])*de+H*r*(sin(b1)*sin(A)+sin(b2)*sin(B))
 for i,(b,ang,a,bb,gg)in enumerate([(b1,A,z[1]-z[9],-z[16],-z[78]),(b2,B,z[3]-z[9],z[20],z[82])]):
  if i==j:e=r*sin(ang)/R;phi=b
  else:
   X=H-2*r*sin(b)*cos(ang);Y=2*r*sin(b)*sin(ang);e=sqrt(X*X+Y*Y)/(2*R);phi=angle(Y,X)
  ans+=J(a)*phi+J(bb)*e*e+J(gg)*e
 return ans
