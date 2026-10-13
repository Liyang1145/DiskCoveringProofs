"""Norm-legal arc parametrization: no change to pinned original kernels."""
from patch_smooth_jet import Jet,sin,cos,sqrt,atan2,asin,Unsafe
from interval_joint_patch import I,R,z,pi,uf,iv
from width_endpoint_jet import endpoint

def ends(r,b):
 s=sqrt(1-r*r);sn=sin(2*b);u=s-r*sn;v=r*cos(2*b);c=1-s*sn
 h=sqrt(s*sn*(2*(1-r)-s*sn));theta=atan2(c,h);gamma=atan2(v,u)
 return (theta-gamma)/2,(Jet(pi)-theta-gamma)/2

def data(box,j):
 r,b,T,q=[Jet(x,[I(int(i==k))for k in range(7)])for i,x in enumerate(box)];lo,hi=ends(r,b);A=lo+(hi-lo)*q;other=T-b;D=(1 if j==0 else -1)*(2*b-T);b1,b2=(b,other)if j==0 else(other,b);v=r*(sin(2*b)+sin(2*A));t=(1 if j==0 else -1)*r*(cos(2*A)-cos(2*b));return r,b1,b2,T,D,A,v,t

def objective(box,j):
 r,b1,b2,T,D,A,v,t=data(box,j)
 f=endpoint(r,b1,0)+endpoint(r,b2,1)+Jet(pi*(z[113]+z[114]-z[2])+pi/2*(z[112]+z[115]-z[1]-z[3]))+Jet(1-z[1]-z[3])*asin(r)
 f+=r*(1-cos(T)*cos(D))*v-r*cos(T)*sin(D)*t
 for i,(a,bb,gg)in enumerate([(z[1]-z[9],-z[16],-z[78]),(z[3]-z[9],z[20],z[82])]):
  if i==j:e=r*sin(A)/R;phi=A
  else:
   X=sin(A)*cos(A)+(1 if j==0 else -1)*cos(T)*sin(D);Y=cos(A)**2-cos(T)*cos(D);e=r*sqrt(X**2+Y**2)/R;phi=atan2(Y,X)
  f+=Jet(a)*phi+Jet(bb)*e*e+Jet(gg)*e
 return f

def bound(box,j):
 from legal_cartesian_value import value
 r,b1,b2,T,D,A,v,t=data(box,j);other=(b2 if j==0 else b1).v
 if other.a>1 or other.b<I('.60946080763725372899').a:return None
 if A.v.b<=0 or (T-A).v.b<=0:return None
 if (cos(T)*sin(2*A-T)).v.a>0:return None
 val=value(r.v,b1.v,b2.v,v.v,t.v)
 if val is None:return None
 up=uf(val)
 try:
  f=objective(box,j);mid=[I((float(x.a)+float(x.b))/2)for x in box];fm=objective(mid,j);mv=fm.v+sum((d*(x-m)for d,x,m in zip(f.d,box,mid)),I(0));up=min(up,uf(f.v),uf(mv))
 except Unsafe:pass
 return up
