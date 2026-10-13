"""Norm+oppositeface legal arc; chartside -1 lowT, +1 highT, cut 0 normendpoint,1 ridge."""
from face_normarc_jet import ends
from patch_smooth_jet import Jet,sin,cos,sqrt,atan2,asin,Unsafe
from interval_joint_patch import I,R,z,pi,uf,iv
from width_endpoint_jet import endpoint

def data(box,j,side,cut):
 r,b1,b2,q=[Jet(x,[I(int(i==k))for k in range(7)])for i,x in enumerate(box)];b=b1 if j==0 else b2;T=b1+b2;D=b1-b2;lo,hi=ends(r,b)
 if cut:
  if side<0:hi=T/2
  else:lo=T/2
 A=lo+(hi-lo)*q;v=r*(sin(2*b)+sin(2*A));t=(1 if j==0 else -1)*r*(cos(2*A)-cos(2*b));return r,b1,b2,T,D,A,v,t,lo,hi

def legal(box,j,side,cut):
 r,b1,b2,q=box;T=b1+b2
 if side<0 and T.a>(pi/2).b:return False
 if side>0 and T.b<(pi/2).a:return False
 lo,hi=ends(Jet(r),Jet(b1 if j==0 else b2));lo,hi=lo.v,hi.v
 if side<0:
  if cut==0 and hi.a>(T/2).b:return False
  if cut==1 and hi.b<(T/2).a:return False
  if lo.a>min(hi.b,(T/2).b):return False
 else:
  if cut==0 and lo.b<(T/2).a:return False
  if cut==1 and lo.a>(T/2).b:return False
  if hi.b<max(lo.a,(T/2).a):return False
 return True

def objective(box,j,side,cut):
 r,b1,b2,T,D,A,v,t,lo,hi=data(box,j,side,cut)
 f=endpoint(r,b1,0)+endpoint(r,b2,1)+Jet(pi*(z[113]+z[114]-z[2])+pi/2*(z[112]+z[115]-z[1]-z[3]))+Jet(1-z[1]-z[3])*asin(r)
 f+=r*(1-cos(T)*cos(D))*v-r*cos(T)*sin(D)*t
 for i,(a,bb,gg)in enumerate([(z[1]-z[9],-z[16],-z[78]),(z[3]-z[9],z[20],z[82])]):
  if i==j:e=r*sin(A)/R;phi=A
  else:
   X=sin(A)*cos(A)+(1 if j==0 else -1)*cos(T)*sin(D);Y=cos(A)**2-cos(T)*cos(D);e=r*sqrt(X**2+Y**2)/R;phi=atan2(Y,X)
  f+=Jet(a)*phi+Jet(bb)*e*e+Jet(gg)*e
 return f

def bound(box,j,side,cut):
 if not legal(box,j,side,cut):return None
 from legal_cartesian_value import value
 r,b1,b2,T,D,A,v,t,lo,hi=data(box,j,side,cut)
 val=value(r.v,b1.v,b2.v,v.v,t.v)
 if val is None:return None
 up=uf(val)
 try:
  f=objective(box,j,side,cut);mid=[I((float(x.a)+float(x.b))/2)for x in box];fm=objective(mid,j,side,cut);mv=fm.v+sum((d*(x-m)for d,x,m in zip(f.d,box,mid)),I(0));up=min(up,uf(f.v),uf(mv))
 except Unsafe:pass
 return up
