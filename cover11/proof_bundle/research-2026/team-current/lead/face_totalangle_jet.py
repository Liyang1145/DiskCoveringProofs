"""Face1 chart(r,b1,T,A), reflectedface2(r,b2,T,B)."""
from patch_smooth_jet import Jet,sin,cos,sqrt,atan2,asin,Unsafe
from interval_joint_patch import I,R,z,pi,uf,iv
from width_endpoint_jet import endpoint

def objective(box,j):
 r,b,T,A=[Jet(x,[I(int(i==k))for k in range(7)])for i,x in enumerate(box)];other=T-b;D=(1 if j==0 else -1)*(2*b-T);b1,b2=(b,other)if j==0 else(other,b)
 v=r*(sin(2*b)+sin(2*A));t=(1 if j==0 else -1)*r*(cos(2*A)-cos(2*b))
 f=endpoint(r,b1,0)+endpoint(r,b2,1)+Jet(pi*(z[113]+z[114]-z[2])+pi/2*(z[112]+z[115]-z[1]-z[3]))+Jet(1-z[1]-z[3])*asin(r)
 f+=r*(1-cos(T)*cos(D))*v-r*cos(T)*sin(D)*t
 for i,(a,bb,gg)in enumerate([(z[1]-z[9],-z[16],-z[78]),(z[3]-z[9],z[20],z[82])]):
  if i==j:e=r*sin(A)/R;phi=A
  else:
   X=sin(A)*cos(A)+(1 if j==0 else -1)*cos(T)*sin(D);Y=cos(A)**2-cos(T)*cos(D);e=r*sqrt(X**2+Y**2)/R;phi=atan2(Y,X)
  f+=Jet(a)*phi+Jet(bb)*e*e+Jet(gg)*e
 return f

def legal(box,j):
 r,b,T,A=box;other=T-b
 if other.a>1 or other.b<I('.60946080763725372899').a:return False
 if A.b<=0 or (T-A).b<=0:return False
 H=2*r*iv.sin(b+A);p=b-A;s=iv.sqrt(1-r*r)
 if H.b<=0:return False
 if (iv.cos(T)*iv.sin(2*A-T)).a>0:return False
 if (H*H-2*s*iv.cos(p)*H+2*r*(1-r)).a>0:return False
 # Independent full-extension centered normcap in (r,b,A).
 xx=[box[0],box[1],box[3]];rr,bb,aa=[Jet(x,[I(int(i==k))for k in range(7)])for i,x in enumerate(xx)]
 g=1-sqrt(1-rr*rr)*(sin(2*bb)+sin(2*aa))-rr*cos(2*(bb+aa))
 mm=[I((float(x.a)+float(x.b))/2)for x in xx];rm,bm,am=mm
 gm=1-iv.sqrt(1-rm*rm)*(iv.sin(2*bm)+iv.sin(2*am))-rm*iv.cos(2*(bm+am))
 mv=gm+sum((d*(x-m)for d,x,m in zip(g.d,xx,mm)),I(0))
 if max(g.v.a,mv.a)>0:return False
 return True

def bound(box,j):
 if not legal(box,j):return None
 f=objective(box,j);mid=[I((float(x.a)+float(x.b))/2)for x in box];fm=objective(mid,j);mv=fm.v+sum((a*(x-m)for a,x,m in zip(f.d,box,mid)),I(0));return min(uf(f.v),uf(mv))

def feasible_bound(box,j):
 if not legal(box,j):return None
 from legal_cartesian_value import value
 r,b,T,A=box;other=T-b;b1,b2=(b,other)if j==0 else(other,b);v=r*(iv.sin(2*b)+iv.sin(2*A));t=(1 if j==0 else -1)*r*(iv.cos(2*A)-iv.cos(2*b));val=value(r,b1,b2,v,t)
 if val is None:return None
 up=uf(val)
 try:return min(up,bound(box,j))
 except Unsafe:return up
