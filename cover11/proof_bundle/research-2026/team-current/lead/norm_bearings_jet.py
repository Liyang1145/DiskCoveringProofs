"""Normcircle left-half chart (r,b1,T,q), centralangle=pi+q."""
from patch_smooth_jet import Jet,sin,cos,sqrt,atan2,asin,Unsafe
from interval_joint_patch import I,R,z,pi,uf,iv
from width_endpoint_jet import endpoint

def data(box):
 r,b,b2,q=[Jet(x,[I(int(i==k))for k in range(7)])for i,x in enumerate(box)];v=sqrt(1-r*r)-(1-r)*cos(q);t=-(1-r)*sin(q);return r,b,b2,b+b2,b-b2,v,t

def objective(box):
 r,b1,b2,T,D,v,t=data(box)
 f=endpoint(r,b1,0)+endpoint(r,b2,1)+Jet(pi*(z[113]+z[114]-z[2])+pi/2*(z[112]+z[115]-z[1]-z[3]))+Jet(1-z[1]-z[3])*asin(r)
 f+=r*(1-cos(T)*cos(D))*v-r*cos(T)*sin(D)*t
 for b,sg,a,bb,gg in [(b1,-1,z[1]-z[9],-z[16],-z[78]),(b2,1,z[3]-z[9],z[20],z[82])]:
  X=v-r*sin(2*b);Y=2*r*sin(b)**2+sg*t;e=sqrt(X**2+Y**2)/(2*R);f+=Jet(a)*atan2(Y,X)+Jet(bb)*e*e+Jet(gg)*e
 return f

def bound(box):
 r,b1,b2,T,D,v,t=data(box)
 if b2.v.a>1 or b2.v.b<I('.60946080763725372899').a:return None
 mid=[I((float(x.a)+float(x.b))/2)for x in box];rm,bm1,bm2,Tm,Dm,vm,tm=data(mid)
 for b,bm,sg in [(b1,bm1,-1),(b2,bm2,1)]:
  g=(v-r*sin(2*b))**2+(t-sg*r*cos(2*b))**2-r*r
  gm=(vm-rm*sin(2*bm))**2+(tm-sg*rm*cos(2*bm))**2-rm*rm
  mv=gm.v+sum((d*(x-m)for d,x,m in zip(g.d,box,mid)),I(0))
  if max(g.v.a,mv.a)>0:return None
 if (v*sin(b1)-t*cos(b1)).v.b<=0 or (v*sin(b2)+t*cos(b2)).v.b<=0:return None
 from legal_cartesian_value import value
 val=value(r.v,b1.v,b2.v,v.v,t.v)
 if val is None:return None
 up=uf(val)
 try:
  f=objective(box);fm=objective(mid);mv=fm.v+sum((d*(x-m)for d,x,m in zip(f.d,box,mid)),I(0));up=min(up,uf(f.v),uf(mv))
 except Unsafe:pass
 return up
