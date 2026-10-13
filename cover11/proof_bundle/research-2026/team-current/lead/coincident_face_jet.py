"""Exact coincident-face surface T=pi/2, full arc parameter A∈[0,pi/2]."""
from patch_smooth_jet import Jet,sin,cos,sqrt,asin
from interval_joint_patch import I,R,z,pi,uf
from width_endpoint_jet import endpoint

def objective(box):
 r,b,A=[Jet(x,[I(int(i==k))for k in range(7)])for i,x in enumerate(box)];b2=Jet(pi/2)-b;B=Jet(pi/2)-A;p=b-A;H=2*r*sin(b+A);v=H*cos(p);t=H*sin(p)
 f=endpoint(r,b,0)+endpoint(r,b2,1)+Jet(pi*(z[113]+z[114]-z[2])+pi/2*(z[112]+z[115]-z[1]-z[3]))+Jet(1-z[1]-z[3])*asin(r)
 f+=r*v+r*(sin(b2)*cos(b2)-sin(b)*cos(b))*t
 for ang,a,bb,gg in [(A,z[1]-z[9],-z[16],-z[78]),(B,z[3]-z[9],z[20],z[82])]:
  e=r*sin(ang)/R;f+=Jet(a)*ang+Jet(bb)*e*e+Jet(gg)*e
 return f

def legal(box):
 r,b,A=box
 from interval_joint_patch import iv
 b2=pi/2-b
 if b2.a>1 or b2.b<I('.60946080763725372899').a:return False
 H=2*r*iv.sin(b+A);p=b-A;s=iv.sqrt(1-r*r)
 if (H*H-2*s*iv.cos(p)*H+2*r*(1-r)).a>0:return False
 return True

def bound(box):
 if not legal(box):return None
 f=objective(box);mid=[I((float(x.a)+float(x.b))/2)for x in box];fm=objective(mid);mv=fm.v+sum((a*(x-m)for a,x,m in zip(f.d,box,mid)),I(0));return min(uf(f.v),uf(mv))
