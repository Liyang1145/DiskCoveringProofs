"""Unclipped analytic Cartesian hub objective, full5variable intervalAD."""
from patch_smooth_jet import Jet,Unsafe,sin,cos,sqrt,atan2
from interval_joint_patch import I,R,z

def objective(box):
 js=[Jet(x,[I(int(i==j))for j in range(7)])for i,x in enumerate(box)];r,b1,b2,v,t=js
 ans=r*(sin(b1)**2+sin(b2)**2)*v+r*(sin(b2)*cos(b2)-sin(b1)*cos(b1))*t
 for b,sg,a,bb,gg in [(b1,-1,z[1]-z[9],-z[16],-z[78]),(b2,1,z[3]-z[9],z[20],z[82])]:
  sb=sin(b);cb=cos(b);Y=2*r*sb*sb+sg*t;X=v-2*r*sb*cb;Q=X*X+Y*Y;ell=sqrt(Q)/(2*R)
  ans+=Jet(a)*atan2(Y,X)+Jet(bb)*ell*ell+Jet(gg)*ell
 return ans

def mean(box):
 whole=objective(box);mid=[I((float(x.a)+float(x.b))/2)for x in box];center=objective(mid)
 return center.v+sum((d*(x-m)for d,x,m in zip(whole.d,box,mid)),I(0))
