"""Both-low circle intersections. j=0/1 norm-face, sign±1; j=2 face-face ridge."""
from patch_smooth_jet import Jet,Unsafe,sin,cos,sqrt,atan2,asin
from interval_joint_patch import I,R,z,pi,uf
from width_endpoint_jet import endpoint

def coords(box,j,sgn):
 r,b1,b2=[Jet(x,[I(int(i==k))for k in range(7)])for i,x in enumerate(box)];s=sqrt(1-r*r)
 if j==2:
  H=2*r*sin(b1+b2);return r,b1,b2,H*cos(b1-b2),H*sin(b1-b2)
 b=b1 if j==0 else b2;sg=-1 if j==0 else 1;cx=r*sin(2*b);cy=sg*r*cos(2*b);vx=s-cx;vy=-cy;dd=1-2*s*r*sin(2*b);d=sqrt(dd);a=r*(1-s*sin(2*b))/d;h=r*sqrt(sin(2*b)*(2*s*(1-r)-s*s*sin(2*b))/dd)
 return r,b1,b2,cx+(a*vx-sgn*h*vy)/d,cy+(a*vy+sgn*h*vx)/d

def objective(box,j,sgn):
 r,b1,b2,v,t=coords(box,j,sgn)
 ans=endpoint(r,b1,0)+endpoint(r,b2,1)+Jet(pi*(z[113]+z[114]-z[2])+pi/2*(z[112]+z[115]-z[1]-z[3]))+Jet(1-z[1]-z[3])*asin(r)
 ans+=r*(sin(b1)**2+sin(b2)**2)*v+r*(sin(b2)*cos(b2)-sin(b1)*cos(b1))*t
 for i,(b,sg,a,bb,gg) in enumerate([(b1,-1,z[1]-z[9],-z[16],-z[78]),(b2,1,z[3]-z[9],z[20],z[82])]):
  if i==j or j==2:
   delta=atan2(t,v);A=b+sg*delta;e=r*sin(A)/R;phi=A
  else:
   X=v-r*sin(2*b);Y=2*r*sin(b)**2+sg*t;e=sqrt(X**2+Y**2)/(2*R);phi=atan2(Y,X)
  ans+=Jet(a)*phi+Jet(bb)*e*e+Jet(gg)*e
 return ans

def legal(box,j,sgn):
 r,b1,b2,v,t=coords(box,j,sgn);s=sqrt(1-r*r)
 if (v*sin(b1)-t*cos(b1)).v.b<=0 or (t*cos(b2)+v*sin(b2)).v.b<=0:return False
 if j<2:
  delta=atan2(t,v)
  signed=cos(b1+b2)*sin(b1-b2-delta)*(1 if j==0 else -1)
  if signed.v.a>0:return False
  b=b2 if j==0 else b1;sg=1 if j==0 else -1;g=(v-r*sin(2*b))**2+(t-sg*r*cos(2*b))**2-r*r
  if g.v.a>0:return False
 else:
  if ((v-s)**2+t*t-(1-r)**2).v.a>0:return False
 return True

def bound(box,j,sgn):
 up=float('inf')
 try:
  if not legal(box,j,sgn):return None
  from legal_cartesian_value import value
  r,b1,b2,v,t=coords(box,j,sgn);val=value(r.v,b1.v,b2.v,v.v,t.v)
  if val is None:return None
  up=uf(val)
  f=objective(box,j,sgn);mid=[I((float(x.a)+float(x.b))/2)for x in box];fc=objective(mid,j,sgn);mv=fc.v+sum((d*(x-m)for d,x,m in zip(f.d,box,mid)),I(0));return min(up,uf(f.v),uf(mv))
 except Unsafe:return up
