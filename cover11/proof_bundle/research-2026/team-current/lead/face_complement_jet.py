"""Full-extension source-vector rewrite using T=b1+b2; no divided cosT."""
from patch_smooth_jet import Jet,sin,cos,sqrt,atan2,asin,Unsafe
from interval_joint_patch import I,R,z,pi,uf
from width_endpoint_jet import endpoint

def objective(box,j):
 r,b1,b2,p=[Jet(x,[I(int(i==k))for k in range(7)])for i,x in enumerate(box)]
 A=b1-p;B=b2+p;T=b1+b2;D=b1-b2;own=A if j==0 else B
 H=2*r*sin(2*b1-p)if j==0 else 2*r*sin(2*b2+p)
 ans=endpoint(r,b1,0)+endpoint(r,b2,1)+Jet(pi*(z[113]+z[114]-z[2])+pi/2*(z[112]+z[115]-z[1]-z[3]))+Jet(1-z[1]-z[3])*asin(r)
 # Cartesian objective angles, including own phi=own (not polarphi=b).
 v=H*cos(p);t=H*sin(p);ans+=r*(sin(b1)**2+sin(b2)**2)*v+r*(sin(b2)*cos(b2)-sin(b1)*cos(b1))*t
 for i,(a,bb,gg)in enumerate([(z[1]-z[9],-z[16],-z[78]),(z[3]-z[9],z[20],z[82])]):
  if i==j:e=r*sin(own)/R;phi=own
  else:
   X=cos(own)*sin(own)+(1 if j==0 else -1)*cos(T)*sin(D)
   Y=cos(own)**2-cos(T)*cos(D)
   e=r*sqrt(X**2+Y**2)/R;phi=atan2(Y,X)
  ans+=Jet(a)*phi+Jet(bb)*e*e+Jet(gg)*e
 return ans
