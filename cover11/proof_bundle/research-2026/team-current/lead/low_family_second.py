"""Independent second-order directional extension of width-eliminated family."""
from face_second_jet import J,sin,cos,sqrt,angle,Unsafe
from interval_joint_patch import I,pi,R,z

def endpoint(r,b,j):
 s=sqrt(1-r*r);ar=angle(r,s);x0=2*b-pi/2+ar;D=1-r*cos(x0);X=r*sin(x0);w=2*angle(X,D)
 mu,h,d,l=(z[1],z[112],z[34],z[96])if j==0 else(z[3],z[115],z[39],z[101]);u=r/R
 return -r*s*sin(b)*sin(b)+J(I('.5')-mu)*w-X/2-J(mu+h)*x0-J(d)*u*u-J(l)*u

def objective(box,j,direction):
 r,b1,b2,p=[J(x,d)for x,d in zip(box,direction)];s=sqrt(1-r*r)
 f=endpoint(r,b1,0)+endpoint(r,b2,1)+J(pi*(z[113]+z[114]-z[2])+pi/2*(z[112]+z[115]-z[1]-z[3]))+J(1-z[1]-z[3])*angle(r,s)
 if j<2:
  A=b1-p;B=b2+p;H=2*r*sin(2*b1-p)if j==0 else 2*r*sin(2*b2+p)
  f+=J(z[3]-z[1])*p+H*r*(sin(b1)*sin(A)+sin(b2)*sin(B))
  for i,(b,ang,a,bb,gg)in enumerate([(b1,A,z[1]-z[9],-z[16],-z[78]),(b2,B,z[3]-z[9],z[20],z[82])]):
   if i==j:e=r*sin(ang)/R;phi=b
   else:X=H-2*r*sin(b)*cos(ang);Y=2*r*sin(b)*sin(ang);e=sqrt(X*X+Y*Y)/(2*R);phi=angle(Y,X)
   f+=J(a)*phi+J(bb)*e*e+J(gg)*e
 else:
  v=s+(1-r)*cos(p);t=(1-r)*sin(p)
  f+=r*(sin(b1)*sin(b1)+sin(b2)*sin(b2))*v+r*(sin(b2)*cos(b2)-sin(b1)*cos(b1))*t
  for b,sg,a,bb,gg in [(b1,-1,z[1]-z[9],-z[16],-z[78]),(b2,1,z[3]-z[9],z[20],z[82])]:
   X=v-r*sin(2*b);Y=2*r*sin(b)*sin(b)+sg*t;e=sqrt(X*X+Y*Y)/(2*R);f+=J(a)*angle(Y,X)+J(bb)*e*e+J(gg)*e
 return f
