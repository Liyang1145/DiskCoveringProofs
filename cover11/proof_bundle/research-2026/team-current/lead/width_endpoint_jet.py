from patch_smooth_jet import Jet,sin,cos,sqrt,atan2,asin
from interval_joint_patch import I,R,z,pi

def endpoint(r,b,j):
 s=sqrt(1-r*r);x0=2*b-pi/2+asin(r);X=r*sin(x0);D=1-r*cos(x0);w=2*atan2(X,D)
 mu,h,d,l=(z[1],z[112],z[34],z[96])if j==0 else(z[3],z[115],z[39],z[101])
 return -r*s*sin(b)**2+Jet(I(1)/2-mu)*w-X/2-Jet(mu+h)*x0-Jet(d)*(r/R)**2-Jet(l)*r/R
