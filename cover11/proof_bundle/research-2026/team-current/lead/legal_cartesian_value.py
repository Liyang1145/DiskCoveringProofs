"""Value-only feasible-set bound. Physical clips NEVER used for derivatives."""
from interval_joint_patch import I,iv,R,z,pi
from width_endpoint_jet import endpoint
from patch_smooth_jet import Jet

def value(r,b1,b2,v,t):
 c=lambda x:Jet(x)
 ans=(endpoint(c(r),c(b1),0)+endpoint(c(r),c(b2),1)).v+pi*(z[113]+z[114]-z[2])+pi/2*(z[112]+z[115]-z[1]-z[3])+(1-z[1]-z[3])*iv.atan2(r,iv.sqrt(1-r*r))
 ans+=r*(iv.sin(b1)**2+iv.sin(b2)**2)*v+r*(iv.sin(b2)*iv.cos(b2)-iv.sin(b1)*iv.cos(b1))*t
 for b,sg,a,bb,gg in [(b1,-1,z[1]-z[9],-z[16],-z[78]),(b2,1,z[3]-z[9],z[20],z[82])]:
  X=v-r*iv.sin(2*b);Y=2*r*iv.sin(b)**2+sg*t
  # Own face disk vertical cap gives Y>=0 (not the wedge). Retain closed relaxation.
  if Y.b<0:return None
  Y=I(max(I(0).a,Y.a),Y.b);Q=X**2+Y**2;e=iv.sqrt(Q)/(2*R)
  if e.a>(r/R).b:return None
  e=I(e.a,min(e.b,(r/R).b));phi=iv.atan2(Y,X)
  if X.a<=0 and Y.a<=0:phi=I(0,pi.b)
  # bb>0: convex quadratic attains upper at an interval endpoint.
  vals=[bb*I(e.a)**2+gg*I(e.a),bb*I(e.b)**2+gg*I(e.b)];up=max(a.b for a in vals)
  ans+=a*phi+I(up)
 return ans
