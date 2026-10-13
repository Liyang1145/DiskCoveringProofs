"""Facecap cone chart: outer(r,b1,b2,u), H=2r sinu; scalarfibers(w1,w3,epsilon)."""
import interval_cancel_fibers as base
import interval_patch_delta as fibers
import interval_joint_patch as k
from interval_joint_patch import I,iv,R,z,pi,lf,uf,clip,pos,asin,acos

def setup(outer):
 r,b1,b2,u=outer;s=iv.sqrt(1-r*r);T=b1+b2;D=b1-b2;beta=I(min(T.a,(pi-T).a),min(T.b,(pi-T).b))
 if u.a<=0 or u.a>beta.b:return None
 H=2*r*iv.sin(u);q=(H*H+2*r*(1-r))/(2*s*H)
 if q.a>1:return None
 q=clip(q,0,1);cap=acos(q)
 low=max((u-beta).a,(-u-D).a,(-cap-D).a,(-b1).a);high=min((beta-u).b,(u-D).b,(cap-D).b,b2.b)
 if high<low:return None
 ep=I(low,high);de=D+ep
 # Existingwidthevaluatorcanbeobtainedfrombroadnecessarydelta projection;
 # its H-feasibilityrejection is safe (containsalleps-derivedpoints).
 st=base.setup([r,b1,b2,de])
 if st is None:return None
 oldK,fs=st;phi=asin(r)
 K=pi*(z[113]+z[114]-z[2])+pi/2*(z[112]+z[115]-z[1]-z[3])+(1-z[1]-z[3])*phi
 def ef(eps):
  delta=D+eps;A=clip(b2-eps,0,pi);B=clip(b1+eps,0,pi)
  if A is None or B is None:return None
  ans=(z[3]-z[1])*delta
  for b,th,a,bb,gg in [(b1,A,z[1]-z[9],-z[16],-z[78]),(b2,B,z[3]-z[9],z[20],z[82])]:
   dd=2*r*iv.sin(b);y=pos(dd*iv.sin(th));x=H-dd*iv.cos(th);Q=clip(x*x+y*y,I(1)/50000**2,4*r*r)
   if Q is None:return None
   ee=iv.sqrt(Q)/(2*R);ans+=H*y/2+a*iv.atan2(y,x)+k.quad_range(bb,gg,ee)
  return ans
 return K,[fs[0],fs[1],(ef,(lf(ep),uf(ep)))]
def bound(outer,tol=1e-5,maxeval=31):
 st=setup(outer)
 if st is None:return None
 K,fs=st;rr=[fibers.envelope(fun,dom,tol,maxeval)for fun,dom in fs]
 if any(a['upper']==-float('inf')for a in rr):return None
 return {'upper':uf(K+sum((I(a['upper'])for a in rr),I(0))),'fibers':rr}
