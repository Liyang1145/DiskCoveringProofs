"""Convexlenschart: outer(r,b1,b2,v); scalar(w1,w3,t)."""
import interval_collapsed_fibers as base
import interval_patch_delta as fibers
import interval_joint_patch as k
from interval_joint_patch import I,iv,R,z,pi,lf,uf,clip,pos,asin

def setup(outer):
 r,b1,b2,v=outer;s=iv.sqrt(1-r*r)
 discs=[(r*iv.sin(2*b1),-r*iv.cos(2*b1),r),(r*iv.sin(2*b2),r*iv.cos(2*b2),r),(s,I(0),1-r)];low=-iv.inf;high=iv.inf
 for cx,cy,rad in discs:
  q=rad*rad-(v-cx)**2
  if q.b<0:return None
  root=iv.sqrt(pos(q));low=max(low,(cy-root).a);high=min(high,(cy+root).b)
 low=max(low,(-v*iv.tan(b2)).a);high=min(high,(v*iv.tan(b1)).b)
 if high<low:return None
 tdom=I(low,high);de=iv.atan2(tdom,v);st=base.setup([r,b1,b2,de])
 if st is None:return None
 _,fs=st;phi=asin(r);K=pi*(z[113]+z[114]-z[2])+pi/2*(z[112]+z[115]-z[1]-z[3])+(1-z[1]-z[3])*phi
 def tf(t):
  ans=r*(iv.sin(b1)**2+iv.sin(b2)**2)*v+r*(iv.sin(b2)*iv.cos(b2)-iv.sin(b1)*iv.cos(b1))*t
  for b,sg,a,bb,gg in [(b1,-1,z[1]-z[9],-z[16],-z[78]),(b2,1,z[3]-z[9],z[20],z[82])]:
   sb=iv.sin(b);cb=iv.cos(b);Y=2*r*sb*sb+sg*t;X=v-2*r*sb*cb
   if Y.b<0:return None
   Y=pos(Y);Q=clip(X*X+Y*Y,I(1)/50000**2,4*r*r)
   if Q is None:return None
   ee=iv.sqrt(Q)/(2*R);ans+=a*iv.atan2(Y,X)+k.quad_range(bb,gg,ee)

  return ans
 return K,[fs[0],fs[1],(tf,(lf(tdom),uf(tdom)))]
def bound(outer,tol=1e-5,maxeval=31):
 st=setup(outer)
 if st is None:return None
 K,fs=st;rr=[fibers.envelope(fun,dom,tol,maxeval)for fun,dom in fs]
 if any(a['upper']==-float('inf')for a in rr):return None
 return {'upper':uf(K+sum((I(a['upper'])for a in rr),I(0))),'fibers':rr}
