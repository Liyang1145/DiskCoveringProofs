"""Exact crossfiber bearing-area cancellation before taking scalar suprema."""
import interval_cartesian_cancel as base
import interval_patch_delta as fibers
import interval_joint_patch as k
from interval_joint_patch import I,iv,R,z,pi,lf,uf,asin,clip,pos

def setup(outer):
 st=base.setup(outer)
 if st is None:return None
 K,fs=st;r,b1,b2,v=outer;s=iv.sqrt(1-r*r);phi=asin(r)
 K+=r*(v-s)*(iv.sin(b1)**2+iv.sin(b2)**2)
 def width(w,b,mu,h,d,l,filtered=True):
  x0=2*b-pi/2+phi;p=iv.cos(w)-r*iv.cos(x0+w);x=-iv.sin(w)+r*iv.sin(x0+w)
  sw=iv.sin(w/2);q=r*r+4*sw**2-4*r*iv.sin(x0+w/2)*sw;den=1-p
  if filtered:
   q=clip(q,(R*I(19)/100)**2,r*r);den=clip(den,I(1)/14,2)
   if q is None or den is None:return None
  elif q.a<=0 or den.a<=0:return None
  u=iv.sqrt(q)/R;eta=iv.atan2(x,den)
  return (I(1)/2-mu)*w+x/2+(mu+h)*eta+k.quad_range(-d,-l,u)
 def wf(w,b,mu,h,d,l):
  raw=width(w,b,mu,h,d,l)
  if raw is None:return None
  x0=2*b-pi/2+phi;sw=iv.sin(w/2);q=r*r+4*sw**2-4*r*iv.sin(x0+w/2)*sw;p=iv.cos(w)-r*iv.cos(x0+w)
  if q.a<=0 or (1-p).a<=0:return raw
  bm=I((float(b.a)+float(b.b))/2);center=width(w,bm,mu,h,d,l,False)
  if center is None:return raw
  db=r*iv.cos(x0+w)+(mu+h)*2*r*(r+iv.cos(x0+w)-iv.cos(x0))/q-(d/(R*R)+l/(2*R*iv.sqrt(q)))*4*r*(iv.sin(x0)-iv.sin(x0+w))
  mv=center+db*(b-bm)
  return I(max(raw.a,mv.a),min(raw.b,mv.b))
 def tf(t):
  ans=r*(iv.sin(b2)*iv.cos(b2)-iv.sin(b1)*iv.cos(b1))*t
  for b,sg,a,bb,gg in [(b1,-1,z[1]-z[9],-z[16],-z[78]),(b2,1,z[3]-z[9],z[20],z[82])]:
   Y=2*r*iv.sin(b)**2+sg*t;X=v-r*iv.sin(2*b)
   if Y.b<0:return None
   Y=pos(Y);Q=clip(X*X+Y*Y,I(1)/50000**2,4*r*r)
   if Q is None:return None
   ee=iv.sqrt(Q)/(2*R);ans+=a*iv.atan2(Y,X)+k.quad_range(bb,gg,ee)
  return ans
 return K,[(lambda w:wf(w,b1,z[1],z[112],z[34],z[96]),fs[0][1]),(lambda w:wf(w,b2,z[3],z[115],z[39],z[101]),fs[1][1]),(tf,fs[2][1])]
def bound(outer,tol=1e-5,maxeval=31):
 st=setup(outer)
 if st is None:return None
 K,fs=st;rr=[fibers.envelope(fun,dom,tol,maxeval)for fun,dom in fs]
 if any(a['upper']==-float('inf')for a in rr):return None
 return {'upper':uf(K+sum((I(a['upper'])for a in rr),I(0))),'fibers':rr}
