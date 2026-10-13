"""Exact cancellation before 4Douter/3scalar envelopes. Alternative enclosure intersects oldkernel."""
import interval_patch_delta as base
import interval_joint_patch as k
from interval_joint_patch import I,iv,pi,R,z,asin,acos,lf,uf,clip,quad_range
import math

def setup(outer):
 old=base.setup(outer)
 if old is None:return None
 _,fs=old;r,b1,b2,de=outer;A=clip(b1-de,0,pi);B=clip(b2+de,0,pi);s=iv.sqrt(1-r*r);phi=asin(r)
 K=pi*(z[113]+z[114]-z[2])+pi/2*(z[112]+z[115]-z[1]-z[3])+(1-z[1]-z[3])*phi+(z[3]-z[1])*de
 def wf(w,b,mu,h,d,l):
  # x0=2b-acosr, frozenneighborbearingparameter
  x0=2*b-(pi/2-phi);D=1-r*iv.cos(x0);X=r*iv.sin(x0)
  cp=D*iv.cos(w)+X*iv.sin(w);xx=X*iv.cos(w)-D*iv.sin(w)
  cnorm=1+r*r-2*r*iv.cos(x0)
  dsq=1+cnorm-2*cp
  # independent identity cancelsnearw=0
  sw=iv.sin(w/2);dalt=r*r+4*sw*sw-4*r*iv.sin(x0+w/2)*sw
  dsq=I(max(dsq.a,dalt.a),min(dsq.b,dalt.b));dsq=clip(dsq,(R*I(19)/100)**2,r*r)
  if dsq is None:return None
  den=clip(1-cp,I(1)/14,2)
  if den is None:return None
  eta=iv.atan2(xx,den);u=iv.sqrt(dsq)/R
  return -r*s*iv.sin(b)**2+(I(1)/2-mu)*w+xx/2+(mu+h)*eta+quad_range(-d,-l,u)
 return K,[(lambda w:wf(w,b1,z[1],z[112],z[34],z[96]),fs[0][1]),(lambda w:wf(w,b2,z[3],z[115],z[39],z[101]),fs[1][1]),fs[2]]

def bound(outer,tol=1e-5,maxeval=31):
 st=setup(outer)
 if st is None:return None
 K,fs=st;rr=[base.envelope(fun,dom,tol,maxeval)for fun,dom in fs]
 if any(a['upper']==-math.inf for a in rr):return None
 total=K+sum((I(row['upper'])for row in rr),I(0))
 return {'upper':uf(total),'fibers':rr,'constant':[lf(K),uf(K)]}
