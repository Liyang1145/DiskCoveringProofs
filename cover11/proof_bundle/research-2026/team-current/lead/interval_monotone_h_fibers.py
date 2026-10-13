"""Validated perouterbox Hendpoint elimination, else complete scalar envelope."""
import interval_cancel_fibers as base
import interval_patch_delta as fibers
import interval_joint_patch as k
from interval_joint_patch import I,iv,R,z,pi,lf,uf,clip,pos
stats={'positive':0,'negative':0,'fallback':0,'empty':0}
def hdata(outer,dom):
 r,b1,b2,de=outer;A=clip(b1-de,0,pi);B=clip(b2+de,0,pi)
 if A is None or B is None:return None
 def grad(H):
  ans=I(0)
  for b,th,a,beta,gamma in [(b1,A,z[1]-z[9],-z[16],-z[78]),(b2,B,z[3]-z[9],z[20],z[82])]:
   D=2*r*iv.sin(b);y=D*iv.sin(th);x=H-D*iv.cos(th);Q=x**2+y**2
   if Q.a<=0:return None
   ans+=y/2-a*y/Q+beta*x/(2*R*R)+gamma*x/(2*R*iv.sqrt(Q))
  return ans
 lo,hi=dom;cuts=[lo+(hi-lo)*i/8 for i in range(9)];cuts[0]=lo;cuts[-1]=hi
 gs=[grad(I(a,b))for a,b in zip(cuts,cuts[1:])]
 if any(g is None for g in gs):return None
 sign=1 if all(g.a>0 for g in gs) else -1 if all(g.b<0 for g in gs)else 0
 if not sign:return None
 s=iv.sqrt(1-r*r);cs=iv.cos(de);disc=s*s*cs*cs-2*r*(1-r)
 if disc.b<0:return None
 root=iv.sqrt(pos(disc))
 if sign>0:
  cand=[2*r*iv.sin(b1+A),2*r*iv.sin(b2+B),s*cs+root,2*r];end=I(min(v.a for v in cand),min(v.b for v in cand))
 else:
  cand=[2*r*abs(iv.sin(de)),s*cs-root,I(0)];end=I(max(v.a for v in cand),max(v.b for v in cand))
 end=clip(end,I(lo),I(hi))
 return sign,end

def bound(outer,tol=1e-5,maxeval=31):
 st=base.setup(outer)
 if st is None:stats['empty']+=1;return None
 K,fs=st;rr=[fibers.envelope(fun,dom,tol,maxeval)for fun,dom in fs[:2]];fun,dom=fs[2];hd=hdata(outer,dom)
 if hd is None:stats['fallback']+=1;rr.append(fibers.envelope(fun,dom,tol,maxeval))
 else:
  sign,end=hd;stats['positive'if sign>0 else'negative']+=1
  val=None
  if end is not None:
   r,b1,b2,de=outer;A=clip(b1-de,0,pi);B=clip(b2+de,0,pi);val=I(0)
   for b,th,a,beta,gamma in [(b1,A,z[1]-z[9],-z[16],-z[78]),(b2,B,z[3]-z[9],z[20],z[82])]:
    D=2*r*iv.sin(b);y=pos(D*iv.sin(th));x=end-D*iv.cos(th);Q=x**2+y**2
    if Q.a<=0:val=None;break
    e=iv.sqrt(Q)/(2*R);val+=end*y/2+a*iv.atan2(y,x)+k.quad_range(beta,gamma,e)
   if val is None:
    rr.append(fibers.envelope(fun,dom,tol,maxeval))
    return None if any(a['upper']==-float('inf')for a in rr)else {'upper':uf(K+sum((I(a['upper'])for a in rr),I(0))),'fibers':rr}
  rr.append({'upper':uf(val)if val is not None else -float('inf'),'method':'monotone_endpoint','sign':sign})
 if any(a['upper']==-float('inf')for a in rr):return None
 return {'upper':uf(K+sum((I(a['upper'])for a in rr),I(0))),'fibers':rr}
