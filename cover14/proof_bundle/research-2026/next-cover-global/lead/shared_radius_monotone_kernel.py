"""Directed box support: old face-loss or exact common-radius polynomial envelope."""
from face_deficit_certificate import *
@lru_cache(None)
def sinpoint(t):
 # t is rational angle/pi; reduce to [-1,1] beforeTaylor.
 t=t%2
 if t>1:t-=2
 return trig(PI*I(t))[0]
def sinbox(lo,hi):
 mid=(lo+hi)/2;v=sinpoint(mid);err=PI*I((hi-lo)/2)
 return I(max(-S,v.lo-err.hi),min(S,v.hi+err.hi),True)
def radius_upper(box):
 lo=[v[0]for v in box];hi=[v[1]for v in box]
 if sum(lo)<=1 or sum(lo)>=2 or min(lo)<=0 or max(lo)>=1:return Q(1)
 hi=lo # x0 decreases in each beta, use lowercorner only
 aa=sum((sinbox(l,h)for l,h in box),I(0));bb=sum((sinbox(lo[i]+lo[j],hi[i]+hi[j])for i,j in combinations(range(3),2)),I(0));cc=sinbox(sum(lo),sum(hi))
 if aa.lo<=0:return Q(1)
 def positive(x):return (aa*x*x-bb*x+cc).lo>=0
 if not positive(Q(1)):return Q(1)
 low=Q(0);high=Q(1)
 for _ in range(10):
  mid=(low+high)/2
  if positive(mid):high=mid
  else:low=mid
 return high
old_boxbound=boxbound
def boxbound(box,p,opts):
 if sum(l for l,h in box)>2:return I(-10**9) # empty: sum gamma=pi and gamma_other>=0 imply sum beta<=2pi
 old=old_boxbound(box,p,opts);X=radius_upper(box)
 if X==1:return old
 # A<=U² X sum sin(beta). Global tangent support with scaled coefficient.
 val=I(0)
 for (lo,hi),pot in zip(box,p):
  aa=U*U*X;pf=float(pot);af=float(aa);opt=0 if pf>=af else(math.pi if pf<=-af else math.acos(pf/af));tf=max(float(lo)*math.pi,min(float(hi)*math.pi,opt));t=max(Q(0),min(Q('3.141592653589'),Q(format(tf,'.12f'))));sn,cs=sc(t);slope=I(aa)*cs-pot;vv=[PI*I(lo)*slope,PI*I(hi)*slope];val+=I(aa)*(sn-I(t)*cs)+I(max(v.lo for v in vv),max(v.hi for v in vv),True)
 return I(min(old.lo,val.lo),min(old.hi,val.hi),True)
