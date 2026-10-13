"""Independent Fraction replay with exact boxcoverage/disjointness audit."""
import json,math,time
from itertools import combinations
from functools import lru_cache
from joint_innernorm_fraction_replay import replay,F,pi,U,add,neg,mul,point,trig,rnd,vmax,P
@lru_cache(None)
def sc(t):return tuple(map(rnd,trig(t)))
def sub(a,b):return add(a,neg(b))
def oldedge(t,p):
 sn,cs=sc(t);slope=add(mul(point(U*U),cs),point(-p));return add(mul(point(U*U),sub(sn,mul(point(t),cs))),mul(pi,vmax([point(F(0)),slope])))
def sup(lo,hi,p):
 a=mul(pi,point(lo));b=mul(pi,point(hi));opt=0 if float(p)>=float(U*U)else(math.pi if float(p)<=-float(U*U)else math.acos(float(p/(U*U))));tf=max(float(lo)*math.pi,min(float(hi)*math.pi,opt));t=max(F(0),min(F('3.141592653589'),F(format(tf,'.12f'))));sn,cs=sc(t);slope=add(mul(point(U*U),cs),point(-p));return add(mul(point(U*U),sub(sn,mul(point(t),cs))),vmax([mul(a,slope),mul(b,slope)]))
def cosiv(v):
 mid=(v[0]+v[1])/2;_,cs=sc(mid);err=(v[1]-v[0])/2;return(cs[0]-err,cs[1]+err)
def checkboxes(boxes):
 assert all(F(0)<=a<b<=F(1)for box in boxes for a,b in box)
 assert sum((math.prod(b-a for a,b in box)for box in boxes),F(0))==1
 for b1,b2 in combinations(boxes,2):assert any(max(a,c)>=min(b,d)for(a,b),(c,d)in zip(b1,b2))
@lru_cache(None)
def sinpoint(t):
 t=t%2
 if t>1:t-=2
 sign=-1 if t<0 else 1;t=abs(t)
 if t==0 or t==1:return point(F(0))
 v=mul(pi,point(t));mid=(v[0]+v[1])/2;err=(v[1]-v[0])/2;sn,_=sc(mid);ans=(sn[0]-err,sn[1]+err);return neg(ans) if sign<0 else ans
def sinbox(lo,hi):
 v=sinpoint((lo+hi)/2);err=mul(pi,point((hi-lo)/2))[1];return(max(F(-1),v[0]-err),min(F(1),v[1]+err))
def radius_upper(box):
 lo=[v[0]for v in box];hi=[v[1]for v in box]
 if sum(lo)<=1 or sum(lo)>=2 or min(lo)<=0 or max(lo)>=1:return F(1)
 hi=lo # coordinate monotonicity of common-radius root
 aa=point(F(0));bb=point(F(0))
 for l in lo:aa=add(aa,sinpoint(l))
 for i,j in combinations(range(3),2):bb=add(bb,sinbox(lo[i]+lo[j],hi[i]+hi[j]))
 cc=sinbox(sum(lo),sum(hi))
 if aa[0]<=0:return F(1)
 def positive(x):return add(sub(mul(aa,point(x*x)),mul(bb,point(x))),cc)[0]>=0
 if not positive(F(1)):return F(1)
 low=F(0);high=F(1)
 for _ in range(10):
  mid=(low+high)/2
  if positive(mid):high=mid
  else:low=mid
 return high
def scaled_sup(lo,hi,p,X):
 aa=U*U*X;a=mul(pi,point(lo));b=mul(pi,point(hi));opt=0 if float(p)>=float(aa)else(math.pi if float(p)<=-float(aa)else math.acos(float(p/aa)));tf=max(float(lo)*math.pi,min(float(hi)*math.pi,opt));t=max(F(0),min(F('3.141592653589'),F(format(tf,'.12f'))));sn,cs=sc(t);slope=add(mul(point(aa),cs),point(-p));return add(mul(point(aa),sub(sn,mul(point(t),cs))),vmax([mul(a,slope),mul(b,slope)]))
def verify(q,edges,faces,row,cert):
 t=list(map(F,row['rational_angles']));y=list(map(F,row['rational_potentials']));ee=[tuple(sorted(e))for e in combinations(faces[cert['face']],2)];assert all(sum(all(v in f for v in e)for f in faces)in (1,2) for e in ee);p=[sum(y[v]for v in e)for e in ee];base=replay(q,edges,row)
 for e,pp in zip(ee,p):base=sub(base,oldedge(t[q+edges.index(e)],pp))
 boxes=[[(F(a),F(b))for a,b in box]for box in cert['leaves']];checkboxes(boxes);vals=[]
 for box in boxes:
  if sum(l for l,h in box)>2:vals.append(point(F(-10**9)));continue
  lo=[v[0]for v in box];hi=[v[1]for v in box];dist=mul(pi,point(max(F(0),sum(lo)-1,1-sum(hi))));pen=mul(point(U*U/2),mul(sub(point(F(1)),cosiv(mul(pi,point(min(lo))))),dist));b=point(F(0))
  for(a,c),pp in zip(box,p):b=add(b,sup(a,c,pp))
  old=sub(b,pen);X=radius_upper(box)
  if X<1:
   val=point(F(0))
   for(a,c),pp in zip(box,p):val=add(val,scaled_sup(a,c,pp,X))
   old=(min(old[0],val[0]),min(old[1],val[1]))
  vals.append(old)
 return rnd(add(base,vmax(vals)))
