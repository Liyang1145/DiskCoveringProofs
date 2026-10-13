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
def verify(q,edges,faces,row,cert):
 t=list(map(F,row['rational_angles']));y=list(map(F,row['rational_potentials']));ee=[tuple(sorted(e))for e in combinations(faces[cert['face']],2)];assert all(sum(all(v in f for v in e)for f in faces)in (1,2) for e in ee);p=[sum(y[v]for v in e)for e in ee];base=replay(q,edges,row)
 for e,pp in zip(ee,p):base=sub(base,oldedge(t[q+edges.index(e)],pp))
 boxes=[[(F(a),F(b))for a,b in box]for box in cert['leaves']];checkboxes(boxes);vals=[]
 for box in boxes:
  lo=[v[0]for v in box];hi=[v[1]for v in box];dist=mul(pi,point(max(F(0),sum(lo)-1,1-sum(hi))));pen=mul(point(U*U/2),mul(sub(point(F(1)),cosiv(mul(pi,point(min(lo))))),dist));b=point(F(0))
  for(a,c),pp in zip(box,p):b=add(b,sup(a,c,pp))
  vals.append(sub(b,pen))
 return rnd(add(base,vmax(vals)))
