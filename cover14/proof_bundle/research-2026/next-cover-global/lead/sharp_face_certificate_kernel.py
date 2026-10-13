"""Directed interval 3D support certificate with radiusdeficit; dyadicboxes partition[0,pi]^3."""
import json,math,heapq,time
from itertools import combinations
from functools import lru_cache
from joint_innernorm_probe import verify,I,Q,S,PI,U,trig,P
@lru_cache(None)
def sc(t):return trig(I(t))
@lru_cache(None)
def costerm(t):return trig(PI*I(t))[1]
def edgeold(x,p):
 sn,cs=sc(x);slope=I(U*U)*cs-p
 return I(U*U)*(sn-I(x)*cs)+PI*I(max(0,slope.lo),max(0,slope.hi),True)
def support(lo,hi,p,opt):
 a=PI*I(lo);b=PI*I(hi);tf=max(float(lo)*math.pi,min(float(hi)*math.pi,opt));t=max(Q(0),min(Q('3.141592653589'),Q(format(tf,'.12f'))));sn,cs=sc(t);slope=I(U*U)*cs-p;vv=[a*slope,b*slope]
 return I(U*U)*(sn-I(t)*cs)+I(max(x.lo for x in vv),max(x.hi for x in vv),True)
@lru_cache(None)
def gterm(h):
 if h==1:return I(1)
 sn,cs=trig(PI*I(h)/2)
 return PI*I(1-h)/2*sn/cs
def boxbound(box,p,opts):
 lo=[v[0]for v in box];hi=[v[1]for v in box];dist=I(max(Q(0),sum(lo)-1,1-sum(hi)))*PI;weights=[2*(1-costerm(l))/(1+gterm(h)) for l,h in box]; weight=I(min(w.lo for w in weights),min(w.hi for w in weights),True);pen=I(U*U/2)*weight*dist
 return sum((support(a,b,y,o)for(a,b),y,o in zip(box,p,opts)),I(0))-pen

