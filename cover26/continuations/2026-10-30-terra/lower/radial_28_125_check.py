from fractions import Fraction as F
from math import acos,ceil,isqrt
from pathlib import Path
import json,time
if not __debug__:raise RuntimeError('Assertions must be enabled')
proposal=json.loads((Path(__file__).parent/'radial_28_125_proposal.json').read_text(encoding='utf8'))
r=F(proposal['radius']);data=[(F(t),w) for t,w in proposal['data']]
assert r==F(28,125) and all(r<t<=1 and isinstance(w,int) and w>=0 for t,w in data)
# sin(pi/13) > x-x^3/6 > r for x=(333/106)/13.
x=F(333,106*13)
assert x-x**3/6>r and r<F(1,2)
def cos_up(q):
 term=F(1);val=term
 for j in range(1,7):
  term*=-q*q/((2*j-1)*(2*j));val+=term
 return val
def sqrt_low(v):
 k=10**12
 return F(isqrt(v.numerator*k*k//v.denominator),k)
def arc_upper(t,lo,hi):
 lo=max(lo,t-r);hi=min(hi,t+r)
 if lo>=hi:return F(0)
 def c(d):return (t*t+d*d-r*r)/(2*t*d)
 v=t*t-r*r
 lower=min(c(lo),c(hi))
 if lo*lo<=v<=hi*hi: lower=min(lower,sqrt_low(v)/t)
 assert 0<=lower<=1
 k=max(1,ceil(acos(float(lower))*1000000)); q=F(k,1000000)
 while cos_up(q)>lower:
  k+=1;q=F(k,1000000)
 assert q<2 and cos_up(q)<=lower
 return q
step=F(1,20000); count=24480
assert count*step==1+r and r/step==4480 and (1-r)/step==15520
start=time.monotonic(); maxima=[F(0),F(0),F(0)];indexes=[None,None,None]
for i in range(count):
 lo=i*step;hi=(i+1)*step
 val=sum(w*arc_upper(t,lo,hi) for t,w in data)
 g=0 if hi<=r else 2 if lo>=1-r else 1
 if val>maxima[g]:maxima[g]=val;indexes[g]=i
sum_w=sum(w for t,w in data); m=max(maxima)
margin=F(333,106)*sum_w-maxima[0]-14*maxima[2]-11*m
print('group maxima',*[str(x) for x in maxima]);print('argmax bins',indexes)
print('margin',str(margin),'~',float(margin),'seconds',time.monotonic()-start)
assert margin>0
print('PROVED: r_D(26)>28/125')
