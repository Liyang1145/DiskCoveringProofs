from fractions import Fraction as F
from math import acos,floor
from pathlib import Path
import json
if not __debug__:raise RuntimeError('Assertions must be enabled')
d=json.loads((Path(__file__).parent/'radial_relax_all_B16.json').read_text(encoding='utf8'))
r=F(d['r']);B=d['B'];T=[F(v) for v in d['circles']];D=[(F(x),int(n)) for x,n in d['radii_counts']]
assert r==F(9,40) and B==16 and sum(n for _,n in D)==26 and all(t>r for t in T)
def count(pred):return sum(n for x,n in D if pred(x))
assert count(lambda x:x<=r)>=1
assert count(lambda x:1-r<=x<=1+r)==B
caps=[(F(113,250),3),(F(97,200),4),(F(109,200),5),(F(61,100),6),(F(169,250),8),(F(737,1000),9),(F(77,100),10),(F(159,200),11)]
for t,k in caps:assert count(lambda x:x<=t)>=k
far=[(F(4,5),12),(F(13,16),11),(F(33,40),10),(F(67,80),8),(F(17,20),6)]
for t,k in far:assert count(lambda x:x>t)>=k
inner=[(F(11,20),8),(F(23,40),7),(F(47,80),6),(F(3,5),5),(F(49,80),4),(F(5,8),2)]
for t,k in inner:assert count(lambda x:t-r<x<1-r)>=k
assert count(lambda x:F(3,8)<x<F(31,40))>=4
def cos_lower(q):
 term=F(1);s=term
 for j in range(1,8):term*=-q*q/((2*j-1)*(2*j));s+=term
 return s
def angle_lower(t,x):
 if x==0 or abs(t-x)>=r:return F(0)
 c=(t*t+x*x-r*r)/(2*t*x);assert 0<c<=1
 k=max(0,floor(acos(float(c))*10**6));q=F(k,10**6)
 while cos_lower(q)<c:
  k-=1;assert k>=0;q=F(k,10**6)
 assert q<2 and cos_lower(q)>=c
 return q
minimum=None
for t in T:
 score=sum(n*angle_lower(t,x) for x,n in D)
 gap=score-F(355,113)
 assert gap>0
 minimum=gap if minimum is None else min(gap,minimum)
print('PASS B16 radial relaxation: integer 26, all nested and six outer counts, 15 concentric angular inequalities')
print('minimum angular excess >',minimum,'=',float(minimum))
print('NOT a planar covering: azimuthal correlations are omitted, and other concentric radii are unverified.')
