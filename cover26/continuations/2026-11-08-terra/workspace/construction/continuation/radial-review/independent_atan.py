"""Independent rational certificate of the radial weighted-arc lower bound.
No floating point or third-party libraries. Run with assertions enabled.
"""
from fractions import Fraction as F
from math import isqrt
if not __debug__: raise RuntimeError('Assertions must be enabled')
# Machin formula and alternating series, proving the only pi bounds used below.
def arctan_inverse_interval(q, n=30):
 s=sum((F((-1)**j,(2*j+1)*q**(2*j+1)) for j in range(n)),F(0))
 e=F(1,(2*n+1)*q**(2*n+1))
 return (s,s+e) if n%2==0 else (s-e,s)
a,b=arctan_inverse_interval(5),arctan_inverse_interval(239)
pi_lo,pi_hi=16*a[0]-4*b[1],16*a[1]-4*b[0]
assert F(333,106)<pi_lo<pi_hi<F(355,113)

r=F(11,50)
data=[(F(t),w) for t,w in [('23/100',19665),('19/75',20748),('83/300',24696),('3/10',21748),('97/300',13145),('26/75',11524),('37/100',1683),('59/100',92039),('37/60',67041),('193/300',46430),('67/100',35384),('209/300',23953),('217/300',21024),('3/4',1711),('1',450827)]]
assert all(t>r and t<=1 and w>=0 for t,w in data)
def sqrt_lower(x):
 k=10**10
 return F(isqrt(x.numerator*k*k//x.denominator),k)
def sqrt_upper(x):
 k=10**10
 a=isqrt(x.numerator*k*k//x.denominator)
 return F(a+1,k)
def atan_upper(y):
 # atan y = pi/4 + atan((y-1)/(y+1)); arctan Taylor bounds
 if y<F(1,4): return y-y**3/3+y**5/5
 u=(y-1)/(y+1)
 if u<0:
  a=u-u**3/3+u**5/5-u**7/7
 else:
  a=u-u**3/3+u**5/5-u**7/7+u**9/9
 return F(355,452)+a # pi/4 < 355/452

def bound(t,lo,hi):
 lo=max(lo,t-r); hi=min(hi,t+r)
 if lo>=hi:return F(0)
 def cosangle(d):return (t*t+d*d-r*r)/(2*t*d)
 c=min(cosangle(lo),cosangle(hi))
 v=t*t-r*r
 if lo*lo<=v<=hi*hi: c=min(c,sqrt_lower(v)/t)
 assert 0<c<=1
 y=sqrt_upper(1-c*c)/c
 return atan_upper(y)

step=F(1,2000); count=2440
assert count*step==1+r
maximum=F(0); index=None
for i in range(count):
 score=sum(w*bound(t,i*step,(i+1)*step) for t,w in data)
 if score>maximum: maximum=score;index=i
margin=F(333,106)*sum(w for _,w in data)-26*maximum
assert margin>0
print('PASS: independent rational atan proof, all 2440 closed distance intervals')
print('largest interval index',index)
print('Exact rational checks: weighted maximum < 100301 and margin > 67500')
assert maximum < 100301 and margin > 67500
print('pi sum(weights) - 26 max_score > 0 by exact Fraction arithmetic')
