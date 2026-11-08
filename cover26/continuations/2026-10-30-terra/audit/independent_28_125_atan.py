"""Independent exact atan replay of the proposed three-class radial bound."""
from fractions import Fraction as F
from functools import lru_cache
from math import isqrt
from pathlib import Path
import json, time
if not __debug__: raise RuntimeError('Assertions must be enabled')

def atan_inverse_bounds(q,n=30):
    s=sum((F((-1)**j,(2*j+1)*q**(2*j+1)) for j in range(n)),F(0))
    e=F(1,(2*n+1)*q**(2*n+1))
    return (s,s+e) if n%2==0 else (s-e,s)
a,b=atan_inverse_bounds(5),atan_inverse_bounds(239)
pi_lo,pi_hi=16*a[0]-4*b[1],16*a[1]-4*b[0]
pi_l=F(3141592653589793,10**15); pi_u=F(3141592653589794,10**15)
assert F(333,106)<pi_l<pi_lo<pi_hi<pi_u<F(355,113)
r=F(28,125)
x=F(333,106*13)
assert x-x**3/6>r and 0<r<F(1,2)
proposal=json.loads((Path(__file__).resolve().parents[1]/'lower/radial_28_125_proposal.json').read_text(encoding='utf8'))
assert F(proposal['radius'])==r
data=[(F(t),w) for t,w in proposal['data']]
assert len(data)==56 and all(r<t<=1 and type(w) is int and w>0 for t,w in data)

def floor_sqrt(q,scale=10**10):
    return F(isqrt(q.numerator*scale**2//q.denominator),scale)
def ceil_sqrt(q,scale=10**10):
    return F(isqrt(q.numerator*scale**2//q.denominator)+1,scale)
def atan_upper(y):
    def atan_small(z,upper):
        # 0 <= z <= 1, reduction gives -3/5 <= u <= 0.
        if z<F(1,4):
            return z-z**3/3+(z**5/5 if upper else 0)
        u=(z-1)/(z+1)
        n=10 if upper else 11
        series=sum(((-1)**j*u**(2*j+1)/ (2*j+1) for j in range(n)),F(0))
        return (pi_u if upper else pi_l)/4+series
    if y<=1: return atan_small(y,True)
    return pi_u/2-atan_small(1/y,False)

@lru_cache(None)
def angle_from_cos_grid(k):
    c=F(k,100000)
    if c==0:
        bound=pi_u/2
    else:
        bound=atan_upper(ceil_sqrt(1-c*c)/c)
    # Round upward, keeping the weighted score's denominator small.
    return (bound.numerator*10**6+bound.denominator-1)//bound.denominator

def angle_integer_bound(t,lo,hi):
    lo=max(lo,t-r);hi=min(hi,t+r)
    if lo>=hi: return 0
    def c(d):return (t*t+d*d-r*r)/(2*t*d)
    val=min(c(lo),c(hi)); v=t*t-r*r
    if lo*lo<=v<=hi*hi: val=min(val,floor_sqrt(v)/t)
    assert 0<=val<=1
    k=(val.numerator*100000)//val.denominator
    return angle_from_cos_grid(k)

step=F(1,20000);count=24480
assert count*step==1+r and r/step==4480 and (1-r)/step==15520
maxscore=[0,0,0];imax=[None,None,None]
start=time.monotonic()
for i in range(count):
    lo=i*step;hi=(i+1)*step
    score=sum(w*angle_integer_bound(t,lo,hi) for t,w in data)
    group=0 if hi<=r else 2 if lo>=1-r else 1
    if score>maxscore[group]:maxscore[group]=score;imax[group]=i
    if i and i%5000==0:print('finished cells',i,'seconds',round(time.monotonic()-start,1),flush=True)
W=sum(w for t,w in data)
m=F(333,106)*W-F(maxscore[0]+14*maxscore[2]+11*max(maxscore),10**6)
print('weights sum',W,'scaled group maxima',maxscore,'argmax',imax)
print('gap',m,'decimal',float(m),'cells',count,'cache',angle_from_cos_grid.cache_info())
assert m>0
print('PASS: independent atan certificate, radius 28/125 impossible')
