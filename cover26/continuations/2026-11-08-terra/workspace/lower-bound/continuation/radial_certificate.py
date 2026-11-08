from fractions import Fraction as F
from math import acos, ceil, isqrt
from time import perf_counter
if not __debug__:
    raise RuntimeError("Assertions must be enabled")

# Nonnegative dual weights in units of 1/100000. All sample radii exceed r.
r=F(11,50)
raw=[('23/100',19665),('19/75',20748),('83/300',24696),('3/10',21748),('97/300',13145),('26/75',11524),('37/100',1683),('59/100',92039),('37/60',67041),('193/300',46430),('67/100',35384),('209/300',23953),('217/300',21024),('3/4',1711),('1',450827)]
data=[(F(t),w) for t,w in raw]
assert all(t>r and w>=0 for t,w in data)

def c_endpoint(t,d):
    return (t*t+d*d-r*r)/(2*t*d)

def cosine_upper(q):
    # Taylor degree 12 upper, as 0 <= q <= 2 and terms decrease.
    term=F(1); val=term
    for j in range(1,7):
        term *= -q*q / ((2*j-1)*(2*j))
        val += term
    return val

def root_lower(q):
    k=10**12
    return F(isqrt(q.numerator*k*k//q.denominator),k)

def angle_bound(t,lo,hi):
    lo=max(lo,t-r); hi=min(hi,t+r)
    if lo>=hi:
        return F(0)
    c=min(c_endpoint(t,lo),c_endpoint(t,hi))
    critical=t*t-r*r
    if lo*lo <= critical <= hi*hi:
        c=min(c,root_lower(critical)/t)
    assert 0<=c<=1
    # Float only suggests a grid point; exact cosine inequality is checked.
    k=max(1,ceil(acos(float(c))*10000))
    q=F(k,10000)
    while cosine_upper(q)>c:
        k+=1; q=F(k,10000)
    assert 0<q<2 and cosine_upper(q)<=c
    return q

if __name__=='__main__':
    start=perf_counter(); step=F(1,2000); M=2440
    assert step*M==1+r
    max_score=F(0); maximum_i=-1
    for i in range(M):
        lo=i*step; hi=(i+1)*step
        score=sum(w*angle_bound(t,lo,hi) for t,w in data)
        if score>max_score: max_score=score;maximum_i=i
    pi_lower=F(333,106)
    goal=pi_lower*sum(w for _,w in data)
    margin=goal-26*max_score
    print('intervals',M,'maximum interval',maximum_i)
    print('max_score',max_score, 'pi_weight_lower',goal)
    print('strict margin',margin, 'approx',float(margin))
    print('seconds',round(perf_counter()-start,2))
    assert margin>0
    print('PROVED: no 26 radius-11/50 disks cover the unit disk')
