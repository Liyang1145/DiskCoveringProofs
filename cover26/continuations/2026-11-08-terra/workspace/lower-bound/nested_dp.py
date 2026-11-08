"""Certified finite nested-boundary DP; all proof arithmetic is rational."""
from fractions import Fraction as F
from math import isqrt
N=26
scale=10**12
pi_lower=F(333,106)

def sin_lower(x):
    # 0<=x<=pi/2; alternating Taylor remainder.
    return x-x**3/6+x**5/120-x**7/5040

def area_lower(n):
    return F(isqrt(scale*scale//n),scale)

def threshold(b):
    return sin_lower(pi_lower/(b-1))

bounds=[None]*(N+1)
witness=[None]*(N+1)
rows=[]
for n in range(1,N+1):
    best=area_lower(n)
    chosen=('area',)
    for b in range(3,n+1):
        inner=F(1,2) if n==b else bounds[n-b]/(1+2*bounds[n-b])
        value=min(threshold(b),inner)
        if n==N: rows.append((b,float(threshold(b)),float(inner),float(value)))
        if value>best:
            best=value
            chosen=('boundary',b,n-b)
    bounds[n]=best
    witness[n]=chosen
print('b  circle threshold  inner-core threshold  certified minimum')
for row in rows:
    print('%2d %.12f %.12f %.12f'%row)
print('n=26 certified rational lower =',bounds[N])
print('n=26 certified decimal lower = %.12f'%float(bounds[N]))
print('n=26 witness =',witness[N])
n=10
print('n=10 witness =',witness[n], 'value = %.12f'%float(bounds[n]))
assert witness[26]==('boundary',16,10)
assert witness[10]==('boundary',10,0)
assert bounds[26]>F(203091,10**6)

# Interval enclosure of the idealized DP with exact sine and area seeds.
# Archimedes/Milü bounds: 333/106 < pi < 355/113.
pi_upper=F(355,113)
def sin_upper(b):
    if b==3:
        return F(1)
    x=pi_upper/(b-1)
    return x-x**3/6+x**5/120

def area_upper(n):
    return F(isqrt(scale*scale//n)+1,scale)
upper_bounds=[None]*(N+1)
upper_candidates={}
for n in range(1,N+1):
    best=area_upper(n)
    for b in range(3,n+1):
        inner=F(1,2) if n==b else upper_bounds[n-b]/(1+2*upper_bounds[n-b])
        value=min(sin_upper(b),inner)
        if n==N: upper_candidates[b]=value
        best=max(best,value)
    upper_bounds[n]=best
assert upper_bounds[N]<F(203096,10**6)
assert max(v for b,v in upper_candidates.items() if b!=16)<bounds[N]
print('Ideal DP optimum is uniquely b=16 and lies strictly in')
print('  %.12f < optimum < %.12f'%(float(bounds[N]),float(upper_bounds[N])))
# Prove the upper DP for n=10 chooses b=10, too.
competitors=[area_upper(10)]
for b in range(3,10):
    inner=upper_bounds[10-b]/(1+2*upper_bounds[10-b])
    competitors.append(min(sin_upper(b),inner))
assert max(competitors)<bounds[10]
assert sin_upper(16)>upper_bounds[10]/(1+2*upper_bounds[10])
print('Ideal optimum = sin(pi/9)/(1 + 2 sin(pi/9)); no improvement within this DP.')
