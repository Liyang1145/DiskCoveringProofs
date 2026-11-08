"""B=14 lens/area necessary conditions, all acceptance is rational arithmetic."""
from fractions import Fraction as F
from itertools import product
import lens_polygon as lens
if not __debug__:raise RuntimeError('Assertions required')
U=F(234700091,10**9)
def arctan_inv(q,n=30):
 s=sum((F((-1)**j,(2*j+1)*q**(2*j+1)) for j in range(n)),F(0));e=F(1,(2*n+1)*q**(2*n+1));return s,s+e
a,b=arctan_inv(5),arctan_inv(239)
pl,pu=16*a[0]-4*b[1],16*a[1]-4*b[0]
assert F(3141592653589793,10**15)<pl<pu<F(3141592653589794,10**15)
lo=F(3141592653589793,14*10**15);hi=F(3141592653589794,14*10**15)
slo=lo-lo**3/6+lo**5/120-lo**7/5040
shi=hi-hi**3/6+hi**5/120
clo=1-hi**2/2+hi**4/24-hi**6/720
H=F(7463,100000);sqrt3hi=F(1732051,1000000)
assert 0<slo<shi<1 and 0<clo<1
assert H*H>U*U-slo*slo and sqrt3hi*sqrt3hi>3
S=2*(14*slo*clo-14*shi*H-36*3*sqrt3hi*U*U/4)
assert S>F(4573,10000)
assert 5*U*U+F(9,50)<F(4573,10000)
assert U*U+13*F(3,100)<F(4573,10000)
# Full-domain admissible half-angle interval.
A=F(237,1000);assert A-A**3/6>U
assert F(333,106)-13*A>F(3,50)
# 64 exact rational points on unit circle, supporting each of both disks.
directions=set()
for k in range(17):
 t=F(k,16); x=(1-t*t)/(1+t*t); y=2*t/(1+t*t)
 for sx,sy in product((-1,1),repeat=2): directions.add((sx*x,sy*y))
assert len(directions)==64 and all(x*x+y*y==1 for x,y in directions)
lens.D=sorted(directions)
q=lens.bound(F(2368,10000),A,F(2368,10000),A)
assert q<F(3,100)
q2=lens.bound(F(234,1000),A,F(234,1000),A)
assert q2<F(391,10000)
print('PASS: all exact; B=14 implies total cross > 4573/10000')
print('At least 6 cross > 1/50; at least 2 cross > 3/100')
print('For both adjacent half-gaps >= 0.2368, cross < 3/100')
print('For both adjacent half-gaps >= 0.234, cross < 0.0391')
print('No whole-branch exclusion claimed')
