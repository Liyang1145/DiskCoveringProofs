"""Rational verification of forced boundary-center norm counts for B=14."""
from fractions import Fraction as F
if not __debug__:raise RuntimeError('Assertions must be enabled')
u=F(234700091,10**9);pi_lower=F(333,106)
assert (1-u*u)**3>F(81,100)
a_upper=u+F(5,27)*u**3
assert 13*a_upper<pi_lower
rows=[(14,F(59,1000),F(77,100)),(13,F(148,1000),F(4,5)),(12,F(177,1000),F(41,50)),(11,F(192,1000),F(21,25)),(10,F(201,1000),F(17,20))]
for k,t,norm in rows:
 assert t*(15-k)<pi_lower-(k-1)*a_upper
 cos_lower=1-t*t/2
 sin_lower=t-t**3/6
 assert cos_lower>norm and u>sin_lower>0
 assert (cos_lower-norm)**2>u*u-sin_lower**2
 print('at least',k,'centers satisfy |c| >',norm,'via half-angle >',t)
print('All exact rational strict inequalities passed.')
