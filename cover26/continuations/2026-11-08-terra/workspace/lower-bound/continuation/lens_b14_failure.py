"""Exact rational check: n21 lens sufficient conditions fail for n26 B14 at U."""
from fractions import Fraction as F
if not __debug__: raise RuntimeError('Assertions must be enabled')
u=F(234700091,10**9)
pi_lo=F(333,106); pi_hi=F(22,7)
# atan/asin bounds: asin u <= u + 5u^3/27, asin u >= u.
assert (1-u*u)**3>F(81,100)
asin_upper=u+F(5,27)*u**3
assert 13*asin_upper<pi_lo
assert pi_hi-13*u<F(1,10)
assert 2*(pi_hi-13*u)<u
# Thus 0<delta0=pi-13 asin u<1/10, 2sin(delta0)-u<0.
# Crude exact enclosures for sin(pi/14), sqrt(u^2-sin^2), sqrt(3), cos(2 delta0).
theta_lo=pi_lo/14; theta_hi=pi_hi/14
assert theta_lo-theta_lo**3/6>F(222,1000)
assert theta_hi<F(225,1000)
assert u*u-F(225,1000)**2>F(66,1000)**2
assert F(1732,1000)**2<3
# cos(2 delta0) > 1 - 2(1/10)^2 = 98/100.
right_lower=36*F(3,4)*F(1732,1000)*u*u+14*F(66,1000)*(F(222,1000)+u*F(98,100))
left_upper=14*F(225,1000)*(1-u*u)
assert right_lower>left_upper
print('Lens prerequisite 2 sin(delta0)-U < 0, exact bound:',2*(pi_hi-13*u)-u)
print('RHS minus LHS >',right_lower-left_upper,'=',float(right_lower-left_upper))
print('Only proves failure of this sufficient exclusion criterion; says nothing about B14 realizability.')
