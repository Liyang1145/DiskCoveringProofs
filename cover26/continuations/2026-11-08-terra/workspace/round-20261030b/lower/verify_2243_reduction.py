from fractions import Fraction as F
if not __debug__:raise RuntimeError('Assertions must be enabled')
r=F(2243,10000);x=F(333,106*13);y=F(333,106*7)
assert x-x**3/6>r
assert r/(1-2*r)<y-y**3/6
assert r<F(1,2)
print('PASS: B>=14, at least 9 non-boundary disks, hence B<=17.')
