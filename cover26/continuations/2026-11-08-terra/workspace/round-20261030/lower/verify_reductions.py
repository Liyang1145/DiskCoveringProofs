from fractions import Fraction as F
if not __debug__:raise RuntimeError('Assertions must be enabled')
r=F(9,40)
x=F(333,106*13)
y=F(333,106*7)
assert x-x**3/6>r
assert y-y**3/6>F(9,22)
assert r/(1-2*r)==F(9,22)
print('All rational boundary and inner-core thresholds passed.')
