from fractions import Fraction as F
from math import sqrt

# sin(x) >= x-x^3/6, cos(x) >= 1-x^2/2 for x >= 0.
a=F(1,10)
sin_lower=a-a**3/6
assert sin_lower**2 > F(99,10000)
assert F(99,10000)/F(2,5)-F(1,200) > F(19,1000)
assert F(1,4)-F(1,4)**3/6 > F(1,5)
assert 3*F(1,4)+23*F(1,10) == F(61,20)
# Archimedean bounds 223/71 < pi < 22/7; 223/71 > 61/20.
assert F(223,71)>F(61,20)
loss=4*F(19,1000)**2/2
assert loss == F(722,1000000)
squared=(1+loss*F(7,22))/26
assert squared == (1+F(2527,11000000))/26
assert squared > F(19613866,100000000)**2
print('Exact squared lower bound:', squared)
print('Informational approximate lower bound:', sqrt(float(squared)))
print('All rational proof checks passed.')

# Exact rational verification of the stronger nested-boundary result.
pi_low,pi_high=F(333,106),F(22,7)
x=pi_low/9
y=pi_high/9
sin9_low=x-x**3/6+x**5/120-x**7/5040
sin9_high=y-y**3/6+y**5/120
assert sin9_low>F(34201,100000)
assert sin9_high<F(343,1000)
z=pi_low/15
sin15_low=z-z**3/6
assert sin15_low>F(207,1000)
lower=F(34201,100000)/(1+2*F(34201,100000))
upper=F(343,1000)/(1+2*F(343,1000))
assert lower>F(203091,1000000)
assert upper<F(204,1000)<F(207,1000)<sin15_low
print('Nested-boundary lower bound >', lower, '> 0.203091')
print('Taylor and threshold checks passed.')
