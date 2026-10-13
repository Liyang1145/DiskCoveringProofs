from fractions import Fraction as F
from math import factorial
import json
from pathlib import Path
R=F(19,50); L=3*R; rho=1-R
coef=(1+rho*rho-L*L)/(2*rho)
assert coef==F(53,775)
x=F(151,100)
# Alternating series through positive x^8 term bounds cosine from above.
upper=sum((-1)**k*x**(2*k)/factorial(2*k) for k in range(5))
assert upper<coef
x=F(39,100)
assert x-x**3/6>R
assert F(151,100)+4*x==F(307,100)<F(31,10)
# pi > 3.1: inscribed regular 12-gon has perimeter/diameter
# 12 sin(pi/12)=3(sqrt(6)-sqrt(2)) > 3.1, or Machin bound below.
def atan_low(x,N):
    assert N%2==0
    return sum((-1)**k*x**(2*k+1)/(2*k+1) for k in range(N))
def atan_up(x,N):
    assert N%2==1
    return sum((-1)**k*x**(2*k+1)/(2*k+1) for k in range(N))
pi_low=16*atan_low(F(1,5),4)-4*atan_up(F(1,239),3)
assert pi_low>F(31,10)
for x,bound in [(F(2,5),R),(F(9,10),2*R)]:
    assert x-x**3/6>bound
out={'status':'exact rational PASS','star_coefficient':str(coef),'cos151_upper_degree8':str(upper),'pi_lower_machin':str(pi_low),'star_halfmeasure_upper':'307/100','two_triple_halfmeasure_upper':'3','scope':'geometric window inequalities, not full covering optimum'}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2))
print(json.dumps(out))
