"""Exact scalar checks for common positive-arc contributors at r=9/40."""
from fractions import Fraction as F
def require(value,message):
    if not value:raise ValueError(message)
def sinlo(x): return x-x**3/6
def coshi(x): return 1-x*x/2+x**4/24
r=F(9,40); d=F(33,40); t=F(3,5); pi_lo=F(333,106)
require(d*d<1-r*r,'outer distance monotonicity interval')
require(sinlo(F(227,1000))>r,'global boundary arc')
z=(1+d*d-r*r)/(2*d)
require(coshi(F(39,250))<z,'near boundary arc')
z=(t*t+(1-r)**2-r*r)/(2*t*(1-r))
require((1-r)**2>t*t-r*r and coshi(F(21,100))<z,'inner circle boundary arc')
require(sinlo(F(39,100))>F(3,8),'inner circle generic arc')
require(sinlo(F(43,100))>F(9,22),'core circle generic arc')
for B,far in ((15,12),(16,10)):
    require((far-1)*F(227,1000)+(B-far+1)*F(39,250)<pi_lo,'boundary count')
for near,interior in ((3,7),(6,5)):
    require(near*F(21,100)+(interior-1)*F(39,100)<pi_lo,'inner circle count')
require(7*F(43,100)<pi_lo,'core circle count')
require(2*r<F(11,20) and F(11,20)<t,'origin disk misses both circles')
print('PASS B15/B16 common nonboundary positive-arc contributors >= 5 / 4')
