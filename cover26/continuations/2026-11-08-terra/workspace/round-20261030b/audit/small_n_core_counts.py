"""Exact arithmetic for nested-core necessary counts, r=9/40.

The k=8,9,10 entries use Fejes Toth's published low-order theorem;
this script checks the numerical comparisons, not that theorem's proof.
"""
from fractions import Fraction as F

def require(flag, message):
    if not flag: raise ValueError(message)

def atan_inv_bounds(q,n=30):
    s=sum((F((-1)**j,(2*j+1)*q**(2*j+1)) for j in range(n)),F(0))
    e=F(1,(2*n+1)*q**(2*n+1))
    return s,s+e

a,b=atan_inv_bounds(5),atan_inv_bounds(239)
pi_lo=16*a[0]-4*b[1]; pi_hi=16*a[1]-4*b[0]
require(F(333,106)<pi_lo<pi_hi<F(22,7),'pi bounds')
r=F(9,40)
data=[('113/250','227/1000',3),('97/200','13/50',4),
      ('109/200','8/25',5),('61/100','77/200',6),
      ('169/250','451/1000',8),('737/1000','64/125',9),
      ('77/100','109/200',10),('159/200','57/100',11)]
for q,t,k in data:
    require(F(q)==F(t)+r and F(t)>r, 'invalid core or threshold')
require(r/F(227,1000)<1,'n2')
require(4*(r/F(13,50))**2<3,'n3')
require(2*(r/F(8,25))**2<1,'n4')
# sin(pi/5)^2=(5-sqrt(5))/8 > 11/32, since sqrt(5)<9/4.
require(F(5)<F(9,4)**2 and (r/F(77,200))**2<F(11,32),'n5')
require(r/F(451,1000)<F(1,2),'n7')
# r8>885/2000 from the published exact formula and rational cos upper bound.
x=F(333,371); cos_upper=1-x*x/2+x**4/24
require(r/F(64,125)<F(885,2000) and cos_upper<(1/F(885,2000)-1)/2,'n8')
# Published r9=sqrt(2)-1.
require((1+r/F(109,200))**2<2,'n9')
# Published r10=1/(1+2 cos(2pi/9)); cosine Taylor upper bound.
x=F(333,477); cos_upper=1-x*x/2+x**4/24
require(r/F(57,100)==F(15,38) and cos_upper<F(23,30),'n10')
for q,t,k in data: print('q=',q,'t=',t,'at least',k,'centers')
print('PASS exact comparisons; low-n theorem scope recorded in CORE-COUNTS.md')
