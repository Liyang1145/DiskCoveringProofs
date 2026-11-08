"""Exact scalar comparisons for the boundary/core reduction, not an n=8 proof."""
from fractions import Fraction as F
def atan_inv_bounds(q,n=30):
    s=sum((F((-1)**j,(2*j+1)*q**(2*j+1)) for j in range(n)),F(0))
    e=F(1,(2*n+1)*q**(2*n+1))
    return s,s+e
a,b=atan_inv_bounds(5),atan_inv_bounds(239)
pi_lower=16*a[0]-4*b[1];pi_upper=16*a[1]-4*b[0]
if not F(333,106)<pi_lower<pi_upper<F(22,7): raise ValueError('Machin bounds')
U=F(234700091,10**9); core=U/(1-2*U)
if not 0<U<F(1,4): raise ValueError('bad threshold')
z=F(333,1378)
if not z-z**3/6>U: raise ValueError('outer arc count')
if not core<F(885,2000): raise ValueError('core threshold')
x=F(333,371)
cos_hi=1-x*x/2+x**4/24
if not cos_hi<(1/F(885,2000)-1)/2: raise ValueError('eight disk theorem comparison')
print('PASS U',U,'core',core,'< 885/2000')
print('PASS boundary lower: sin(pi/13)>',z-z**3/6,'> U')
print('PASS conditional on Fejes Toth: r_D(8)> 885/2000')
R=F(9,40); s=R/(1-2*R)
if not s==F(9,22) or not (1+s)**2<2: raise ValueError('nine disk threshold')
print('PASS conditional on Fejes Toth: core for r<=9/40 is < r_D(9)=sqrt(2)-1')
