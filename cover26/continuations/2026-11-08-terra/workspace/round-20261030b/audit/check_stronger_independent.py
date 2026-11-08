"""Independent rational upper bounds including two-edge deficit, b=14..26.

This checks numerical inequalities, not the geometric reduction or concavity.
"""
from fractions import Fraction as F
from math import isqrt
import argparse

parser=argparse.ArgumentParser()
parser.add_argument('--negative-control',action='store_true')
args=parser.parse_args()

def bounds_atan_inv(q,n=30):
    s=sum((F((-1)**j,(2*j+1)*q**(2*j+1)) for j in range(n)),F(0))
    e=F(1,(2*n+1)*q**(2*n+1))
    return s,s+e
a,b=bounds_atan_inv(5),bounds_atan_inv(239)
pl,pu=16*a[0]-4*b[1],16*a[1]-4*b[0]
low=F(3141592653589793,10**15);high=F(3141592653589794,10**15)
if not low<pl<pu<high:raise ValueError('Machin interval')
if F(1732051,10**6)**2<=3:raise ValueError('sqrt 3 bound')
def sqrt_up(q):
    if q<0:raise ValueError('negative radicand')
    K=10**12
    return F(isqrt(q.numerator*K*K//q.denominator)+1,K)
def sinlo(x):return x-x**3/6+x**5/120-x**7/5040
def sinhi(x):return x-x**3/6+x**5/120
def coslo(x):return 1-x*x/2+x**4/24-x**6/720
r=F(23,100) if args.negative_control else F(228251,1000000)
triangle=3*F(1732051,10**6)*r*r/4
w=F(37,100)
young=1/(2*w)+1/(8*(1/(4*w)-w))
if young!=F(147325,83694) or F(433,250)**2>=3:
    raise ValueError('paired-face rational Young bound')
if F(3,4)*F(433,250)+F(1,2)-young<=F(19,500):
    raise ValueError('paired-face strict deficit')
s3=F(1732051,10**6)
c0=F(1,2);c1=s3/4+F(1,4);c2=-s3/48-F(1,32)
if not c2<0:raise ValueError('quadratic must be concave')
vertex=-c1/(2*c2);two_edge_max=c0-c1*c1/(4*c2)
if not 4<vertex<8 or not (2<two_edge_max):
    raise ValueError('wrong maximum branch')
if F(3,4)*F(433,250)+1-two_edge_max<=F(33,500):
    raise ValueError('two-edge face strict deficit')
rejected=[]
for n in range(14,27):
    xlo,xhi=low/n,high/n
    s0,s1=sinlo(xlo),sinhi(xhi)
    c0=coslo(xhi)
    if not (0<s0<=s1<r and c0>0):raise ValueError('domain')
    area=(50-n)*triangle+n*r*r/2+n*(xhi-s0*c0+s1*sqrt_up(r*r-s0*s0))-F(33,1000)*n*r*r
    gap=low-area
    if gap<=0:rejected.append(n)
    print('b',n,'rational gap approx',float(gap))
if args.negative_control:
    if not rejected:raise ValueError('negative control failed to detect any nonpositive gap')
    print('PASS negative control: r=23/100 cannot be certified for b',rejected)
else:
    if rejected:raise ValueError('nonpositive gap at b='+str(rejected))
    print('PASS Young, quadratic and all 13 exact inequalities; geometry not checked here')
