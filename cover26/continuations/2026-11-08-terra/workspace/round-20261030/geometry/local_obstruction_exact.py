from fractions import Fraction as F
from lens_polygon import coslo,coshi,sinlo,sinhi,U
if not __debug__: raise RuntimeError('Assertions required')
def atan_inv(q,n=30):
 s=sum((F((-1)**j,(2*j+1)*q**(2*j+1)) for j in range(n)),F(0)); return s,s+F(1,(2*n+1)*q**(2*n+1))
a,b=atan_inv(5),atan_inv(239)
assert F(3141592653589793,10**15)<16*a[0]-4*b[1]<16*a[1]-4*b[0]<F(3141592653589794,10**15)
assert F(1732,1000)**2<3
v=(-F(121,1000),-F(401,2000));w=(v[0],-v[1]); L=F(3141592653589793,14*10**15);H=F(3141592653589794,14*10**15)
ax=(coslo(2*H)-1,coshi(2*L)-1);ay=(-sinhi(2*H),-sinlo(2*L))
def norm2(x,y):return x*x+y*y
assert norm2(*v)<U*U and norm2(1+v[0],v[1])<1
assert all(norm2(v[0]-x,v[1]-y)<U*U for x in ax for y in ay)
x=abs(v[0]*w[1]-v[1]*w[0]); assert 14*x>F(4573,10000)
print('PASS exact independent lenses witness: X=',x,'; 14 X > 4573/10000')
print('Witness is local only: no claimed global sharing of centres')
slo=L-L**3/6+L**5/120-L**7/5040;shi=H-H**3/6+H**5/120;clo=1-H**2/2+H**4/24-H**6/720;chi=1-L**2/2+L**4/24;hlo=F(746,10000)
assert hlo*hlo<U*U-shi*shi
surplus=36*3*F(1732,1000)*U*U/4+14*slo*hlo-14*shi*chi+7*x
assert surplus>F(1,10)
print('Even independent-area upper relaxation has surplus > 1/10, so this route cannot exclude B=14 without coupling')


