from fractions import Fraction as F
if not __debug__:raise RuntimeError('Assertions required')
r=F(9,40)
def sinlo(x):return x-x**3/6
def coshi(x):return 1-x*x/2+x**4/24
assert sinlo(F(227,1000))>r
assert coshi(F(39,250))<F(163,165)
assert coshi(F(21,100))<F(91,93)
assert sinlo(F(39,100))>F(3,8)
assert sinlo(F(43,100))>F(9,22)
def atan_interval(q,n=30):
 s=sum((F((-1)**j,(2*j+1)*q**(2*j+1)) for j in range(n)),F(0));return s,s+F(1,(2*n+1)*q**(2*n+1))
a,b=atan_interval(5),atan_interval(239)
pi=F(333,106);assert pi < 16*a[0]-4*b[1]
for B,k in ((15,12),(16,10)):
 assert (k-1)*F(227,1000)+(B-(k-1))*F(39,250)<pi
for J,m in ((3,7),(6,5)):
 assert J*F(21,100)+(m-1)*F(39,100)<pi
assert 7*F(43,100)<pi
print('PASS: B15 => at most 3 boundary discs cover any positive arc on radius 3/5; at least 7 nonboundary discs cover this circle')
print('PASS: B16 => at most 6 boundary discs cover any positive arc on radius 3/5; at least 5 nonboundary discs cover this circle')
print('PASS: core circle needs 8 nonboundary discs; simultaneous-intersection counts >=4 and >=3')
# Exact outer-boundary angular capacity across multiple radial thresholds.
rows=[('4/5','11531/100000',13,12),('13/16','13810/100000',13,11),('33/40','15586/100000',12,10),('67/80','17026/100000',11,8),('17/20','18216/100000',10,6),('7/8','20034/100000',6,0)]
for ds,as_,k15,k16 in rows:
 d,q=F(ds),F(as_); z=(1+d*d-r*r)/(2*d)
 assert (1-r)<=d and d*d<=1-r*r and coshi(q)<z
 for B,k in ((15,k15),(16,k16)):
  if k:
   assert (k-1)*F(227,1000)+(B-k+1)*q<pi
 print('rho',d,'halfwidth <',q,'at least beyond rho B15/B16',k15,k16)
# Integer sample arcs for the six forced-nonboundary middle circles.
from math import acos,asin,ceil
computed=[]
for ds,as_,k15,k16 in rows:
 d=F(ds); t=d-r; db=1-r
 z=(t*t+db*db-r*r)/(2*t*db)
 assert db*db>t*t-r*r and z<=1
 qB=F(ceil(acos(float(z))*10000)+1,10000)
 while coshi(qB)>=z:qB+=F(1,10000)
 qI=F(ceil(asin(float(r/t))*10000)+1,10000)
 while sinlo(qI)<=r/t:qI+=F(1,10000)
 if t+r==1-r:raise RuntimeError('unexpected tangency')
 results=[]
 for B,k in ((15,k15),(16,k16)):
  J=B-k; n=0
  while J*qB+n*qI<pi:n+=1
  assert n==0 or J*qB+(n-1)*qI<pi
  results.append(n)
 computed.append(tuple(results))
 print('t',t,'boundary_max_count',15-k15,16-k16,'alpha<',qB,'inner<',qI,'inner_min',*results)

# Joint origin exclusion plus intersection of middle/core positive-arc sets.
mid15=[8,8,7,6,6];mid16=[7,6,5,4,2]
assert computed[:5]==list(zip(mid15,mid16))
for t, n15,n16 in zip(map(F,['23/40','47/80','3/5','49/80','5/8']),mid15,mid16):
 assert t>2*r and F(11,20)>2*r
 assert n15+8-(11-1)>=0 and n16+8-(10-1)>=0
 print('t',t,'joint B15/B16',n15+8-10,n16+8-9,'implied radial interval',(t-r,F(31,40)))


