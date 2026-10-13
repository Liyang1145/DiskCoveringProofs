"""Independent exact-rational Taylor/isqrt verification. No producer helpers."""
from fractions import Fraction as F
from math import factorial,isqrt
import json
N=50; SCALE=10**30
def add(a,b):return (a[0]+b[0],a[1]+b[1])
def neg(a):return (-a[1],-a[0])
def sub(a,b):return add(a,neg(b))
def mul(a,b):
 q=[x*y for x in a for y in b];return min(q),max(q)
def pt(a):return F(a),F(a)
def sq(a):return (F(0) if a[0]<=0<=a[1] else min(a[0]**2,a[1]**2),max(a[0]**2,a[1]**2))
def div(a,b):
 assert b[0]>0
 return mul(a,(1/b[1],1/b[0]))
def root(a):
 assert a[0]>=0
 out=[]
 for x in a:
  k=isqrt(x.numerator*SCALE*SCALE//x.denominator)
  out.append(k)
 return F(out[0],SCALE),F(out[1]+1,SCALE)
def trig(x,parity):
 s=sum(((-1)**k*x**(2*k+parity)/factorial(2*k+parity) for k in range(N)),F(0))
 err=abs(x)**(2*N+parity)/factorial(2*N+parity)
 assert abs(x)<6
 return s-err,s+err
# alternating arctan tail gives pi, independently of libraries
def atan(x,n):
 s=sum(((-1)**k*x**(2*k+1)/(2*k+1) for k in range(n)),F(0));e=x**(2*n+1)/(2*n+1)
 return s-e,s+e
pi=sub(mul(pt(16),atan(F(1,5),60)),mul(pt(4),atan(F(1,239),20)))
r=F(19,50);r2=r*r
t=[F(322232,10**6),F(389796,10**6),F(347568,10**6)]+[F(38979,10**5)]*6
o=[pt(F(512993,10**6))]+[pt(F(1,10**6))]*7
o.append(sub(pt(2*sum(t)-sum(z[0] for z in o)),mul(pt(2),pi)))
assert all(z[0]>0 for z in o)
private=[sub(pt(2*t[k]),add(o[k-1],o[k])) for k in range(9)]
assert all(z[0]>0 for z in private)
phi=[F(0)]
for k in range(8):phi.append(phi[-1]+t[k]+t[k+1]-o[k][0])
c=[]
for tk,ph in zip(t,phi):
 st=trig(tk,1);ct=trig(tk,0)
 assert st[1]<r
 rho=sub(ct,root(sub(pt(r2),sq(st))))
 c.append((mul(rho,trig(ph,0)),mul(rho,trig(ph,1))))
def vsub(a,b):return sub(a[0],b[0]),sub(a[1],b[1])
def norm2(a):return add(sq(a[0]),sq(a[1]))
def d2(a,b):return norm2(vsub(a,b))
d=vsub(c[1],c[0]);dn=root(norm2(d));assert dn[0]>0 and dn[1]<2*r
h=root(sub(pt(r2),mul(pt(F(1,4)),norm2(d))))
M=tuple(mul(pt(F(1,2)),add(c[0][i],c[1][i])) for i in range(2))
w=div(neg(d[1]),dn),div(d[0],dn)
v=tuple(add(M[i],mul(h,w[i])) for i in range(2))
vother=tuple(sub(M[i],mul(h,w[i])) for i in range(2))
assert norm2(v)[1]<1<norm2(vother)[0]
assert d2(v,c[2])[1]<r2
# Crossing property is an analytic identity of M +- h rot(d)/|d|;
# the interval computation proves its real domain, not equality by zero containment.
P=[(F(201,500),F(179,1000)),(F(-89,250),F(259,1000)),(F(-23,500),F(-219,500))] # revised producer witness; earlier independently checked triple also valid
pointnorm=[sum(x*x for x in p) for p in P];assert all(x<1 for x in pointnorm)
hole_lowers=[min(d2(tuple(pt(x) for x in p),ck)[0] for ck in c) for p in P]
assert all(x>r2 for x in hole_lowers)
pair_dist=[sum((P[i][k]-P[j][k])**2 for k in range(2)) for i in range(3) for j in range(i+1,3)]
assert all(x>4*r2 for x in pair_dist)
def display(z):return [float(z[0]),float(z[1])]
out=dict(status='ALL_EXACT_RATIONAL_ASSERTIONS_PASS',representation='rational Taylor remainders, independent Machin pi, isqrt outward bounds',o8=display(o[-1]),private_min_lower=float(min(z[0] for z in private)),inner_norm2=display(norm2(v)),other_norm2=display(norm2(vother)),third_distance2=display(d2(v,c[2])),hole_norm2=list(map(str,pointnorm)),hole_distance2_lower=list(map(float,hole_lowers)),pair_distance2=list(map(str,pair_dist)),r2=str(r2),floating_outputs='display only; all assertions are exact Fraction comparisons')
print(json.dumps(out,indent=2))
