from fractions import Fraction as Q

# Closed rational intervals, with no floating-point arithmetic in the proof.
def add(x,y): return (x[0]+y[0],x[1]+y[1])
def neg(x): return (-x[1],-x[0])
def sub(x,y): return add(x,neg(y))
def mul(x,y):
    p=[a*b for a in x for b in y]
    return min(p),max(p)
def scale(x,n): return mul(x,(Q(n),Q(n)))
def sq(x):
    assert x[0]>=0
    return x[0]**2,x[1]**2
def arctan_inv(q,N=35):
    terms=[Q((-1)**j,(2*j+1)*q**(2*j+1)) for j in range(N)]
    s=sum(terms,Q(0)); e=Q(1,(2*N+1)*q**(2*N+1))
    return (s-e,s) if N%2 else (s,s+e)
def cosine_point(x,N=18):
    # Sum through exponent 2N; next term bounds remainder on 0 <= x < 1.
    from math import factorial
    s=sum(((-1)**j*x**(2*j)/factorial(2*j) for j in range(N+1)),Q(0))
    e=x**(2*N+2)/factorial(2*N+2)
    return (s-e,s) if N%2==0 else (s,s+e)
def cosine_interval(x):
    assert 0<=x[0]<=x[1]<1
    return cosine_point(x[1])[0],cosine_point(x[0])[1]
def rational(x): return Q(str(x))
def singleton(x): return (x,x)

pi=sub(scale(arctan_inv(5),16),scale(arctan_inv(239),4))
c=cosine_interval(scale(pi,Q(1,9)))
d=cosine_interval(scale(pi,Q(1,16)))
k=sub(scale(sq(c),4),singleton(Q(1)))
assert Q(5,2)<k[0]<k[1]<Q(13,5)

def F(x):
    x=singleton(x)
    return sub(scale(mul(sq(d),add(sq(x),mul(k,x))),4),sq(add(singleton(Q(1)),mul(k,x))))
lo=Q(24722664,100000000); hi=Q(24722665,100000000)
assert F(lo)[1] < 0 and F(hi)[0] > 0
# At x=1/k, F=4*(d^2*(1+1/k^2)-1)>0.
end=sub(mul(sq(d),add(singleton(Q(1)),(1/k[1]**2,1/k[0]**2))),singleton(Q(1)))
assert end[0]>0
# Quadratic coefficient negative; hence strict concavity gives uniqueness on (0,1/k).
A=sub(scale(sq(d),4),sq(k)); assert A[1]<0
# Geometric conditions a>0, b>0, s=kr<1, and b lies between sd and d.
s=mul(k,(lo,hi)); assert s[1]<1
b=( (1+s[0])/(2*d[1]), (1+s[1])/(2*d[0]) )
assert sub(b,mul(s,d))[0]>0 and sub(d,b)[0]>0
print('PASS: exact rational interval certificate')
print('pi bracket via Machin; cosine brackets via Taylor; all arithmetic Fraction')
print('r is unique root in (0,1/k), with 0.24722664 < r < 0.24722665')
print('F(lo)<0, F(hi)>0, F(1/k)>0, quadratic coefficient <0')
print('0<s<1 and s*d<b<d; 26 discs cover the unit disk')
