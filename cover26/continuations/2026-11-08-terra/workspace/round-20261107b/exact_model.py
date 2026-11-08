"""Sparse integer polynomial model, using only the Python standard library."""
N=26
ZERO=(0,)*N

class Poly:
    def __init__(self, terms=0):
        if isinstance(terms,Poly):
            self.terms=terms.terms.copy()
        elif isinstance(terms,int):
            self.terms={} if terms==0 else {ZERO:terms}
        else:
            self.terms={m:int(c) for m,c in terms.items() if c}
    def __add__(self,other):
        out=self.terms.copy()
        for m,c in poly(other).terms.items():out[m]=out.get(m,0)+c
        return Poly(out)
    __radd__=__add__
    def __neg__(self):return Poly({m:-c for m,c in self.terms.items()})
    def __sub__(self,other):return self+-poly(other)
    def __rsub__(self,other):return poly(other)+-self
    def __mul__(self,other):
        out={}
        for a,c in self.terms.items():
            for b,d in poly(other).terms.items():
                m=tuple(x+y for x,y in zip(a,b));out[m]=out.get(m,0)+c*d
        return Poly(out)
    __rmul__=__mul__
    def __pow__(self,n):
        out=Poly(1)
        for _ in range(n):out=out*self
        return out
    def diff(self,i):
        out={}
        for m,c in self.terms.items():
            if m[i]:
                key=list(m);key[i]-=1;out[tuple(key)]=c*m[i]
        return Poly(out)
    def __eq__(self,other):return self.terms==poly(other).terms
    def signature(self):return tuple(sorted(self.terms.items()))

def poly(x):return x if isinstance(x,Poly) else Poly(x)
def variable(i):
    m=[0]*N;m[i]=1
    return Poly({tuple(m):1})
def sub(a,b):return (a[0]-b[0],a[1]-b[1])
def dot(a,b):return a[0]*b[0]+a[1]*b[1]
def cross(a,b):return a[0]*b[1]-a[1]*b[0]
def norm(a):return dot(a,a)

NAMES='x0 x1 y1 x2 y2 x3 y3 y4 p q s t v r'.split()
TRIANGLES=[(16,18,19),(16,19,20),(1,2,19),(16,17,20),
           (3,4,20),(3,19,20),(0,1,18),(1,18,19)]

def circle_triangle(a,b,c,r):
    return 4*r*r*cross(sub(b,a),sub(c,a))**2-norm(sub(b,a))*norm(sub(c,b))*norm(sub(a,c))

def anchor_data(a,b,r):
    hi=1+norm(a)-r*r;hj=1+norm(b)-r*r
    num=(hi*b[1]-hj*a[1],a[0]*hj-b[0]*hi)
    denominator=2*cross(a,b)
    return num,denominator,hi,hj

def boundary(a,b,r):
    num,den,_,_=anchor_data(a,b,r)
    return norm(num)-den*den

def build():
    Z=[variable(i) for i in range(N)]
    x0,x1,y1,x2,y2,x3,y3,y4,p,q,s,t,v,r=Z[:14]
    z=Poly(0)
    C=[(x0,z),(x1,y1),(x2,y2),(x3,y3),(z,y4),(-x3,y3),(-x2,y2),(-x1,y1)]
    C.extend([(-a,-b) for a,b in C.copy()])
    C.extend([(p,z),(-p,z),(q,z),(s,t),(z,v),(-s,t),(-q,z),(-s,-t),(z,-v),(s,-t)])
    G=[circle_triangle(C[i],C[j],C[k],r) for i,j,k in TRIANGLES]
    G.extend(boundary(C[i],C[i+1],r) for i in range(4))
    F=G+[sum((Z[14+k]*G[k].diff(i) for k in range(12)),Poly(0))-(1 if i==13 else 0)
         for i in range(14)]
    return C,G,F
