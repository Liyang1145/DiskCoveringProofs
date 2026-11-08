"""Polynomial definition of a D2-symmetric candidate, unrelated to old hashes."""
import sympy as sp

NAMES='x0 x1 y1 x2 y2 x3 y3 y4 p q s t v r'.split()
TRIANGLES=[(16,18,19),(16,19,20),(1,2,19),(16,17,20),
           (3,4,20),(3,19,20),(0,1,18),(1,18,19)]

def build():
    X=sp.symbols(' '.join(NAMES));L=sp.symbols('l0:12')
    x0,x1,y1,x2,y2,x3,y3,y4,p,q,s,t,v,r=X
    C={0:sp.Matrix([x0,0]),1:sp.Matrix([x1,y1]),2:sp.Matrix([x2,y2]),
       3:sp.Matrix([x3,y3]),4:sp.Matrix([0,y4]),16:sp.Matrix([p,0]),
       17:sp.Matrix([-p,0]),18:sp.Matrix([q,0]),19:sp.Matrix([s,t]),20:sp.Matrix([0,v])}
    cross=lambda a,b:a[0]*b[1]-a[1]*b[0]
    norm=lambda a:a.dot(a)
    G=[]
    for i,j,k in TRIANGLES:
        a,b,c=C[i],C[j],C[k]
        G.append(4*r*r*cross(b-a,c-a)**2-norm(b-a)*norm(c-b)*norm(a-c))
    for i in range(4):
        a,b=C[i],C[i+1];h=1+norm(a)-r*r;k=1+norm(b)-r*r
        G.append((h*b[1]-k*a[1])**2+(a[0]*k-b[0]*h)**2-4*cross(a,b)**2)
    G=sp.Matrix(G);J=G.jacobian(X)
    F=list(G)+[sum(L[k]*J[k,i] for k in range(12))-(1 if i==13 else 0) for i in range(14)]
    return X+L,sp.Matrix(F)
