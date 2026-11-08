"""Propose an exact polynomial system for the D2 candidate; numerical only."""
from pathlib import Path
import json
import numpy as np
import sympy as sp
from scipy.optimize import root

HERE=Path(__file__).resolve().parent
data=json.loads((HERE/'numerical_contacts.json').read_text())
seed=data['rotated_centers']
names='x0 x1 y1 x2 y2 x3 y3 y4 p q s t v r'
X=sp.symbols(names)
x0,x1,y1,x2,y2,x3,y3,y4,p,q,s,t,v,r=X
C={0:sp.Matrix([x0,0]),1:sp.Matrix([x1,y1]),2:sp.Matrix([x2,y2]),
   3:sp.Matrix([x3,y3]),4:sp.Matrix([0,y4]),16:sp.Matrix([p,0]),
   17:sp.Matrix([-p,0]),18:sp.Matrix([q,0]),19:sp.Matrix([s,t]),20:sp.Matrix([0,v])}
def cross(a,b):return a[0]*b[1]-a[1]*b[0]
def norm(a):return a.dot(a)
def triangle(i,j,k):
    a,b,c=C[i],C[j],C[k]
    return 4*r*r*cross(b-a,c-a)**2-norm(b-a)*norm(c-b)*norm(a-c)
def boundary(i,j):
    a,b=C[i],C[j]
    h=1+norm(a)-r*r;k=1+norm(b)-r*r
    return (h*b[1]-k*a[1])**2+(a[0]*k-b[0]*h)**2-4*cross(a,b)**2
triangles=[(16,18,19),(16,19,20),(1,2,19),(16,17,20),
           (3,4,20),(3,19,20),(0,1,18),(1,18,19)]
G=sp.Matrix([triangle(*tri) for tri in triangles]+[boundary(i,i+1) for i in range(4)])
J=G.jacobian(X)
gfun=sp.lambdify([X],G,'numpy',cse=True)
jfun=sp.lambdify([X],J,'numpy',cse=True)
guess=np.array([seed[0][0],*seed[1],*seed[2],*seed[3],seed[4][1],
                seed[16][0],seed[18][0],*seed[19],seed[20][1],data['radius']])
JJ=np.array(jfun(guess),dtype=float)
u,singular,vh=np.linalg.svd(JJ)
e=np.zeros(14);e[-1]=1
lam=np.linalg.lstsq(JJ.T,e,rcond=None)[0]
print('constraint singular values',singular,flush=True)
print('r derivative along tangent directions',vh[-2:]@e,flush=True)
print('initial multipliers',lam,flush=True)
def equations(z):
    x,l=z[:14],z[14:]
    return np.concatenate([np.array(gfun(x)).ravel(),np.array(jfun(x)).T@l-e])
ans=root(equations,np.concatenate([guess,lam]),tol=1e-11)
print('stationary root',ans.success,ans.message,'residual',max(abs(equations(ans.x))),flush=True)
print(dict(zip(names.split(),ans.x[:14])),flush=True)
print('multipliers',ans.x[14:],flush=True)
out={'variables':names.split(),'coordinates':ans.x[:14].tolist(),'multipliers':ans.x[14:].tolist(),
     'residual':float(max(abs(equations(ans.x)))),'success':bool(ans.success),
     'triangles':triangles,'polynomials':[str(z) for z in G]}
(HERE/'stationary-proposal.json').write_text(json.dumps(out,indent=2))
