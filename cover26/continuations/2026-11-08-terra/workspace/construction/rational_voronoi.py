"""Certify a rational radius for rational centers, using exact restricted Voronoi vertices.
Input JSON: {"radius":"...", "centers":[["x","y"],...]}.
Each decimal string is interpreted exactly as a rational number. Python -O is forbidden.
"""
from fractions import Fraction as Q
from itertools import combinations
import json,sys
if not __debug__: raise RuntimeError('Assertions required')

def sign(a,b=Q(0),d=Q(0)):
    # sign(a+b sqrt(d))
    assert d>=0
    if not b or not d: return (a>0)-(a<0)
    if not a: return (b>0)-(b<0)
    if (a>0)==(b>0): return (a>0)-(a<0)
    t=a*a-b*b*d
    return ((t>0)-(t<0)) * ((a>0)-(a<0))

def vsub(p,q): return p[0]-q[0],p[1]-q[1]
def dot(p,q): return p[0]*q[0]+p[1]*q[1]
def cross(p,q): return p[0]*q[1]-p[1]*q[0]
def circum(a,b,c):
    u=vsub(b,a); v=vsub(c,a); det=2*cross(u,v)
    if not det:return None
    h=dot(b,b)-dot(a,a); k=dot(c,c)-dot(a,a)
    return ((h*v[1]-k*u[1])/det,(u[0]*k-v[0]*h)/det)
def distance_diff(i,j,xa,xb,ya,yb,d):
    # dist(x,i)^2-dist(x,j)^2
    p,q=C[i],C[j]
    da=dot(p,p)-dot(q,q)-2*((p[0]-q[0])*xa+(p[1]-q[1])*ya)
    db=-2*((p[0]-q[0])*xb+(p[1]-q[1])*yb)
    return sign(da,db,d)
def inspect_boundary(xa,xb,ya,yb,d,i):
    if any(distance_diff(i,j,xa,xb,ya,yb,d)>0 for j in range(n)): return False
    p=C[i]; a=1+dot(p,p)-2*(p[0]*xa+p[1]*ya)-R*R
    b=-2*(p[0]*xb+p[1]*yb)
    if sign(a,b,d)>0: raise AssertionError('Uncovered boundary critical point')
    return True

data=json.loads(open(sys.argv[1],encoding='utf-8').read())
C=[tuple(Q(a) for a in p) for p in data['centers']]; R=Q(data['radius']); n=len(C)
assert n>0 and R>=0 and len(set(C))==n
count=0
for i,j,k in combinations(range(n),3):
    p=circum(C[i],C[j],C[k])
    if p is None or dot(p,p)>1: continue
    ds=dot(vsub(p,C[i]),vsub(p,C[i]))
    if any(dot(vsub(p,q),vsub(p,q))<ds for q in C): continue
    if ds>R*R: raise AssertionError('Uncovered interior Voronoi vertex')
    count+=1
boundary=0
# Boundary edge endpoints arise from bisectors intersecting x^2+y^2=1.
for i,j in combinations(range(n),2):
    u=vsub(C[j],C[i]); L=dot(u,u); h=(dot(C[j],C[j])-dot(C[i],C[i]))/2
    D=L-h*h
    if D<0: continue
    xa=h*u[0]/L; ya=h*u[1]/L; xb=-u[1]/L; yb=u[0]/L
    boundary+=inspect_boundary(xa,xb,ya,yb,D,i)
    if D: boundary+=inspect_boundary(xa,-xb,ya,-yb,D,i)
# Arc extrema where derivative of distance along the boundary vanishes.
for i,p in enumerate(C):
    L=dot(p,p)
    if not L: continue
    boundary+=inspect_boundary(0,p[0]/L,0,p[1]/L,L,i)
    boundary+=inspect_boundary(0,-p[0]/L,0,-p[1]/L,L,i)
boundary+=inspect_boundary(Q(1),Q(0),Q(0),Q(0),Q(0),0) if not any(distance_diff(0,j,Q(1),Q(0),Q(0),Q(0),Q(0))>0 for j in range(n)) else 0
# The test point (1,0) must also be checked against its nearest center.
idx=min(range(n),key=lambda j:dot(vsub((Q(1),Q(0)),C[j]),vsub((Q(1),Q(0)),C[j])))
assert inspect_boundary(Q(1),Q(0),Q(0),Q(0),Q(0),idx)
print(f'PASS: {n} rational centers cover unit disk at exact radius {R}')
print(f'Interior active circumcenters: {count}; active boundary candidates: {boundary}')
