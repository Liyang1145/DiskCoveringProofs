#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
"""Read-only exact checker of existence and attainment for the n=13 candidate."""
from collections import Counter
from fractions import Fraction as F
from hashlib import sha256
from pathlib import Path
import json
from decimal import Decimal as D, localcontext
import sys

DIGEST = "00bd9e1b2ea0364ea586efe8c92b77f89f5f3664335cccc2b2a4b7b5433478e1"
N, G, T = 119, 62, 62
ACTIVE = [(0,10,12),(1,2,10),(3,4,11),(3,10,11),(4,5,11),
          (5,6,11),(6,7,11),(7,11,12),(8,9,12)]
INACTIVE = [(0,1,10),(0,9,12),(2,3,10),(7,8,12),(10,11,12)]


def require(p, reason):
    if not p:
        raise ValueError(reason)


def add(p, m, a):
    p[m] = p.get(m, 0) + a


def square_difference(p, u, v, coordinate):
    def term(node):
        return (2*(node-1)+coordinate,) if node else ()
    for i, a in ((u, 1), (v, -1)):
        for j, b in ((u, 1), (v, -1)):
            if (i or coordinate == 0) and (j or coordinate == 0):
                add(p, tuple(sorted(term(i)+term(j))), a*b)


def equations():
    edges = [(i, 10+(i+k)%10) for i in range(10) for k in range(2)]
    edges += [(23+j,10+i) for j, face in enumerate(ACTIVE) for i in face]
    constraints = []
    for u,v in edges:
        p = {(T,): -1}
        for k in range(2):
            square_difference(p, u, v, k)
        constraints.append(p)
    for node in range(1,10):
        i = 2*(node-1)
        constraints.append({(): -1,(i,i):1,(i+1,i+1):1})
    stationary = [{} for _ in range(G+1)]
    stationary[T][()] = 1
    for i,p in enumerate(constraints):
        for monomial,a in p.items():
            for j,k in enumerate(monomial):
                add(stationary[k], monomial[:j]+monomial[j+1:]+(G+1+i,), a)
    return constraints + stationary


def approximate_inverse(jac, q):
    """Compute a candidate inverse; only subsequent integer tests are trusted."""
    yq = 10**48
    with localcontext() as oc:
        oc.prec = 62
        M = [[D(row.get(j,0))/q for j in range(N)] +
             [D(i==j) for j in range(N)] for i,row in enumerate(jac)]
        for k in range(N):
            pivot = max(range(k,N),key=lambda i:abs(M[i][k]))
            if not M[pivot][k]:
                raise ArithmeticError("singular approximate Jacobian")
            M[k],M[pivot]=M[pivot],M[k]
            row=M[k]
            inv = 1/row[k]
            row[k:] = [x*inv for x in row[k:]]
            for i in range(N):
                if i==k:
                    continue
                dst=M[i]
                m=dst[k]
                if m:
                    dst[k]=D(0)
                    dst[k+1:] = [x-m*y for x,y in zip(dst[k+1:],row[k+1:])]
        return yq, [[int((x*yq).to_integral_value()) for x in row[N:]] for row in M]


def isolate(data):
    q = int(data["Qx"])
    z = [int(s) for s in data["xnum"]]
    radius = F(int(data["rho_num"]),int(data["rho_den"]))
    require(len(z)==N and q>0 and 0<radius<=F(1,10**65),"Invalid dimensions or radius")
    polys = equations()
    require(len(polys)==N, "Invalid system size")
    value, jac, growth = [], [], []
    for p in polys:
        val, row, g = 0, {}, 0
        for m,a in p.items():
            if not a:
                continue
            if len(m)==0:
                val += a*q*q
            elif len(m)==1:
                val += a*q*z[m[0]]
                add(row,m[0],a*q)
            else:
                i,j=m
                val += a*z[i]*z[j]
                add(row,i,a*z[j])
                add(row,j,a*z[i])
                g += 2*abs(a)
        value.append(val)
        jac.append(row)
        growth.append(g)
    yq,y = approximate_inverse(jac,q)
    unit = q*yq
    for radius in (radius,):
        for i,row in enumerate(y):
            product = [0]*N
            for a,j in zip(row,jac):
                for k,b in j.items():
                    product[k] += a*b
            product[i] -= unit
            err = F(sum(map(abs,product)),unit)
            jac_motion = radius*F(sum(abs(a)*b for a,b in zip(row,growth)),yq)
            displacement = F(abs(sum(a*b for a,b in zip(row,value))),q*unit)
            require(displacement/radius+err+jac_motion < 1,
                    f"Contraction failed at row {i}")
    return [F(x,q) for x in z]


class Interval:
    def __init__(self, lo, hi=None):
        self.lo = lo
        self.hi = lo if hi is None else hi

    def __add__(self, b):
        return Interval(self.lo+b.lo,self.hi+b.hi)

    def __sub__(self,b):
        return Interval(self.lo-b.hi,self.hi-b.lo)

    def __mul__(self,b):
        t = [u*v for u in (self.lo,self.hi) for v in (b.lo,b.hi)]
        return Interval(min(t),max(t))


def sub(a,b):
    return tuple(x-y for x,y in zip(a,b))


def cross(a,b):
    return a[0]*b[1]-a[1]*b[0]


def dot(a,b):
    return a[0]*b[0]+a[1]*b[1]


def circumcenter(a,b,c):
    u,v=sub(b,a),sub(c,a)
    h,k=dot(u,u)/2,dot(v,v)/2
    d=cross(u,v)
    return (a[0]+(h*v[1]-k*u[1])/d,a[1]+(u[0]*k-v[0]*h)/d)


def geometry(z):
    r = F(1,10**65)
    const = tuple(map(F,(1,0)))
    middle = [const]+list(zip(z[:62:2],z[1:62:2]))
    points = [tuple(Interval(x if not j else x-r,x if not j else x+r) for x in xy)
              for j,xy in enumerate(middle)]
    tlo,thi=z[T]-r,z[T]+r
    require(0<tlo<thi<F(13,100), "Invalid radius")
    require(all(w-r>0 for w in z[63:110]), "Nonpositive rod weight")
    require(F("0.346645456927389643467869738193878789537187452966783984053969")**2<tlo and
            thi<F("0.346645456927389643467869738193878789537187452966783984053970")**2,
            "Decimal bracket failed")
    # Strict half-plane test against all other anchors makes the ordered chain
    # the positively oriented convex boundary, avoiding trigonometric unwrap.
    for i in range(10):
        a,b = points[(i-1)%10],points[i]
        c=points[10+i]
        require(cross(a,b).lo>0 and dot(a,b).lo>0
                and cross(a,c).lo>0 and cross(c,b).lo>0,"Arc cone")
        for j in range(10):
            if j not in ((i-1)%10,i):
                require(cross(sub(b,a),sub(points[j],a)).lo>0,"Nonconvex anchor order")
    for face in INACTIVE:
        ids=[10+i for i in face]
        v=tuple(Interval(x) for x in circumcenter(*(middle[j] for j in ids)))
        for j in ids:
            u=sub(v,points[j]); require(dot(u,u).hi<tlo,"Inactive witness")
    faces=[tuple(10+i for i in face) for face in ACTIVE+INACTIVE]
    faces.extend(((i-1)%10,i,10+i) for i in range(10))
    faces.extend((i,10+i,10+(i+1)%10) for i in range(10))
    boundary=Counter()
    for a,b,c in faces:
        v=cross(sub(points[b],points[a]),sub(points[c],points[a]))
        if v.hi<0:
            b,c=c,b
        else:
            require(v.lo>0,"Ambiguous face orientation")
        for u,v in ((a,b),(b,c),(c,a)):
            boundary[u,v]+=1
            boundary[v,u]-=1
    want=Counter({(i,(i+1)%10):1 for i in range(10)})
    want.update({((i+1)%10,i):-1 for i in range(10)})
    require(all(boundary[e]==want[e] for e in (boundary.keys()|want.keys())), "Wrong oriented boundary")
    # An anchor has exactly the two active nearest centers and gives tightness
    # for this configuration (not arbitrary-center optimality).
    for j in range(12,23):
        u=sub(points[0],points[j]); require(dot(u,u).lo>thi,"Anchor not tight")


def main(path):
    raw=Path(path).read_bytes()
    require(sha256(raw).hexdigest()==DIGEST,"Candidate input digest mismatch")
    geometry(isolate(json.loads(raw)))
    print("n=13 boxed root and exact full-disk attaining construction: PASS")


if __name__=="__main__":
    main(sys.argv[1] if len(sys.argv)>1 else Path(__file__).resolve().parent.parent / "verification/n13/candidate_midpoint.json")
