#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
"""Read-only exact checker of existence and attainment for the n=17 candidate."""
from collections import Counter
from fractions import Fraction as F
from hashlib import sha256
from pathlib import Path
import json
import sys

DIGEST = "f520c34816aab807fd115933a1159151ec7e71e4b8fb3b9b9d85d7c554050ac2"
N, G, T = 157, 82, 82
ACTIVE = [(0,1,16),(0,11,16),(1,15,16),(2,3,15),(3,4,15),(4,14,15),
          (5,6,14),(6,7,13),(8,9,12),(8,12,13),(9,10,12),(11,12,16),(13,14,16)]
INACTIVE = [(1,2,15),(4,5,14),(6,13,14),(7,8,13),(10,11,12),(12,13,16),(14,15,16)]


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
    edges = [(i, 12+(i+k)%12) for k in range(2) for i in range(12)]
    edges += [(29+j,12+i) for j, face in enumerate(ACTIVE) for i in face]
    constraints = []
    for u,v in edges:
        p = {(T,): -1}
        for k in range(2):
            square_difference(p, u, v, k)
        constraints.append(p)
    for node in range(1,12):
        i = 2*(node-1)
        constraints.append({(): -1,(i,i):1,(i+1,i+1):1})
    stationary = [{} for _ in range(G+1)]
    stationary[T][()] = 1
    for i,p in enumerate(constraints):
        for monomial,a in p.items():
            for j,k in enumerate(monomial):
                add(stationary[k], monomial[:j]+monomial[j+1:]+(G+1+i,), a)
    return constraints + stationary


def isolate(data):
    q,yq = int(data["Qx"]),int(data["Qy"])
    z = [int(s) for s in data["xnum"]]
    y = [[int(s) for s in row] for row in data["Ynum"]]
    require(len(z)==len(y)==N and all(len(row)==N for row in y) and q>0 and yq>0,
            "Invalid dimensions")
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
    unit = q*yq
    for radius in (F(1,10**60),F(1,10**80)):
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
    r = F(1,10**80)
    const = tuple(map(F,(1,0)))
    middle = [const]+list(zip(z[:82:2],z[1:82:2]))
    points = [tuple(Interval(x if not j else x-r,x if not j else x+r) for x in xy)
              for j,xy in enumerate(middle)]
    tlo,thi=z[T]-r,z[T]+r
    require(0<tlo<thi<F(9,100), "Invalid radius")
    require(all(w-r>0 for w in z[83:146]), "Nonpositive rod weight")
    require(F("0.298531589256428059869843774423980703734387603913740470124900")**2<tlo and
            thi<F("0.298531589256428059869843774423980703734387603913740470124901")**2,
            "Decimal bracket failed")
    # Strict half-plane test against all other anchors makes the ordered chain
    # the positively oriented convex boundary, avoiding trigonometric unwrap.
    for i in range(12):
        a,b = points[(i-1)%12],points[i]
        c=points[12+i]
        require(cross(a,b).lo>0 and dot(a,b).lo>0
                and cross(a,c).lo>0 and cross(c,b).lo>0,"Arc cone")
        for j in range(12):
            if j not in ((i-1)%12,i):
                require(cross(sub(b,a),sub(points[j],a)).lo>0,"Nonconvex anchor order")
    for face in INACTIVE:
        ids=[12+i for i in face]
        v=tuple(Interval(x) for x in circumcenter(*(middle[j] for j in ids)))
        for j in ids:
            u=sub(v,points[j]); require(dot(u,u).hi<tlo,"Inactive witness")
    faces=[tuple(12+i for i in face) for face in ACTIVE+INACTIVE]
    faces.extend(((i-1)%12,i,12+i) for i in range(12))
    faces.extend((i,12+i,12+(i+1)%12) for i in range(12))
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
    want=Counter({(i,(i+1)%12):1 for i in range(12)})
    want.update({((i+1)%12,i):-1 for i in range(12)})
    require(all(boundary[e]==want[e] for e in (boundary.keys()|want.keys())), "Wrong oriented boundary")
    # An anchor has exactly the two active nearest centers and gives tightness
    # for this configuration (not arbitrary-center optimality).
    for j in range(14,29):
        u=sub(points[0],points[j]); require(dot(u,u).lo>thi,"Anchor not tight")


def main(path):
    raw=Path(path).read_bytes()
    require(sha256(raw).hexdigest()==DIGEST,"Candidate input digest mismatch")
    geometry(isolate(json.loads(raw)))
    print("n=17 boxed root and exact full-disk attaining construction: PASS")


if __name__=="__main__":
    main(sys.argv[1])
