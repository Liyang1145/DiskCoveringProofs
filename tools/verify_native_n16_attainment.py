#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
"""Independent exact arithmetic replay of the pinned n16 root and upper cover."""
from collections import Counter
from fractions import Fraction as Q
from hashlib import sha256
from pathlib import Path
import json
import sys

ROOT_SHA = "a89dfe7e356a670176622e0726a0e7d27f14136e5e1d79326f9afedac285ab9e"
ACTIVE = [(0,1,12),(2,12,13),(3,4,13),(5,13,14),(6,7,14),(8,14,15),
          (9,10,15),(11,12,15),(12,13,15),(13,14,15)]
SLACK = [(0,11,12),(1,2,12),(2,3,13),(4,5,13),
         (5,6,14),(7,8,14),(8,9,15),(10,11,15)]
T, P, N = 74, 75, 140


def require(condition, what):
    if not condition:
        raise ValueError(what)


def linear_vertex(v, d):
    return ({2*(v-1)+d: 1}, 0) if v else ({}, 1-d)


def equations():
    def squares(pairs, rhs):
        out = Counter({rhs: -1})
        for u, v in pairs:
            for d in range(2):
                aa, ac = linear_vertex(u, d)
                bb, bc = linear_vertex(v, d)
                terms = Counter(aa)
                terms.subtract(bb)
                terms[-1] = ac-bc
                for i, a in terms.items():
                    for j, b in terms.items():
                        out[tuple(sorted(k for k in (i,j) if k >= 0))] += a*b
        return out

    # The ordering is part of the pinned Lagrange multiplier coordinates.
    edges = ([(i,12+i) for i in range(12)] +
             [(i,12+(i+1)%12) for i in range(12)] +
             [(28+j,12+i) for j, face in enumerate(ACTIVE) for i in face])
    f = [squares([(u,v)], (T,)) for u,v in edges]
    for i in range(1,12):
        j = 2*(i-1)
        f.append(Counter({(j,j):1, (j+1,j+1):1, (): -1}))

    stat = [Counter() for _ in range(P)]
    stat[T][()] = 1
    for k, poly in enumerate(f):
        for mon, c in poly.items():
            for j,i in enumerate(mon):
                stat[i][mon[:j]+mon[j+1:]+(P+k,)] += c
    return f + stat


def root_box(data):
    x, y = list(map(int,data["xnum"])), [list(map(int,row)) for row in data["Ynum"]]
    s, z, rho = int(data["Qx"]), int(data["Qy"]), Q(data["rho"])
    require(len(x) == len(y) == N and all(len(row)==N for row in y), "root dimension")
    require(rho > 0 and s > 0 and z > 0, "root scales")
    polys = equations()
    require(len(polys)==N, "equation dimension")
    value, jac, hess = [0]*N, [[0]*N for _ in x], [[0]*N for _ in x]
    for k, poly in enumerate(polys):
        for m,a in poly.items():
            if not m:
                value[k] += a*s*s
            elif len(m)==1:
                i, = m
                value[k] += a*x[i]*s
                jac[k][i] += a*s
            else:
                i,j=m
                value[k] += a*x[i]*x[j]
                jac[k][i] += a*x[j]
                jac[k][j] += a*x[i]
                hess[k][i] += abs(a)
                hess[k][j] += abs(a)
    zs = z*s
    row_variation = list(map(sum,hess))
    # Fixed-point map x -> x-YF(x); use induced infinity norm.
    err = max_offset = 0
    for i, row in enumerate(y):
        center_error = sum(abs((zs if i==j else 0)-
                               sum(row[k]*jac[k][j] for k in range(N)))
                           for j in range(N))
        slope_error = sum(abs(a)*v for a,v in zip(row,row_variation))
        bound = Q(center_error,zs) + rho*Q(slope_error,z)
        offset = Q(abs(sum(a*b for a,b in zip(row,value))),z*s*s)
        require(bound < 1 and offset + bound*rho < rho, "root contraction/invariance")
        err=max(err,bound)
        max_offset=max(max_offset,offset)
    return [Q(a,s) for a in x], min(rho, max_offset/(1-err)), err


class I:
    """Outward-exact rational interval."""
    def __init__(self,a,b=None):
        self.a,self.b=Q(a),Q(a if b is None else b)
    def __add__(self,o):
        return I(self.a+o.a,self.b+o.b)
    def __sub__(self,o):
        return I(self.a-o.b,self.b-o.a)
    def __mul__(self,o):
        ts=[a*b for a in (self.a,self.b) for b in (o.a,o.b)]
        return I(min(ts),max(ts))
    def mid(self):
        return (self.a+self.b)/2


def minus(a,b):
    return tuple(u-v for u,v in zip(a,b))


def dot(a,b):
    return a[0]*b[0]+a[1]*b[1]


def cross(a,b):
    return a[0]*b[1]-a[1]*b[0]


def circumcenter(u,v,w):
    p,q=minus(v,u),minus(w,u)
    d=2*cross(p,q)
    aa,bb=dot(p,p),dot(q,q)
    return u[0]+(aa*q[1]-bb*p[1])/d, u[1]+(p[0]*bb-q[0]*aa)/d


def check_cover(x,rho):
    box=[I(a-rho,a+rho) for a in x]
    v=[(I(1),I(0))]+[tuple(box[i:i+2]) for i in range(0,74,2)]
    t=box[T]
    require(Q(".308219801898617848870103269221814832006106420717596171183693")**2<t.a and
            t.b<Q(".308219801898617848870103269221814832006106420717596171183694")**2,
            "radius interval")
    # The exact equations cover the active face witnesses and all cap endpoints.
    for i in range(2,16):
        d=minus(v[0],v[12+i])
        require(dot(d,d).a>t.b,"anchor distance to other centers")
    for triangle in SLACK:
        points=[v[12+i] for i in triangle]
        p=tuple(I(q) for q in circumcenter(*(tuple(a.mid() for a in c) for c in points)))
        for c in points:
            d=minus(c,p)
            require(dot(d,d).b<t.a,"strict nonactive face witness")
    triangles=[tuple(12+i for i in a) for a in ACTIVE+SLACK]
    for i in range(12):
        prev=(i-1)%12
        nxt=(i+1)%12
        triangles.extend([(prev,i,12+i),(i,12+nxt,12+i)])
    require(len(triangles)==42,"face count")
    chain=Counter()
    for a,b,c in triangles:
        ori=cross(minus(v[b],v[a]),minus(v[c],v[a]))
        if ori.b<0:
            b,c=c,b
        else:
            require(ori.a>0,"strict triangle orientation")
        for i,j in [(a,b),(b,c),(c,a)]:
            chain[(i,j)]+=1
            chain[(j,i)]-=1
    for i in range(12):
        j=(i+1)%12
        chain[(i,j)]-=1
        chain[(j,i)]+=1
    require(not any(chain.values()),"oriented 2-chain boundary")
    # A transverse ray in direction (1,1/100): count its single upward
    # crossing by the short positively oriented anchor arcs.
    ray=(I(1),I(Q(1,100)))
    sides=[cross(ray,v[i]) for i in range(12)]
    require(all(s.a>0 or s.b<0 for s in sides),"strict transverse ray side")
    crossings=0
    for i in range(12):
        prev=(i-1)%12
        a,b,c=v[prev],v[i],v[12+i]
        require(cross(a,b).a>0 and dot(a,b).a>0,"positive short anchor step")
        require(cross(a,c).a>0 and cross(c,b).a>0,"cap center direction")
        if sides[prev].b<0<sides[i].a:
            # This sign change crosses the positive ray, not its negative:
            # short positive arcs crossing the negative ray go + to -.
            crossings+=1
    require(crossings==1,"one anchor winding")


def main():
    if len(sys.argv)!=2:
        raise SystemExit("usage: verify_native_n16_attainment.py /path/to/root16.json")
    raw=Path(sys.argv[1]).read_bytes()
    require(sha256(raw).hexdigest()==ROOT_SHA,"unpinned root bytes")
    x,rho,err=root_box(json.loads(raw))
    check_cover(x,rho)
    print("N16 EXACT ROOT AND WHOLE-DISK COVER PASSED")
    print("Ceiling of fixed-point Lipschitz bound times 10^12:",
          -(-(err*10**12).numerator//(err*10**12).denominator))

if __name__=="__main__":
    main()
