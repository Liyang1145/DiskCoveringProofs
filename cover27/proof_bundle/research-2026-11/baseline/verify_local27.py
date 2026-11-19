"""Check the full-space positive stress and second-order certificate for n=27."""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction as F
import hashlib
import json
from math import isqrt
from pathlib import Path

import sympy as sp

from cover27_model import GEOMETRY, T_INDEX, center_expressions, edge_contact, face_contact, primitive, system
from verify_contact_root import ZERO, absolute, add, mul, point, scale, sub
from verify_cover27 import anchor, ivcross, ivdiv, ivnorm, ivsub, load_and_check

# The rotational gauge is the second coordinate of outer center 2.
GAUGE=5
FREE=tuple(i for i in range(54) if i!=GAUGE)
INDEX={j:i for i,j in enumerate(FREE)}


def sqdistance(a,b):
    return ivnorm(ivsub(a,b))


def check_far(q,ids,c,t,inside=False):
    if inside and ivnorm(q)[1]>=1:
        raise ValueError("active vertex is not strictly inside the large disk")
    if any(sqdistance(q,p)[0]<=t[1] for j,p in enumerate(c) if j not in ids):
        raise ValueError("active point is not separated from other centers")


def linear_intersection(u,v,h,k):
    d=ivcross(u,v)
    return (ivdiv(sub(mul(h,v[1]),mul(k,u[1])),scale(F(2),d)),
            ivdiv(sub(mul(u[0],k),mul(v[0],h)),scale(F(6),d)))


def circumcenter(a,b,c):
    u,v=ivsub(b,a),ivsub(c,a)
    return linear_intersection(u,v,sub(ivnorm(b),ivnorm(a)),sub(ivnorm(c),ivnorm(a)))


def sqrt_interval(a):
    q=10**44
    if a[0]<=0:
        raise ValueError("bisector does not intersect the unit circle transversely")
    lo,hi=(isqrt(v.numerator*q*q//v.denominator) for v in a)
    return F(lo,q),F(hi+1,q)


def check_exposure(geom,c,t):
    for ids in geom["active_faces"]:
        p=circumcenter(*(c[i] for i in ids))
        check_far(p,ids,c,t,inside=True)
    for ids,root in zip(geom["edges"],geom["anchors"]):
        a,b=(c[i] for i in ids)
        # The moving point is on the unit circle and equidistant from a and b.
        u=ivsub(b,a)
        u0=ivsub(geom["centers"][ids[1]],geom["centers"][ids[0]])
        side=ivcross(u0,root)
        sign=1 if side[0]>0 else -1 if side[1]<0 else 0
        if not sign:
            raise ValueError("unverified bisector branch")
        uu=ivnorm(u)
        g=ivdiv(sub(ivnorm(b),ivnorm(a)),scale(F(2),uu))
        foot=tuple(mul(z,g) for z in u)
        h=sqrt_interval(ivdiv(sub(point(1),ivnorm(foot)),scale(F(3),uu)))
        p=add(foot[0],scale(F(-3*sign),mul(u[1],h))),add(foot[1],scale(F(sign),mul(u[0],h)))
        check_far(p,ids,c,t)
        q=anchor(a,b,t)
        d=ivcross(a,b)
        if ivdiv(ivcross(q,b),d)[0]<=0 or ivdiv(ivcross(a,q),d)[0]<=0:
            raise ValueError("boundary intersection is outside the positive cone")


class Jet:
    """Value, gradient and Hessian of a factored polynomial on a local box."""

    def __init__(self,v,g,h):
        self.v,self.g,self.h=v,g,h

    @classmethod
    def coordinate(cls,v,n,i=None):
        return cls(v,[point(int(j==i)) for j in range(n)],[[ZERO]*n for _ in range(n)])

    def __add__(self,b):
        return Jet(add(self.v,b.v),[add(x,y) for x,y in zip(self.g,b.g)],
                   [[add(x,y) for x,y in zip(u,v)] for u,v in zip(self.h,b.h)])

    def scaled(self,k):
        return Jet(scale(k,self.v),[scale(k,x) for x in self.g],
                   [[scale(k,x) for x in row] for row in self.h])

    def __sub__(self,b):
        return self+b.scaled(F(-1))

    def __mul__(self,b):
        d=len(self.g)
        return Jet(mul(self.v,b.v),
                   [add(mul(x,b.v),mul(self.v,y)) for x,y in zip(self.g,b.g)],
                   [[add(add(mul(self.h[i][j],b.v),mul(self.v,b.h[i][j])),
                         add(mul(self.g[i],b.g[j]),mul(self.g[j],b.g[i])))
                     for j in range(d)] for i in range(d)])


def contact_jet(face,co,t):
    n=len(co)
    p=[Jet.coordinate(v,n,i) for i,v in enumerate(co)]
    a,b=p[:2],p[2:4]
    t=Jet.coordinate(t,n)

    def dot(u,v):
        return u[0]*v[0]+(u[1]*v[1]).scaled(F(3))

    def cross(u,v):
        return u[0]*v[1]-u[1]*v[0]

    def difference(u,v):
        return [a-b for a,b in zip(u,v)]

    u=difference(b,a)
    if face:
        c=p[4:6]
        v,w=difference(c,a),difference(c,b)
        determinant=cross(u,v)
        return dot(u,u)*dot(v,v)*dot(w,w)-(t*determinant*determinant).scaled(F(12))

    midpoint=[(x+y).scaled(F(1,2)) for x,y in zip(a,b)]
    radial=Jet.coordinate(point(1),n)+dot(midpoint,midpoint)+dot(u,u).scaled(F(1,4))-t
    projection=dot(midpoint,u).scaled(F(2))
    x,y=(radial*p-projection*q for p,q in zip(u,midpoint))
    determinant=cross(midpoint,u)
    return dot((x,y),(x,y))-(determinant*determinant).scaled(F(12))


def components(box,geom,delta=F(0),penalties=None):
    """Enclose gradient rows and the non-Gram part of the energy Hessian."""
    t=box[T_INDEX]
    c=[tuple((z[0]-delta,z[1]+delta) if 2*i+j!=GAUGE else z for j,z in enumerate(p))
       for i,p in enumerate(geom["centers"])]
    check_exposure(geom,c,t)
    points=center_expressions()
    contacts,_=system()
    lookup={p:i for i,p in enumerate(contacts)}
    orbits=[]
    shapes=[(True,f) for f in geom["active_faces"]]+[(False,e) for e in geom["edges"]]
    for face,ids in shapes:
        raw=-face_contact(points,ids) if face else edge_contact(points,ids)
        p=primitive(raw,GEOMETRY)
        typ=lookup[p]
        normalizer=F(p.LC()/sp.Poly(raw,*GEOMETRY,domain=sp.QQ).LC())
        orbits.append((typ,normalizer))
    counts=Counter(j for j,_ in orbits)
    if tuple(counts[j] for j in range(8))!=(3,3,3,6,6,6,6,3):
        raise ValueError("wrong group orbit sizes")
    # Check that these are precisely the D3 orbits, rather than merely
    # polynomials which coincide on the symmetry-fixed subspace.
    def key(ids):
        return tuple(sorted(ids))

    def reflect(k):
        sector,typ=divmod(k,9)
        if typ==1:
            return 9*((-sector-1)%3)+1
        reflection=(0,1,2,4,3,6,5,8,7)
        return 9*((-sector)%3)+reflection[typ]

    for j in range(8):
        members={key(ids) for (_,ids),(q,_) in zip(shapes,orbits) if q==j}
        rep=next(iter(members))
        orbit={key(tuple((k+9*s)%27 for k in seed)) for s in range(3)
               for seed in (rep,tuple(reflect(k) for k in rep))}
        if orbit!=members:
            raise ValueError("active set is not the full symmetry orbit")
    A=[]
    H=[[ZERO for _ in FREE] for _ in FREE]
    weights=[]
    for k,((face,ids),(j,s)) in enumerate(zip(shapes,orbits)):
        lam=scale(-s/counts[j],box[10+j])
        if lam[0]<=0:
            raise ValueError("nonpositive stress")
        weights.append(lam)
        co=[z for i in ids for z in c[i]]
        jet=contact_jet(face,co,t)
        local=[2*i+j for i in ids for j in (0,1)]
        curvature_weight=lam
        if penalties is not None:
            # The polynomial vanishes at the exact root. Use the mean value
            # bound to retain that cancellation on the full coordinate box.
            size=delta*sum(absolute(g) for i,g in zip(local,jet.g) if i in INDEX)
            score=scale(penalties[k],(max(-size,jet.v[0]),min(size,jet.v[1])))
            if absolute(score)>=2*lam[0]:
                raise ValueError("quadratic penalty may exceed the linear term")
            curvature_weight=add(lam,score)
        row=[ZERO for _ in FREE]
        for i,ii in enumerate(local):
            if ii not in INDEX:
                continue
            I=INDEX[ii]
            row[I]=jet.g[i]
            for j,jj in enumerate(local):
                if jj in INDEX:
                    J=INDEX[jj]
                    H[I][J]=add(H[I][J],mul(curvature_weight,jet.h[i][j]))
        A.append(row)
    return A,H,weights


def check_matrix(A,H,cert):
    g=[F(x) for x in cert["gram_weights"]]
    Y=[[int(x) for x in row] for row in cert["Ynum"]]
    sy=int(cert["Yden"])
    d=len(FREE)
    if len(g)!=len(A) or any(x<=0 for x in g) or sy<=0 or len(Y)!=d or any(len(x)!=d for x in Y):
        raise ValueError("invalid positive Gram weights or preconditioner")
    Q=10**32
    M=[[0 for _ in FREE] for _ in FREE]
    error=[[0 for _ in FREE] for _ in FREE]
    for i in range(d):
        for j in range(i+1):
            bounds=H[i][j]
            for a,k in zip(A,g):
                if a[i]!=ZERO and a[j]!=ZERO:
                    bounds=add(bounds,scale(k,mul(a[i],a[j])))
            lo=bounds[0].numerator*Q//bounds[0].denominator
            hi=-((-bounds[1].numerator*Q)//bounds[1].denominator)
            z=(lo+hi)//2
            M[i][j]=M[j][i]=z
            error[i][j]=error[j][i]=max(z-lo,hi-z)
    YM=[[sum(x*y for x,y in zip(row,column)) for column in zip(*M)] for row in Y]
    P=[[sum(x*y for x,y in zip(row,other)) for other in Y] for row in YM]
    colsum=[sum(map(abs,col)) for col in zip(*Y)]
    radii=[sum(x*y for x,y in zip(row,colsum)) for row in error]
    margin=min(P[i][i]-sum(abs(P[i][j]) for j in range(d) if j!=i)
               -sum(abs(x)*y for x,y in zip(Y[i],radii)) for i in range(d))
    if margin<=0:
        raise ValueError("the outward-enclosed congruence is not strictly diagonally dominant")
    return F(margin,sy*sy*Q)


def verify_local(base,delta):
    _,box,geom=load_and_check(base)
    source=base/"ROOT-CERTIFICATE.json"
    cert=json.loads((base/"LOCAL-MATRIX.json").read_text(encoding="utf-8"))
    if cert["root_sha256"]!=hashlib.sha256(source.read_bytes()).hexdigest():
        raise ValueError("unbound local certificate")
    A,H,weights=components(box,geom,delta,tuple(F(g) for g in cert["gram_weights"]))
    margin=check_matrix(A,H,cert)
    minimum=min(w[0] for w in weights)
    def strict_decimal_lower(x, places):
        scale=10**places
        lo=(x.numerator*scale-1)//x.denominator
        return f"{lo//scale}.{lo%scale:0{places}d}"

    print(f"Verified {len(A)} positive contact stresses (minimum > {strict_decimal_lower(minimum,6)}).")
    print(f"Verified strict diagonal dominance in all {len(FREE)} gauged coordinates "
          f"(minimum margin > {strict_decimal_lower(margin,10)}).")
    print(f"Verified the local barrier throughout the gauged box of half-width {delta}.")


if __name__=="__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("certificate",type=Path,nargs="?",default=Path(__file__).resolve().parent)
    p.add_argument("--half-width",type=F,default=F("0.000001"))
    args=p.parse_args()
    if args.half_width<0:
        p.error("negative half-width")
    verify_local(args.certificate,args.half_width)
