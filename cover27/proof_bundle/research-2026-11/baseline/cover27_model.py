"""Exact polynomial description of the D3 contact configuration for 27 disks."""
from functools import lru_cache

import sympy as sp

GEOMETRY = sp.symbols("u v h mx my px py qx qy t")
DUAL = sp.symbols("mu0:8")
VARIABLES = GEOMETRY + DUAL
T_INDEX = 9
FACE_REPRESENTATIVES = ((0,9,1),(0,3,4),(2,3,4),(3,1,7),(3,5,7))
EDGE_REPRESENTATIVES = ((2,5),(5,7),(7,17))
BOUNDARY = tuple(i for k in range(3) for i in (
    2+9*k,5+9*k,7+9*k,8+9*((k+1)%3),6+9*((k+1)%3),
))


def rotate(p):
    x,y=p
    return -(x+3*y)/2,(x-y)/2


def center_expressions():
    u,v,h,mx,my,px,py,qx,qy,_ = GEOMETRY
    first = [
        (u,sp.S(0)),(v/2,v/2),(h,sp.S(0)),(mx,my),(mx,-my),
        (px,py),(px,-py),(qx,qy),(qx,-qy),
    ]
    second = [rotate(p) for p in first]
    return first+second+[rotate(p) for p in second]


def sub(a,b):
    return a[0]-b[0],a[1]-b[1]


def cross(a,b):
    return a[0]*b[1]-a[1]*b[0]


def norm(a):
    return a[0]**2+3*a[1]**2


def face_contact(p,face):
    a,b,c=(p[i] for i in face)
    return 12*GEOMETRY[T_INDEX]*cross(sub(b,a),sub(c,a))**2 \
        -norm(sub(b,a))*norm(sub(c,a))*norm(sub(c,b))


def edge_contact(p,edge):
    a,b=(p[i] for i in edge)
    t=GEOMETRY[T_INDEX]
    h,k=1+norm(a)-t,1+norm(b)-t
    return 3*(h*b[1]-k*a[1])**2+(a[0]*k-b[0]*h)**2-12*cross(a,b)**2


def primitive(expression,variables=VARIABLES):
    p=sp.Poly(expression,*variables,domain=sp.QQ)
    _,p=p.clear_denoms()
    _,p=p.primitive()
    return -p if p.LC()<0 else p


@lru_cache
def system():
    p=center_expressions()
    contact=tuple(primitive(g,GEOMETRY) for g in (
        *(face_contact(p,f) for f in FACE_REPRESENTATIVES),
        *(edge_contact(p,e) for e in EDGE_REPRESENTATIVES),
    ))
    rows=[g.as_expr() for g in contact]
    rows.extend(
        sum(mu*g.diff(x).as_expr() for mu,g in zip(DUAL,contact))-int(j==T_INDEX)
        for j,x in enumerate(GEOMETRY)
    )
    return contact,tuple(primitive(g) for g in rows)


def encode(poly):
    return [{"coefficient":str(c),"powers":list(powers)} for powers,c in poly.terms()]


def system_record():
    _,polys=system()
    return {
        "schema":"disk-cover-27-D3-contact-stationarity-v1",
        "N":27,"B":15,
        "dimension":len(VARIABLES),
        "variables":list(map(str,VARIABLES)),
        "radius_squared_index":T_INDEX,
        "equations":[encode(g) for g in polys],
    }
