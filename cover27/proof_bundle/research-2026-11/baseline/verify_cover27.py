"""Rational check of the algebraic n=27 candidate and its continuous cover."""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path

import sympy as sp

from cover27_model import (
    BOUNDARY, GEOMETRY, T_INDEX, center_expressions, edge_contact,
    face_contact, primitive, system, system_record,
)
from verify_contact_root import add, mul, point, scale, sub, verify

RHO=F(1,10**74)


def ivdiv(a,b):
    if b[0]<=0<=b[1]:
        raise ValueError("division interval contains zero")
    return mul(a,(1/b[1],1/b[0]))


def ivsq(a):
    u,v=a[0]**2,a[1]**2
    return (F(0) if a[0]<=0<=a[1] else min(u,v),max(u,v))


def ivsub(a,b):
    return tuple(sub(x,y) for x,y in zip(a,b))


def ivcross(a,b):
    return sub(mul(a[0],b[1]),mul(a[1],b[0]))


def ivdot(a,b):
    return add(mul(a[0],b[0]),scale(F(3),mul(a[1],b[1])))


def ivnorm(a):
    return add(ivsq(a[0]),scale(F(3),ivsq(a[1])))


def evaluate_linear(expr,box):
    total=point(0)
    for powers,c in sp.Poly(expr,*GEOMETRY,domain=sp.QQ).terms():
        j=sum(powers)
        if j==0:
            total=add(total,point(F(c)))
        elif j==1:
            total=add(total,scale(F(c),box[powers.index(1)]))
        else:
            raise ValueError("coordinate expression is nonlinear")
    return total


def center_intervals(box):
    return [tuple(evaluate_linear(x,box) for x in p) for p in center_expressions()]


def edge_chain(faces):
    chain=Counter()
    for face in faces:
        for a,b in zip(face,face[1:]+face[:1]):
            chain[tuple(sorted((a,b)))]+=1 if a<b else -1
    return {e:s for e,s in chain.items() if s}


def triangle_radius_squared(a,b,c):
    u,v,w=ivsub(b,a),ivsub(c,a),ivsub(c,b)
    area=scale(F(12),ivsq(ivcross(u,v)))
    return ivdiv(mul(mul(ivnorm(u),ivnorm(v)),ivnorm(w)),area)


def anchor(a,b,t):
    h=sub(add(point(1),ivnorm(a)),t)
    k=sub(add(point(1),ivnorm(b)),t)
    det=ivcross(a,b)
    x=ivdiv(sub(mul(h,b[1]),mul(k,a[1])),scale(F(2),det))
    y=ivdiv(sub(mul(a[0],k),mul(b[0],h)),scale(F(6),det))
    return x,y


def verify_mesh(source,box,mesh):
    boundary=tuple(mesh["boundary"])
    faces=[tuple(face) for face in mesh["faces"]]
    if boundary!=BOUNDARY or len(faces)!=37:
        raise ValueError("wrong boundary cycle or triangle count")
    if any(len(set(f))!=3 or len(f)!=3 or any(type(i) is not int or not 0<=i<27 for i in f)
           for f in faces) or len({tuple(sorted(f)) for f in faces})!=len(faces):
        raise ValueError("bad triangle labels")
    if edge_chain(faces)!=edge_chain([boundary]):
        raise ValueError("triangle chain has the wrong boundary")

    p=center_expressions()
    c=center_intervals(box)
    t=box[T_INDEX]
    contacts,_=system()
    slack,active=[],[]
    for f in faces:
        d=triangle_radius_squared(*(c[i] for i in f))
        polynomial=primitive(face_contact(p,f),GEOMETRY)
        if polynomial in contacts[:5]:
            active.append(f)
        elif d[1]<t[0]:
            slack.append(f)
        else:
            raise ValueError(f"unproved triangle {f}")
    if (len(active),len(slack))!=(21,16):
        raise ValueError("wrong number of active/slack faces")

    anchors=[]
    edges=list(zip(boundary,boundary[1:]+boundary[:1]))
    for i,j in edges:
        g=primitive(edge_contact(p,(i,j)),GEOMETRY)
        if g not in contacts[5:]:
            raise ValueError("anchor identity is not a contact equation")
        if ivnorm(ivsub(c[i],c[j]))[1]>=4*t[0]:
            raise ValueError("anchor disks do not have strict center overlap")
        anchors.append(anchor(c[i],c[j],t))

    # The angle increments are in (0, pi/2). Since each adjacent
    # pair belongs to one small disk, the increments are also at
    # most 2 asin(r) < pi/5. Their sum is a positive multiple of 2 pi
    # smaller than 4 pi, so these anchors turn around exactly once.
    if t[1]>=F(".231")**2:
        raise ValueError("radius too large for the turn-count bound")
    pi_10_lo=F("3.14159")/10
    if pi_10_lo-pi_10_lo**3/6<=F(".231"):
        raise AssertionError("sin(pi/10) bound")
    for a,b in zip(anchors,anchors[1:]+anchors[:1]):
        if ivcross(a,b)[0]<=0 or ivdot(a,b)[0]<=0:
            raise ValueError("anchors do not form positive acute turns")
    return {"active_faces":active,"slack_faces":slack,"edges":edges,
            "centers":c,"anchors":anchors}


def load_and_check(base):
    path=base/"SYSTEM.json"
    sys=json.loads(path.read_text(encoding="utf-8"))
    cert=json.loads((base/"ROOT-CERTIFICATE.json").read_text(encoding="utf-8"))
    if sys!=system_record():
        raise ValueError("serialized polynomials differ from the reconstructed equations")
    if cert["system_sha256"]!=hashlib.sha256(path.read_bytes()).hexdigest():
        raise ValueError("root data refer to a different polynomial system")
    bound=verify(sys,cert,RHO)
    z=[F(int(x),int(cert["Qx"])) for x in cert["xnum"]]
    box=[(x-RHO,x+RHO) for x in z]
    mesh=json.loads((base/"TRIANGULATION.json").read_text(encoding="utf-8"))
    geom=verify_mesh(sys,box,mesh)
    return bound,box,geom


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate",type=Path,nargs="?",default=Path(__file__).resolve().parent)
    bound,box,geom=load_and_check(parser.parse_args().certificate)
    print(json.dumps(bound,indent=2))
    print(f"Verified the same-root cover using {len(geom['active_faces'])} active faces, "
          f"{len(geom['slack_faces'])} slack faces and {len(geom['anchors'])} boundary anchors.")
