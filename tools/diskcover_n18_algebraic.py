# SPDX-License-Identifier: MIT
"""Independent exact root and unit-disk coverage check for the n=18 candidate.

The sole input is the source's pinned candidate-number file; no external
executable or previously recorded verdict is imported.
"""
import argparse
from collections import Counter, defaultdict
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path

SHA = "446d47409d67bd6d6d2af39813b6c4b974f29d896ea8b25f7ec15bf78dd13c34"
FACES = [(0,1,14),(0,11,14),(1,2,13),(1,13,14),(2,3,13),(3,4,12),
         (3,12,13),(4,5,12),(5,6,12),(6,7,16),(6,12,17),(6,16,17),
         (7,8,16),(8,9,16),(9,10,15),(9,15,16),(10,11,15),(11,14,15),
         (12,13,17),(13,14,17),(14,15,17),(15,16,17)]
ACTIVE = [FACES[i] for i in (0,1,2,3,6,7,8,9,10,11,12,15,16,17,19,20)]
EDGES = [(i,12+i) for i in range(12)] + [(i,12+(i+1)%12) for i in range(12)]
EDGES += [(30+j,12+k) for j,face in enumerate(ACTIVE) for k in face]


def require(p, what):
    if not p:
        raise ArithmeticError(what)


def equations():
    # Monomials are (coefficient, variable tuple). Use F=(g,h,∇L),
    # in the order [72 rods, 11 spheres, 90 spatial forces, 1 time force].
    g = [[] for _ in range(72)]
    h = [[] for _ in range(11)]
    force = [[] for _ in range(90)]

    def coordinate(point,k):
        return (None, int(k==0)) if point==0 else (2*(point-1)+k,0)

    for j,(u,v) in enumerate(EDGES):
        for k in range(2):
            i,a = coordinate(u,k)
            l,b = coordinate(v,k)
            terms = {z:c for z,c in ((i,1),(l,-1)) if z is not None}
            const = a-b
            g[j].append((const**2,()))
            for z,c in terms.items():
                g[j].append((2*const*c,(z,)))
                force[z].append((2*c*const,(91+j,)))
                for zz,cc in terms.items():
                    g[j].append((c*cc,(z,zz)))
                    force[z].append((2*c*cc,(91+j,zz)))
        g[j].append((-1,(90,)))
    for j in range(11):
        h[j].append((-1,()))
        for i in (2*j,2*j+1):
            h[j].append((1,(i,i)))
            force[i].append((2,(163+j,i)))
    return g+h+force+[[(1,())]+[(-1,(91+j,)) for j in range(72)]]


def root_certificate(data):
    x = data["xnum"]
    y = data["Ynum"]
    q = int(data["Qx"])
    p = int(data["Qy"])
    polys = equations()
    n = len(polys)
    require(n==174 and len(x)==n and len(y)==n and all(len(row)==n for row in y),"root dimensions")
    jac = []
    f = []
    widths = []
    for poly in polys:
        v = 0
        J = defaultdict(int)
        # Exact quadratic coefficient cancellation before interval norm bounds.
        quadratics = Counter()
        for c,vs in poly:
            if len(vs)==0:
                v += c*q*q
            elif len(vs)==1:
                i, = vs
                v += c*x[i]*q
                J[i] += c*q
            else:
                i,j = vs
                v += c*x[i]*x[j]
                J[i] += c*x[j]
                J[j] += c*x[i]
                quadratics[tuple(sorted(vs))] += c
        f.append(v)
        jac.append(J)
        widths.append(2*sum(abs(c) for c in quadratics.values()))
    # p*q^2 scaling for YF, p*q scaling for YJ.
    worst = {}
    for k in (60,80):
        rho = 10**k
        cases = []
        for i,row in enumerate(y):
            yz = sum(a*b for a,b in zip(row,f))
            J = defaultdict(int)
            for u,a in enumerate(row):
                if a:
                    for v,b in jac[u].items():
                        J[v] += a*b
            J[i] -= p*q
            error = F(sum(abs(v) for v in J.values()),p*q)
            variation = F(sum(abs(a)*d for a,d in zip(row,widths)),p*rho)
            cert = F(abs(yz)*rho,p*q*q)+error+variation
            require(cert<1,f"contraction failed at radius 10^-{k}, row {i}: {float(cert)}")
            cases.append(cert)
        worst[k]=max(cases)
    return x,q,worst


def _sub(a,b):
    return (a[0]-b[0],a[1]-b[1])


def _det(a,b):
    return a[0]*b[1]-a[1]*b[0]


def _dot(a,b):
    return a[0]*b[0]+a[1]*b[1]


def isolate_radius(x,q):
    e=F(1,10**80)
    t=F(x[90],q)
    lower="0.290167717640566729113154525601061718306280885754041798808094"
    upper="0.290167717640566729113154525601061718306280885754041798808095"
    require(0<F(lower)**2<t-e<t+e<F(upper)**2,"radius isolation failed")
    return [lower,upper]


def upper_certificate(x,q):
    # All points including the fixed q0 are enclosed coordinatewise by e.
    e = F(1,10**80)
    mid = [(F(1),F(0))]+[(F(x[k],q),F(x[k+1],q)) for k in range(0,90,2)]
    lower_t = F(x[90],q)-e
    require(lower_t>0,"candidate has nonpositive radius")

    def bilinear_margin(a,b):
        # All bilinear check arguments are points or differences of points.
        # Each argument coordinate moves by at most 2e.
        return 2*e*(sum(map(abs,a))+sum(map(abs,b)))+8*e*e

    def cross_pos(a,b):
        return _det(a,b)>bilinear_margin(a,b)

    def tri_pos(i,j,k):
        return cross_pos(_sub(mid[j],mid[i]),_sub(mid[k],mid[i]))

    triangles = [tuple(12+k for k in face) for face in FACES]
    for i in range(12):
        a,b,c = (i-1)%12,i,12+i
        triangles += [(a,b,c),(b,12+(i+1)%12,c)]
        # Roots enforce anchor norm 1. Strict orientation and a positive
        # dot product bind the forward arc to the short arc (< pi/2).
        require(cross_pos(mid[a],mid[b]),"anchor turn not positive")
        require(_dot(mid[a],mid[b])>bilinear_margin(mid[a],mid[b]),"anchor arc too long")
        require(cross_pos(mid[a],mid[c]) and cross_pos(mid[c],mid[b]),"center outside arc cone")
        require(all(tri_pos(a,b,j) for j in range(12) if j not in (a,b)),
                "edge does not strictly support the polygon")

    directed=Counter()
    for i,j,k in triangles:
        if not tri_pos(i,j,k):
            j,k=k,j
        require(tri_pos(i,j,k),"nonpositive oriented triangle")
        directed.update(((i,j),(j,k),(k,i)))
    residual=directed.copy()
    for i,j in directed:
        residual[(i,j)]-=directed[(j,i)]
    require(+residual==Counter((i,(i+1)%12) for i in range(12)), "triangle boundary mismatch")

    # q0 meets precisely the two boundary disks assigned by its rods.
    upper_t = F(x[90],q)+e
    for c in mid[14:30]:
        displacement = _sub(c,mid[0])
        require(sum(max(F(0),abs(v)-e)**2 for v in displacement)>upper_t,
                "nonincident disk obscures tight boundary anchor")
    min_slack = None
    for face in set(FACES)-set(ACTIVE):
        a,b,c = (mid[12+i] for i in face)
        u,v = _sub(b,a),_sub(c,a)
        d = 2*_det(u,v)
        require(d!=0,"degenerate candidate face")
        # The midpoint circumcenter is merely a rational witness.
        su,sv = _dot(u,u),_dot(v,v)
        w0,w1=(su*v[1]-sv*u[1])/d,(u[0]*sv-v[0]*su)/d
        w=(w0+a[0],w1+a[1])
        for i in face:
            t=_sub(w,mid[12+i])
            upper_dist=sum((abs(z)+e)**2 for z in t)
            slack=lower_t-upper_dist
            require(slack>0,"inactive face witness lacks strict margin")
            min_slack=slack if min_slack is None else min(min_slack,slack)
    slack_report=F(1212,10**6)
    require(min_slack>slack_report,"inactive face slack below reporting floor")
    return {"oriented_triangles":len(triangles), "supported_short_caps":12, "tight_boundary_anchor":0,
            "inactive_faces":len(FACES)-len(ACTIVE), "strict_slack_lower":str(slack_report)}


def _expect_rejection(action, marker):
    try:
        action()
    except ArithmeticError as exc:
        require(marker in str(exc), f"wrong negative-control failure: {exc}")
    else:
        raise ArithmeticError(f"negative control unexpectedly accepted: {marker}")


def check(path, negative_controls=False):
    raw=Path(path).read_bytes()
    require(hashlib.sha256(raw).hexdigest()==SHA,"candidate file digest mismatch")
    data=json.loads(raw)
    require(data["edges"]==[list(e) for e in EDGES],"rod order mismatch")
    require(data["all_faces"]==[list(f) for f in FACES],"center-face order mismatch")
    require(data["active_faces"]==[list(f) for f in ACTIVE],"active-face order mismatch")
    x,q,r=root_certificate(data)
    report={"status":"isolated_root_and_cover_not_global_optimality",
            "sha256":SHA, "root_radii_checked":list(r), "exact_contact_rods":len(EDGES),
            "containment_max_display":{k:float(v) for k,v in r.items()},
            "candidate_radius_strict_interval":isolate_radius(x,q),
            "coverage":upper_certificate(x,q)}
    if negative_controls:
        bad={**data,"Ynum":[[0]*174]+data["Ynum"][1:]}
        _expect_rejection(lambda:root_certificate(bad),"contraction failed")
        bad_center=x.copy()
        bad_center[22] = -bad_center[22]
        _expect_rejection(lambda:upper_certificate(bad_center,q),"center outside arc cone")
        bad_radius=x.copy()
        bad_radius[90] -= q//10
        _expect_rejection(lambda:isolate_radius(bad_radius,q),"radius isolation failed")
        report["negative_controls_rejected"]=3
    return report


if __name__=="__main__":
    a=argparse.ArgumentParser(description=__doc__)
    a.add_argument("candidate")
    a.add_argument("--negative-controls", action="store_true")
    args=a.parse_args()
    print(json.dumps(check(args.candidate,args.negative_controls),indent=2))
