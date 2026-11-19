# SPDX-License-Identifier: MIT
"""Independent exact check for the n=19 lattice candidate's graph only."""
from fractions import Fraction as F
from functools import cmp_to_key
from itertools import combinations
import json


def dot(p, q):
    return 3*p[0]*q[0] + p[1]*q[1]


def sub(p, q):
    return p[0]-q[0], p[1]-q[1]


def comb(p, q, a=1, b=1):
    return a*p[0]+b*q[0], a*p[1]+b*q[1]


def norm(p):
    return dot(p,p)


def polar_cmp(p, q):
    def half(w):
        return int(w[1] < 0 or (w[1] == 0 and w[0] < 0))
    if half(p) != half(q):
        return half(p)-half(q)
    cross = p[0]*q[1]-p[1]*q[0]
    return (cross < 0)-(cross > 0)


def check(ok, what):
    if not ok:
        raise ArithmeticError(what)


def verify():
    points = [(F(2*a+b,2),F(3*b,2)) for a in range(-2,3) for b in range(-2,3)
              if max(abs(a),abs(b),abs(a+b)) <= 2]
    outer = sorted([p for p in points if norm(p) in (9,12)], key=cmp_to_key(polar_cmp))
    inner = sorted([p for p in points if norm(p)==3], key=cmp_to_key(polar_cmp))
    check(len(outer)==12 and len(inner)==6, "lattice counts")
    anchors, faces = [], []
    for i,p in enumerate(outer):
        q = outer[(i+1)%12]
        delta=sub(q,p)
        check(norm(delta)==3 and norm(p)+norm(q)==21, "alternating shell")
        m=comb(p,q,F(1,2),F(1,2))
        offset=(-delta[1]/6,delta[0]/2)
        both=[v for v in (comb(m,offset),comb(m,offset,1,-1)) if norm(v)==13]
        check(len(both)==1, "outward anchor")
        anchors.append(both[0])
        if norm(p)==9:
            pool=[q for q in inner if norm(sub(q,p))==3]
            check(len(pool)==2 and norm(sub(*pool))==3, "equilateral side triangle")
            triple=[p,*pool]
            centroid=tuple(sum(v[j] for v in triple)/3 for j in (0,1))
            faces.append((centroid,triple))
    check(sorted(anchors,key=cmp_to_key(polar_cmp)) in
          [anchors[i:]+anchors[:i] for i in range(12)], "anchor order")
    for i,q in enumerate(anchors):
        p=anchors[(i+1)%12]
        check(polar_cmp(q,p)<0 or i==11 or q[1] < 0 <= p[1], "cyclic angle order")
        check(q[0]*p[1]-q[1]*p[0]>0 and dot(q,p)>=11, "adjacent gap maximum")

    # The selected lattice triangles must realize the same cyclic
    # incidence as the abstract candidate graph, up to relabeling.
    pairs = [set(tri[1:]) for _,tri in faces]
    check([outer.index(tri[0]) for _,tri in faces]==list(range(1,12,2)),
          "odd outer face positions")
    check(any(pairs==[{inner[(j+k)%6],inner[(j+k+1)%6]} for j in range(6)]
              for k in range(6)), "cyclic side-face incidence")

    # Derive two boundary weights by shell valence and a shallow-site
    # equilibrium; use one as an unnormalized weight for every face rod.
    sample=faces[0][1][0]; i=outer.index(sample)
    face_force=sub(sample,faces[0][0])
    arc_force=comb(sub(sample,anchors[i]),sub(sample,anchors[i-1]))
    j=next(j for j in (0,1) if arc_force[j])
    ws=-face_force[j]/arc_force[j]
    # The ratio for the alternating extreme sites follows from anchor
    # alignment, whose tangential component must vanish.
    i=next(i for i,p in enumerate(outer) if norm(p)==12)
    q=anchors[i]; e=sub(q,outer[i]); s=sub(q,outer[(i+1)%12])
    cross=lambda p,q:p[0]*q[1]-p[1]*q[0]
    we=-ws*cross(q,s)/cross(q,e)
    total=12*(we+ws)+18
    check(ws>0 and we>0 and len(faces)==6,"positive normalized stress")
    nodes=anchors+outer+inner+[p for p,_ in faces]
    check(len(nodes)==36 and len(set(nodes))==36,"distinct nodes")
    graph={}
    def put(i,j,w):
        i,j=sorted((i,j))
        graph[i,j]=graph.get((i,j),0)+w
    for i in range(12):
        for j in (i,(i+1)%12):
            put(i,12+j,(we if norm(outer[j])==12 else ws)/total)
    for i,(_,tri) in enumerate(faces):
        for p in tri:
            put(30+i,nodes.index(p),1/total)
    check(len(graph)==42 and sum(graph.values())==1,"stress size")

    f=[(F(0),F(0)) for _ in nodes]
    for (i,j),w in graph.items():
        d=sub(nodes[i],nodes[j])
        check(norm(d)==1,"active edge length")
        f[i]=comb(f[i],d,1,w)
        f[j]=comb(f[j],d,1,-w)
    for i,p in enumerate(nodes):
        check(cross(p,f[i])==0 if i<12 else norm(f[i])==0,
              "tangential or free-node equilibrium")
    for k in range(35,11,-1):
        touching={i:w for (i,j),w in graph.items() if j==k}
        total_k=sum(touching.values())
        check(total_k>0,"connected elimination")
        for i,j in combinations(touching,2):
            put(i,j,touching[i]*touching[j]/total_k)
        for i in touching:
            del graph[i,k]
    check(len(graph)==66,"positive anchor graph")

    # Any true anchor gap is <= 2 asin(1/sqrt(13)); k<=5 gaps
    # stay below pi since 11/13 > cos(pi/5)=(1+sqrt(5))/4.
    check(F(31,13)**2>5,"maximum angular range")
    b=[F(1),F(11,13)]
    for k in range(2,6):
        b.append(2*b[1]*b[-1]-b[-2])
    b.append(F(-1))
    H=[[F(0) for _ in range(12)] for _ in range(12)]
    for (i,j),w in graph.items():
        v=2*w*b[min(j-i,12-j+i)]
        H[i][i]+=v; H[j][j]+=v; H[i][j]-=v; H[j][i]-=v
    # Fix angle zero and use exact symmetric Schur complements (LDL).
    pivots=[]
    for k in range(1,12):
        d=H[k][k]
        check(d>0,"positive Hessian pivot")
        pivots.append(d)
        for i in range(k+1,12):
            for j in range(k+1,12):
                H[i][j]-=H[i][k]*H[k][j]/d
    check(sum(w*norm(sub(anchors[i],anchors[j])) for (i,j),w in graph.items())==1,
          "scaled candidate energy")
    return {"scope":"n19 lattice candidate graph only",
            "normalized_lower_squared":"1/13","positive_pivots":len(pivots),
            "positive_rods":42,"anchor_pairs":66,
            "weights": [str(we/total),str(ws/total),str(1/total)]}


if __name__=="__main__":
    print(json.dumps(verify(),indent=2))
