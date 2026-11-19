"""Check that every retained B=14 apex pattern gives a planar forced annulus."""
import argparse
from collections import Counter, defaultdict
from itertools import combinations
import json
from pathlib import Path

from verify_boundary_walk import B, apex_norm_ceiling, verify as check_patterns

NEIGHBOR_CEILINGS={8:833_896_000,9:905_600_000}


def edge(a,b):
    return tuple(sorted((a,b)))


def check_annulus(faces,outer,inner):
    if len(set(faces))!=len(faces):
        raise ValueError("duplicate annulus face")
    incidence=Counter(e for face in faces for e in combinations(face,2))
    boundary={edge(v[i],v[(i+1)%len(v)]) for v in (outer,inner) for i in range(len(v))}
    if {e for e,n in incidence.items() if n==1}!=boundary:
        raise ValueError("annulus has the wrong boundary")
    if any(n not in (1,2) for n in incidence.values()):
        raise ValueError("invalid annulus edge incidence")
    vertices=set(outer)|set(inner)
    if len(vertices)-len(incidence)+len(faces)!=0:
        raise ValueError("invalid annulus Euler characteristic")
    links={v:defaultdict(set) for v in vertices}
    for face in faces:
        for i,v in enumerate(face):
            a,b=face[(i+1)%3],face[(i+2)%3]
            links[v][a].add(b)
            links[v][b].add(a)
    for loop in (outer,inner):
        for i,v in enumerate(loop):
            g=links[v]
            end={loop[i-1],loop[(i+1)%len(loop)]}
            if {x for x,h in g.items() if len(h)==1}!=end or any(len(h)>2 for h in g.values()):
                raise ValueError("annulus link is not a path")
            work=[next(iter(end))]
            reached=set(work)
            while work:
                for x in g[work.pop()]-reached:
                    reached.add(x)
                    work.append(x)
            if reached!=set(g):
                raise ValueError("disconnected annulus link")


def verify():
    patterns,_=check_patterns()
    annuli=[]
    # If all d_i are 3 or 4, the link between the two boundary-face
    # apices is a point or one edge. Then every neighbor of the outer
    # boundary is a boundary-face apex, so at least eight are required.
    for p in patterns:
        if len(p)<8:
            continue
        q=[None]*B
        for j,block in enumerate(p):
            for i in block:q[i]=B+j
        faces=[tuple(sorted((i,(i+1)%B,q[i]))) for i in range(B)]
        inner=[]
        for i in range(B):
            if q[i]!=q[i-1]:
                inner.append(q[i])
                faces.append(tuple(sorted((i,q[i-1],q[i]))))
        if len(set(inner))!=len(p):
            raise ValueError("inner boundary repeats a vertex")
        check_annulus(faces,list(range(B)),inner)
        ceiling=min(apex_norm_ceiling(len(inner)),NEIGHBOR_CEILINGS.get(len(inner),10**9))
        annuli.append({"apex_pattern":p,"triangles":faces,
                       "inner_boundary":inner,"unplaced_vertices":13-len(inner),
                       "owner_norm_ceiling":ceiling})
    return annuli


if __name__=="__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--output",type=Path)
    a=p.parse_args()
    annuli=verify()
    print(f"PASS B=14: {len(annuli)} complete forced annuli when every outer degree is 3 or 4.")
    for low in (833_896_000,876_600_000,892_960_000,905_600_000):
        allowed=sum(record["owner_norm_ceiling"]>low for record in annuli)
        print(f"D1 >= {low}/1e9: {allowed} of these annuli retained.")
    if a.output:
        a.output.write_text(json.dumps({"annuli":annuli},separators=(",",":"))+"\n",encoding="utf-8")
