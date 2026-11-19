"""Enumerate the B=14 strips with exactly ten exposed inner vertices."""
import argparse
from collections import Counter
from itertools import combinations
import json
from pathlib import Path

from verify_b14_incidence import profiles
from verify_boundary_walk import B, apex_norm_ceiling, verify as check_patterns
from verify_boundary_residual import check_annulus
from verify_expanded_core_count import LOWER


def compositions(total, length):
    """Every placement of total indistinguishable entries in length gaps."""
    end=total+length-1
    for bars in combinations(range(end),length-1):
        ends=(-1,*bars,end)
        yield tuple(b-a-1 for a,b in zip(ends,ends[1:]))


def annulus(pattern,extra):
    apex=[-1]*B
    for label,edges in enumerate(pattern,B):
        for i in edges:
            apex[i]=label
    outer=list(range(B))
    faces=[tuple(sorted((i,(i+1)%B,apex[i]))) for i in outer]
    inner=[]
    degree=[3]*B
    free=B+len(pattern)
    extras=iter(extra)
    for i in outer:
        q=apex[i]
        previous=apex[i-1]
        if previous==q:
            continue
        count=next(extras)
        middle=list(range(free,free+count))
        free+=count
        degree[i]=4+count
        path=[previous,*middle,q]
        inner.extend(path[1:])
        faces.extend(tuple(sorted((i,a,b))) for a,b in zip(path,path[1:]))
    if len(inner)!=10 or len(set(inner))!=10 or sum(degree)!=52 or next(extras,None) is not None:
        raise ValueError("invalid ten-vertex boundary walk")
    check_annulus(faces,outer,inner)
    return {"apex_pattern":pattern,"outer_degrees":degree,"inner_cycle":inner,
            "triangles":faces,"unplaced_vertices":3}


def orbit_key(degrees):
    return min(row[i:]+row[:i] for row in (degrees,degrees[::-1]) for i in range(B))


def verify(source):
    old=set(profiles(source))
    patterns,_=check_patterns()
    visited=Counter()
    retained=Counter()
    degree_profiles=set()
    representatives={}
    words=set()
    catalog=[]
    for pattern in patterns:
        m=len(pattern)
        if m>10 or LOWER>=apex_norm_ceiling(m):
            continue
        for extra in compositions(10-m,m):
            record=annulus(pattern,extra)
            visited[m]+=1
            degree=tuple(sorted(record["outer_degrees"]))
            if degree not in old:
                continue
            retained[m]+=1
            degree_profiles.add(degree)
            word=tuple(record["outer_degrees"])
            if word in words:
                raise ValueError("two strips have the same fixed-index degree word")
            words.add(word)
            catalog.append(record)
            key=orbit_key(word)
            representatives.setdefault(key,len(catalog)-1)
    for key,index in representatives.items():
        if orbit_key(tuple(catalog[index]["outer_degrees"]))!=key:
            raise ValueError("invalid rotation and reflection quotient")
    print(f"PASS B=14: D1 >= {LOWER}/1e9 and the core cycle give outer degree sum 52.")
    print(f"PASS B=14: {len(catalog)} labelled strips out of {sum(visited.values())} and {len(degree_profiles)} degree profiles.")
    print(f"PASS B=14: {len(representatives)} strips up to rotation and reflection.")
    for m in sorted(visited):
        print(f"{m} apices: {retained[m]} of {visited[m]} strips.")
    return {"owner_norm_floor":LOWER,"degree_sum":52,
            "degree_profiles":sorted(degree_profiles),"strips":catalog,
            "orbit_representative_indices":[representatives[key] for key in sorted(representatives)]}


if __name__=="__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("source",type=Path)
    p.add_argument("--output",type=Path)
    a=p.parse_args()
    report=verify(a.source)
    if a.output:
        a.output.write_text(json.dumps(report,separators=(",",":"))+"\n",encoding="utf-8")
