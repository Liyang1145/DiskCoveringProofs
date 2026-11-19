#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
"""Recheck numeric external witnesses for specified remaining native n17 orbits."""
from argparse import ArgumentParser
from collections import Counter
from fractions import Fraction as Q
import gzip
from hashlib import sha256
from itertools import combinations, permutations, product
import json
from pathlib import Path

import candidate_data_replay as candidate
from candidate_data_replay import f, verify_record

FOREST_SHA="0bb19fb51bf7a9d99f9b149d5040352200138e46b288383d17c2a6dce973cb1d"
UNPAID={12:(612,616,621,622,624,628,630),13:(169,170,198,199)}
N=17


def degrees(faces):
    ans=[set() for _ in range(N)]
    for face in faces:
        for i,j in combinations(face,2):
            ans[i].add(j)
            ans[j].add(i)
    return list(map(len,ans))


def equivalent(b,src,dsrc,want,dwant):
    # Enumerate every cyclic orientation of the owners, and all interior
    # bijections preserving degree. A graph isomorphism must preserve degree.
    if sorted(dsrc[b:])!=sorted(dwant[b:]):
        return False
    groups={}
    for i in range(b,N):
        groups.setdefault(dsrc[i],[]).append(i)
    source=list(groups.values())
    dest=[[i for i in range(b,N) if dwant[i]==dsrc[group[0]]] for group in source]
    for off in range(b):
        for sign in (-1,1):
            name=[(off+sign*i)%b for i in range(b)] + [None]*(N-b)
            if any(dsrc[i]!=dwant[name[i]] for i in range(b)):
                continue
            for options in product(*(permutations(g) for g in dest)):
                for group,chosen in zip(source,options):
                    for i,j in zip(group,chosen):
                        name[i]=j
                if tuple(sorted(sum(1<<name[i] for i in face) for face in src))==want:
                    return True
    return False


def verify_tree(b,faces,nodes):
    masks=sorted(sum(1<<i for i in face) for face in faces)
    graph,dist=f.graph_data(b,masks)
    edges=([(i,b+i) for i in range(b)]+[(i,b+(i+1)%b) for i in range(b)]
           +[(b+N+k,b+i) for k,face in enumerate(faces) for i in face])
    renum={b+N+k:b+N+masks.index(sum(1<<i for i in face)) for k,face in enumerate(faces)}
    f.need(len(graph)==len(edges)==2*b+3*(32-b) and
           {frozenset(renum.get(i,i) for i in e) for e in edges}==
           {frozenset(e) for e in graph},"witness graph mismatch")
    seen=set()
    counts=Counter()
    margins=[]
    def walk(i,lo,hi):
        f.need(type(i) is int and 0<=i<len(nodes) and i not in seen,
               "bad or duplicate node index")
        seen.add(i)
        lo,hi=f.tighten(dist,lo,hi)
        node=nodes[i]
        kind=node["kind"]
        counts[kind]+=1
        if kind=="EMPTY":
            f.need(any(a>b for a,b in zip(lo,hi)),"false empty")
            return
        f.need(all(a<=b for a,b in zip(lo,hi)),"unexpected empty box")
        if kind=="SPLIT":
            axis=node["axis"]
            f.need(type(axis) is int and len(node["children"])==2,"malformed split")
            for k,(l,h) in zip(node["children"],f.children(lo,hi,axis+1,Q(node["mid"])),strict=True):
                walk(k,l,h)
        elif kind=="DUAL":
            lam=node["lambda_num"]
            f.need(all(type(i) is int and i>=0 for i in lam),"invalid multipliers")
            margins.append(f.verify_leaf(b,edges,lo,hi,[[i*10**21 for i in lam],node["force_num"]]))
        else:
            raise ArithmeticError("unknown or non-permitted noncandidate leaf")
    walk(0,*f.rootbox(b))
    f.need(len(seen)==len(nodes) and bool(margins),"incomplete witness tree")
    return counts,min(margins)


def check(census_dir,forest,negative_controls=False,wanted_orbits=None):
    f.CAPS=candidate.TREE_CAPS
    f.check_caps()
    f.PREC,f.ROOT_PREC=10**36,10**45
    f.support.cache_clear()
    wanted_orbits = UNPAID if wanted_orbits is None else wanted_orbits
    targets={}
    for b,indices in wanted_orbits.items():
        d=json.loads((Path(census_dir)/f"n17-B{b}.json").read_text())
        verify_record(d,b,"dfs")
        for i in indices:
            masks=tuple(d["survivors"][i]["faces"])
            targets[b,i]=(masks,degrees([[k for k in range(N) if v>>k&1] for v in masks]))
    raw=Path(forest).read_bytes()
    f.need(sha256(raw).hexdigest()==FOREST_SHA,"bad external numeric forest digest")
    matched={}
    node_counts=Counter()
    margin=[]
    with gzip.open(forest,"rt") as src:
        header=json.loads(next(src))
        f.need(header["version"]==1,"wrong forest version")
        for line in src:
            r=json.loads(line)
            b=r["B"]
            wanted=[(i,v) for (c,i),v in targets.items() if b==c]
            if not wanted:
                continue
            faces=r["faces"]
            f.need(r["version"]==1 and len(faces)==32-b and r["I"]==N-b and
                   all(len(face)==len(set(face))==3 and all(type(i) is int and 0<=i<N for i in face)
                       for face in faces),"malformed numeric forest graph")
            dsrc=degrees(faces)
            for i,(masks,dwant) in wanted:
                if equivalent(b,faces,dsrc,masks,dwant):
                    key=b,i
                    f.need(key not in matched,"multiple witnesses matched one native orbit")
                    counts,m=verify_tree(b,faces,r["nodes"])
                    node_counts.update(counts)
                    margin.append(m)
                    matched[key]={"owners":b,"index":i,"source_residual_index":r["residual_index"],
                                  "node_counts":dict(counts),"minimum_margin_display":float(m)}
    f.need(matched.keys()==targets.keys(),"missing native orbit data or witness")
    controls=0
    if negative_controls and targets:
        b,i=next(iter(targets))
        masks,d=targets[b,i]
        bad=tuple(sorted(masks[:-1]+(masks[0],)))
        # A duplicate face is never equivalent to a distinct-face native target.
        faces=[[k for k in range(N) if v>>k&1] for v in bad]
        f.need(not equivalent(b,faces,degrees(faces),masks,d),"duplicate face accepted")
        controls+=1
    return dict(status="specified_noncandidate_orbits_excluded",forest_witness_sha256=FOREST_SHA,
                count=len(matched),counts=dict(node_counts),
                minimum_exact_force_margin_display=float(min(margin)) if margin else None,
                negative_controls_rejected=controls,
                matches=[matched[k] for k in sorted(matched)])


if __name__=="__main__":
    ap=ArgumentParser(description=__doc__)
    ap.add_argument("census",type=Path)
    ap.add_argument("forest",type=Path)
    ap.add_argument("--negative-controls",action="store_true")
    a=ap.parse_args()
    print(json.dumps(check(a.census,a.forest,a.negative_controls),indent=2))
