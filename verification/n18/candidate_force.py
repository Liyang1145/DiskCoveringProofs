# SPDX-License-Identifier: MIT
"""Pinned adaptations of the existing rational rod force checker for n18."""
from fractions import Fraction as Q
from importlib.util import module_from_spec, spec_from_file_location
from itertools import combinations
from pathlib import Path
from compare_census import CAPS, caps

path=Path(__file__).resolve().parents[1]/"n16"/"force_exclusion.py"
spec=spec_from_file_location("n18_common_force",path)
module=module_from_spec(spec)
spec.loader.exec_module(module)
module.U=Q("0.290167717640566729113154525601061718306280885754041798808095")
module.CAPS=CAPS
S=module.S
need=module.need

def graph_data(b,faces):
    triples=[tuple(i for i in range(18) if mask>>i&1) for mask in faces]
    need(len(triples)==34-b and all(len(t)==3 for t in triples),"bad face list")
    edges=[]
    for i in range(b):
        edges.extend(((i,b+i),(i,b+(i+1)%b)))
    adj=[{i} for i in range(18)]
    for k,t in enumerate(triples):
        edges.extend((b+i,b+18+k) for i in t)
        for i,j in combinations(t,2):
            adj[i].add(j); adj[j].add(i)
    two=[set().union(*(adj[j] for j in a)) for a in adj]
    dist=[[0 if i==j else 10*S for j in range(b)] for i in range(b)]
    def put(i,j,w):
        dist[i][j]=min(dist[i][j],w)
    for i in range(b):
        j=(i+1)%b
        put(i,j,CAPS[0]-(S if j==0 else 0))
        put(j,i,S if j==0 else 0)
    for i,j in combinations(range(b),2):
        ends={j,(j+1)%b}
        if (adj[i]|adj[(i+1)%b])&ends:
            cap=CAPS[1]
        elif (two[i]|two[(i+1)%b])&ends:
            cap=CAPS[2]
        else:
            continue
        k=j-i
        if k*CAPS[0]<S-cap:
            put(i,j,cap)
        if (b-k)*CAPS[0]<S-cap:
            put(j,i,cap-S)
    for k in range(b):
        for i in range(b):
            for j in range(b):
                dist[i][j]=min(dist[i][j],dist[i][k]+dist[k][j])
    need(all(dist[i][i]>=0 for i in range(b)),"empty root angle domain")
    return edges,dist


# Shared replay functions refer to their own module's pinned U.
module.graph_data=graph_data
module.check_caps=caps
f=module
