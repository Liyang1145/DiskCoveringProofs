"""Standalone standard-library partial-graph force/tree acceptance.

No NumPy, SciPy, Clarabel or mutable vertex-count globals are used here.
Explicit supplied edges, rational caps and radius are rechecked from graph faces.
"""
from pathlib import Path
from fractions import Fraction as F
from math import isqrt
from functools import lru_cache
from collections import Counter
import sys

if not __debug__:
    raise RuntimeError("Assertions must be enabled")
ROOT=Path(__file__).resolve().parent
ARCS=ROOT.parent.parent/"disk-cover-proof-library/external/pinned/cover20/proof_bundle/core"
sys.path.insert(0,str(ARCS))
from exact_arcs import QA,QB,arc_halfplane


def bits(mask):
    assert type(mask) is int and mask>0
    return [i for i in range(mask.bit_length()) if mask>>i&1]


def graph(B,N,masks):
    assert type(B) is int and B in (13,14)
    assert type(N) is int and B<=N<=21
    assert masks==sorted(set(masks)) and all(type(m)is int and m.bit_count()==3 and 0<m<(1<<N) for m in masks)
    faces=[bits(m) for m in masks]
    edges=[(i,B+i) for i in range(B)]+[(i,B+(i+1)%B) for i in range(B)]
    edges += [(B+N+k,B+j) for k,f in enumerate(faces) for j in f]
    V=B+N+len(faces)
    assert sorted({v for e in edges for v in e})==list(range(V))
    return faces,edges,V


def angle_bounds(B,N,faces,constants):
    D=constants["angle_scale"];A,C4,C6=constants["angle_caps"]
    assert type(D)is int and D>0 and 0<2*A<C4<C6<D//2
    adj=[{i} for i in range(N)]
    for f in faces:
        for v in f:
            adj[v].update(f)
    two=[set().union(*(adj[j] for j in adj[v])) for v in range(N)]
    mat=[[10**9]*B for _ in range(B)]
    for i in range(B):
        mat[i][i]=0;j=(i+1)%B
        mat[i][j]=min(mat[i][j],A-(D if j==0 else 0))
        mat[j][i]=min(mat[j][i],D if j==0 else 0)
    for i in range(B):
        near=adj[i]|adj[(i+1)%B]
        farther=two[i]|two[(i+1)%B]
        for j in range(i+1,B):
            endpoints={j,(j+1)%B}
            if near&endpoints:
                cap=C4
            elif farther&endpoints:
                cap=C6
            else:
                continue
            k=j-i
            if min(k,B-k)*A<=cap:
                continue
            fw=k*A<D-cap;bw=(B-k)*A<D-cap
            assert not(fw and bw),"necessary angle contradiction requires its own exclusion record"
            if fw:
                mat[i][j]=min(mat[i][j],cap)
            elif bw:
                mat[j][i]=min(mat[j][i],cap-D)
    for k in range(B):
        for i in range(B):
            for j in range(B):
                mat[i][j]=min(mat[i][j],mat[i][k]+mat[k][j])
    assert all(mat[i][i]==0 for i in range(B))
    return mat


def tighten(mat,lo,hi,D):
    B=len(mat)
    assert len(lo)==len(hi)==B-1
    lower=[F(0)]+list(map(F,lo));upper=[F(0)]+list(map(F,hi))
    nl=[max(lower[i]-F(mat[j][i],D) for i in range(B)) for j in range(B)]
    nu=[min(upper[i]+F(mat[i][j],D) for i in range(B)) for j in range(B)]
    if any(a>b for a,b in zip(nl,nu)):
        return None
    assert nl[0]<=0<=nu[0]
    return nl[1:],nu[1:]


def ceil_root(n):
    assert type(n)is int and n>=0
    v=isqrt(n)
    return v+(v*v<n)


@lru_cache(maxsize=256)
def tree(V,ed):
    adjacency=[[] for _ in range(V)]
    for k,(u,v) in enumerate(ed):
        assert 0<=u<V and 0<=v<V and u!=v
        adjacency[u].append((v,k));adjacency[v].append((u,k))
    parent=[None]*V;parent[0]=(-1,-1);order=[0];used=set()
    for u in order:
        for v,k in adjacency[u]:
            if parent[v] is None:
                parent[v]=(u,k);used.add(k);order.append(v)
    assert len(order)==V
    return parent,order,[k for k in range(len(ed)) if k not in used]


def force_margin(B,V,edges,lo,hi,certificate,U):
    assert set(certificate)=={"q","l","b","f"}
    Q=certificate["q"];la=certificate["l"];beta=certificate["b"];cycle=certificate["f"]
    assert type(Q)is int and 0<Q<=10**18
    assert len(la)==B-1 and len(beta)==2*(B-1)
    assert all(type(v)is int and v>=0 for v in la)
    assert all(type(v)is int for v in beta+cycle)
    parent,order,chords=tree(V,tuple(edges))
    assert len(cycle)==2*len(chords)
    aa=[];bb=[]
    for l,h in zip(lo,hi):
        a,b=arc_halfplane(l,h);aa.append(a);bb.append(b)
    balance=[[0,0] for _ in range(V)]
    for i in range(B-1):
        for axis in (0,1):
            value=la[i]*aa[i][axis]-beta[2*i+axis]*QA
            balance[i+1][axis]=value;balance[0][axis]-=value
    flow=[[0,0] for _ in edges]
    for j,k in enumerate(chords):
        u,v=edges[k]
        for axis in (0,1):
            value=cycle[2*j+axis]*QA
            flow[k][axis]=value;balance[u][axis]-=value;balance[v][axis]+=value
    for v in reversed(order[1:]):
        u,k=parent[v];sign=1 if edges[k][0]==v else -1
        for axis in (0,1):
            flow[k][axis]=sign*balance[v][axis]
            balance[u][axis]+=balance[v][axis];balance[v][axis]=0
    assert all(value==[0,0] for value in balance)
    divergence=[[0,0] for _ in range(V)]
    for (u,v),f in zip(edges,flow):
        for axis in (0,1):
            divergence[u][axis]+=f[axis];divergence[v][axis]-=f[axis]
    target=[[0,0] for _ in range(V)]
    for i in range(B-1):
        for axis in (0,1):
            target[i+1][axis]=la[i]*aa[i][axis]-beta[2*i+axis]*QA
            target[0][axis]-=target[i+1][axis]
    assert divergence==target
    normsum=sum(ceil_root(x*x+y*y) for x,y in flow)
    assert normsum>0
    work=0
    for i in range(B-1):
        x,y=beta[2*i:2*i+2]
        work+=la[i]*(bb[i]-aa[i][0]*(QB//QA))
        work-=(ceil_root((x*QA)**2+(y*QA)**2)-x*QA)*(QB//QA)
    return F(work*QA,QB*normsum)-U


def verify(B,N,masks,nodes,constants):
    faces,edges,V=graph(B,N,masks)
    mat=angle_bounds(B,N,faces,constants)
    D=constants["angle_scale"];U=F(constants["radius_upper"])
    lower=[F(-mat[i][0],D) for i in range(1,B)]
    upper=[F(mat[0][i],D) for i in range(1,B)]
    pending=[(0,lower,upper)];seen=set();counts=Counter();minimum=None
    while pending:
        index,lo,hi=pending.pop()
        assert type(index)is int and 0<=index<len(nodes) and index not in seen
        seen.add(index);node=nodes[index]
        assert isinstance(node,dict) and node["kind"] in ("EMPTY","SPLIT","DUAL")
        box=tighten(mat,lo,hi,D)
        if node["kind"]=="EMPTY":
            assert box is None
        else:
            assert box is not None
            lo,hi=box
            if node["kind"]=="DUAL":
                margin=force_margin(B,V,edges,lo,hi,node["certificate"],U)
                assert margin>0
                minimum=margin if minimum is None else min(minimum,margin)
            else:
                axis=node["axis"];cut=F(node["mid"]);children=node["children"]
                assert type(axis)is int and 0<=axis<B-1 and lo[axis]<cut<hi[axis]
                assert len(children)==2 and children[0]!=children[1]
                assert all(type(v)is int and 0<=v<len(nodes) for v in children)
                left=list(hi);right=list(lo)
                left[axis]=cut;right[axis]=cut
                pending.extend([(children[0],list(lo),left),(children[1],right,list(hi))])
        counts[node["kind"]]+=1
    assert seen==set(range(len(nodes))) and minimum is not None
    return {"verified":True,"nodes":len(seen),"counts":dict(counts),"minimum_margin":str(minimum),
            "vertices":V,"edges":len(edges)}
