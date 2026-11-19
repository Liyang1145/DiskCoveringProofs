# SPDX-License-Identifier: MIT
"""Native n=19 exact force verifier; optional SciPy LP generates untrusted hints."""
from collections import deque
from fractions import Fraction as Q
from functools import lru_cache
from itertools import combinations
from math import factorial, isqrt
import argparse
import json

S = 100000
CAPS = (8946, 18717, 31284)
U = Q(27735009811263,10**14)
PREC = 10**15
ROOT_PREC = 10**24
ZERO = (0,0)


def need(ok, reason):
    if not ok:
        raise ArithmeticError(reason)


def add(p,q):
    return (p[0]+q[0],p[1]+q[1])


def sub(p,q):
    return (p[0]-q[0],p[1]-q[1])


def scale(s,p):
    return (s*p[0],s*p[1])


def atan(n):
    p=sum(Q((-1)**j,(2*j+1)*n**(2*j+1)) for j in range(24))
    return p,p+Q(1,49*n**49)


q,r=atan(5),atan(239)
PI=(16*q[0]-4*r[1],16*q[1]-4*r[0])


@lru_cache(maxsize=4096)
def trig(turn, parity):
    """Enclose cos (0) or sin (1), evaluated at 2*pi*turn."""
    turn=Q(turn)%1
    if turn>Q(1,2):
        turn-=1
    x=2*turn*(PI[0]+PI[1])/2
    need(abs(x)<4,"Taylor domain")
    y=sum((-1)**j*x**(2*j+parity)/factorial(2*j+parity) for j in range(24))
    # Taylor at degree 47 (cos odd coefficient zero) or 47 (sin).
    e=Q(4**48,factorial(48))+abs(turn)*(PI[1]-PI[0])
    return y-e,y+e


def check_caps():
    a,c,d=(Q(x,2*S) for x in CAPS)
    need(U>0 and 13*U*U>1,"test upper bound")
    for t,k in [(a,1),(c,2),(d,3)]:
        need(trig(t,1)[0]>k*U,"angular cap must be conservative")


@lru_cache(maxsize=4096)
def support(l,h):
    need(0<=l<=h<=1,"bad arc")
    a0,a1=trig((l+h)/2,0)
    b0,b1=trig((l+h)/2,1)
    a=Q(round(PREC*(a0+a1)/2),PREC); b=Q(round(PREC*(b0+b1)/2),PREC)
    err=max(abs(a-a0),abs(a-a1))+max(abs(b-b0),abs(b-b1))
    c=trig((h-l)/2,0)[0]-err
    return (a,b),Q(c*PREC//1,PREC)


def graph_data(b,faces):
    triples=[tuple(i for i in range(19) if mask>>i&1) for mask in faces]
    need(len(triples)==36-b and all(len(t)==3 for t in triples),"bad face list")
    edges=[]
    for i in range(b):
        edges.extend(((i,b+i),(i,b+(i+1)%b)))
    adj=[{i} for i in range(19)]
    for k,t in enumerate(triples):
        edges.extend((b+i,b+19+k) for i in t)
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


def tighten(dist,lo,hi):
    b=len(dist)
    newlo=tuple(max(lo[j]-Q(dist[i][j],S) for j in range(b)) for i in range(b))
    newhi=tuple(min(hi[j]+Q(dist[j][i],S) for j in range(b)) for i in range(b))
    return newlo,newhi


def norm_hi(v):
    z=(v[0]**2+v[1]**2)*ROOT_PREC**2
    n=isqrt(z//1)
    return Q(n+(n*n<z),ROOT_PREC)


def divergence(edges,flow):
    net=[ZERO]*(max(max(e) for e in edges)+1)
    for (i,j),f in zip(edges,flow,strict=True):
        net[i]=add(net[i],f);net[j]=sub(net[j],f)
    return net


def verify_leaf(b,edges,lo,hi,cert):
    """The certificate contains only edge flow and nonnegative multipliers."""
    lam,flow=cert
    need(len(lam)==b-1 and all(type(x) is int and x>=0 for x in lam),
         "invalid support multipliers")
    need(len(flow)==len(edges) and all(len(f)==2 and all(type(x) is int for x in f) for f in flow),
         "invalid edge flow")
    flow=[scale(Q(1,PREC),v) for v in flow]
    net=divergence(edges,flow)
    need(all(p==ZERO for p in net[b:]),"nonanchor force imbalance")
    lhs=Q(0)
    for i in range(1,b):
        a,c=support(lo[i],hi[i]); mu=Q(lam[i-1],PREC)
        d=sub(scale(mu,a),net[i])
        lhs+=mu*(c-a[0])+d[0]-norm_hi(d)
    rhs=U*sum(norm_hi(f) for f in flow)
    need(lhs>rhs,"no strict force separation")
    return lhs-rhs


def fix_flow(edges,flow,b):
    """Fix integer nonanchor divergence using a spanning tree to anchor 0."""
    net=divergence(edges,flow)
    adj=[[] for _ in net]
    for k,(i,j) in enumerate(edges):
        adj[i].append((j,k,1));adj[j].append((i,k,-1))
    parent={0:None}; q=deque([0]); order=[]
    while q:
        i=q.popleft();order.append(i)
        for j,k,d in adj[i]:
            if j not in parent:
                parent[j]=(i,k,-d);q.append(j)
    need(len(order)==len(net),"disconnected rod graph")
    for i in reversed(order[1:]):
        if i<b:
            continue
        j,k,d=parent[i]
        flow[k]=sub(flow[k],scale(d,net[i]))
        net[j]=add(net[j],net[i])
    return flow


def generate_hint(b,edges,lo,hi,directions=32):
    # Numerical LP proposes forces only. Every returned force is independently
    # tested using exact rational arithmetic and exact graph divergence.
    from math import cos, pi, sin
    from scipy.optimize import linprog
    from scipy.sparse import coo_matrix

    dseq=[(cos(2*pi*j/directions),sin(2*pi*j/directions)) for j in range(directions)]
    nodes=max(max(e) for e in edges)+1
    rows,cols,values,rhs=[],[],[],[]
    t=2*(nodes-1)
    def cp(i,d):
        row=len(rhs)
        if i==0:
            return d[0]
        for ax in (0,1):
            rows.append(row);cols.append(2*(i-1)+ax);values.append(float(d[ax]))
        return 0
    for i,j in edges:
        for d in dseq:
            adjust=cp(i,d)+cp(j,scale(-1,d))
            rows.append(len(rhs));cols.append(t);values.append(-1.)
            rhs.append(-adjust)
    for i in range(1,b):
        a,c=support(lo[i],hi[i])
        rhs.append(float(-c-cp(i,scale(-1,a))))
        for d in dseq:
            rhs.append(1.-cp(i,d))
    mat=coo_matrix((values,(rows,cols)),shape=(len(rhs),t+1)).tocsr()
    opt=linprog([0.]*t+[1.],A_ub=mat,b_ub=rhs,
                bounds=[(None,None)]*t+[(0,None)],method="highs")
    if not opt.success or opt.fun<=float(U):
        return None
    mul=[max(0.,-x) for x in opt.ineqlin.marginals]
    flows=[]
    for k in range(len(edges)):
        vals=mul[k*directions:(k+1)*directions]
        flows.append(tuple(round(PREC*sum(m*d[j] for m,d in zip(vals,dseq)))
                           for j in (0,1)))
    base=len(edges)*directions
    lam=[round(PREC*mul[base+(i-1)*(directions+1)]) for i in range(1,b)]
    cand=lam,fix_flow(edges,flows,b)
    try:
        verify_leaf(b,edges,lo,hi,cand)
    except ArithmeticError:
        return None
    return cand


def rootbox(b):
    return (Q(0),)*b,(Q(0),)+(Q(1),)*(b-1)


def children(lo,hi,i,mid):
    need(type(i) is int and 0<i<len(lo) and lo[i]<mid<hi[i],"invalid split")
    return ((lo,hi[:i]+(mid,)+hi[i+1:]), (lo[:i]+(mid,)+lo[i+1:],hi))


def build_tree(b,edges,dist,depth=4,directions=32):
    def go(lo,hi,level):
        lo,hi=tighten(dist,lo,hi)
        if any(a>c for a,c in zip(lo,hi)):
            return ["empty"]
        cand=generate_hint(b,edges,lo,hi,directions)
        if cand is not None:
            return ["force",cand]
        if level==depth:
            raise ArithmeticError("generation stopped with unresolved angle box")
        i=max(range(1,b),key=lambda j:hi[j]-lo[j])
        mid=(lo[i]+hi[i])/2
        return ["split",i,str(mid),*[go(a,c,level+1) for a,c in children(lo,hi,i,mid)]]
    return go(*rootbox(b),0)


def verify_tree(b,faces,tree):
    check_caps()
    edges,dist=graph_data(b,faces)
    goals={"force":0,"empty":0,"split":0}
    def go(lo,hi,node):
        lo,hi=tighten(dist,lo,hi)
        tag=node[0]
        need(tag in goals,"unknown node type")
        goals[tag]+=1
        if tag=="empty":
            need(len(node)==1 and any(a>c for a,c in zip(lo,hi)),"false empty node")
        elif tag=="force":
            need(len(node)==2 and all(a<=c for a,c in zip(lo,hi)),"invalid force node")
            verify_leaf(b,edges,lo,hi,node[1])
        else:
            need(len(node)==5 and all(a<=c for a,c in zip(lo,hi)),"invalid split node")
            for (a,c),nt in zip(children(lo,hi,node[1],Q(node[2])),node[3:],strict=True):
                go(a,c,nt)
    go(*rootbox(b),tree)
    return goals


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--generate")
    ap.add_argument("--indices",nargs="+",type=int)
    ap.add_argument("--spread",type=int,help="choose evenly spaced census indices")
    ap.add_argument("--range",dest="index_range",nargs=2,type=int,
                    help="choose consecutive indices [start,stop)")
    ap.add_argument("--depth",type=int,default=4)
    ap.add_argument("--directions",type=int,default=32)
    ap.add_argument("--report",help="write per-graph disposition even on incomplete batch")
    ap.add_argument("--census",help="bind checked certificates to this local canonical list")
    ap.add_argument("certificates")
    args=ap.parse_args()
    if args.generate:
        check_caps()
        with open(args.generate) as f:
            census=json.load(f)
        b=census["B"]
        records=[]
        entries=[]
        count=len(census["survivors"])
        choices=args.indices
        if args.spread is not None:
            need(1<args.spread<=count,"bad spread")
            choices=[j*(count-1)//(args.spread-1) for j in range(args.spread)]
        if args.index_range is not None:
            choices=list(range(*args.index_range))
        need(choices and len(choices)==len(set(choices)) and
             all(0<=j<count for j in choices),"bad index selection")
        for index in choices:
            faces=census["survivors"][index]["faces"]
            try:
                tree=build_tree(b,*graph_data(b,faces),args.depth,args.directions)
                goals=verify_tree(b,faces,tree)
            except ArithmeticError as err:
                entries.append({"index":index,"status":"unresolved","reason":str(err)})
                print(f"graph {index}: unresolved ({err})",flush=True)
                continue
            records.append({"index":index,"owners":b,"faces":faces,"tree":tree})
            entries.append({"index":index,"status":"excluded","replay":goals})
            print(f"graph {index}: {goals}",flush=True)
        with open(args.certificates,"w") as f:
            json.dump(records,f,separators=(",",":"))
            f.write("\n")
        if args.report:
            with open(args.report,"w") as f:
                json.dump({"owners":b,"requested":len(choices),"certified":len(records),
                           "unresolved":len(choices)-len(records),"entries":entries},f,indent=2)
                f.write("\n")
        if len(records)!=len(choices):
            raise SystemExit(2)
    else:
        with open(args.certificates) as f:
            records=json.load(f)
        need(bool(records),"empty certificate collection")
        local=None
        if args.census:
            with open(args.census) as f:
                local=json.load(f)
        seen=set()
        for rec in records:
            key=(rec["owners"],rec["index"])
            need(key not in seen,"duplicate claimed graph")
            seen.add(key)
            if local is not None:
                need(local["B"]==rec["owners"] and 0<=rec["index"]<len(local["survivors"])
                     and local["survivors"][rec["index"]]["faces"]==rec["faces"],
                     "certificate graph is not the specified native orbit")
            goals=verify_tree(rec["owners"],rec["faces"],rec["tree"])
            print(f'graph {rec["index"]}: {goals}')


if __name__=="__main__":
    main()
