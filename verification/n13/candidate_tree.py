# SPDX-License-Identifier: MIT
"""Independent candidate-graph replay of pinned split/force DATA only.

Generate with --convert using the separately downloaded upstream data; replay
requires only the bundled compact tree and the native census and root checks.
"""
import argparse, gzip, json
from hashlib import sha256
from pathlib import Path
from fractions import Fraction as Q
from collections import Counter

from force_prototype import (
    CANDIDATE_INDEX, CANDIDATE_TEST, PREC, S, PI, trig, need, load_census,
    verify_leaf, fix_flow, check_candidate_theorem, candidate_data,
)

HERE = Path(__file__).resolve().parent
SOURCE_HASH = "54dee4b47b3c307064c30cf2f93f5e9cc7a755b3f5fb7aeeb6ae859f7996e51a"
CAP = Q(1127,10000)
B = 10
ROOT_BOX = Q(0), Q(1)


def geometry(census):
    candidate_data()  # Also locates the repository tools module.
    from check_native_n13_root import ACTIVE, INACTIVE
    source_faces = sorted(set(ACTIVE+INACTIVE))
    need(len(source_faces)==14,"candidate face count")
    mapped = census["survivors"][CANDIDATE_INDEX]["faces"]
    need(tuple(mapped)==candidate_data()[1][0][0],"candidate graph/census mismatch")
    # Retain the original q0 gauge of the isolated root. Each edge and
    # anchor correspondence has been verified in candidate_data.
    edges = [(i,10+i) for i in range(10)]+[(i,10+(i+1)%10) for i in range(10)]
    edges += [(23+j,10+i) for j,face in enumerate(source_faces) for i in face]
    need(len(edges)==62,"candidate rod count")
    return source_faces,edges


def tighten(lo,hi):
    # Difference closure for 0<=u_(i+1)-u_i<=CAP plus u0=0,u10=1.
    # This chain admits a complete forward/backward prefix minimum pass.
    lo,hi = list(lo)+[Q(1)],list(hi)+[Q(1)]
    for i in range(1,11):
        hi[i]=min(hi[i],hi[i-1]+CAP)
        lo[i]=max(lo[i],lo[i-1])
    for i in range(9,-1,-1):
        lo[i]=max(lo[i],lo[i+1]-CAP)
        hi[i]=min(hi[i],hi[i+1])
    if any(a>b for a,b in zip(lo,hi)):
        return None
    return tuple(lo[:10]),tuple(hi[:10])


def local(lo,hi):
    rho,maps=candidate_data()
    anchors=maps[0][4]
    total=Q(0)
    for i,(x,y) in enumerate(anchors[1:],1):
        need(0<=hi[i]-lo[i]<Q(1,2),"bad local arc width")
        bounds=[]
        for u in (lo[i],hi[i]):
            a,b=trig(u,0),trig(u,1)
            bounds.append(min(x*t for t in a)+min(y*t for t in b)-2*rho)
        lower=min(bounds)
        need(lower>0,"local endpoints must lie in positive hemisphere")
        total+=max(Q(0),2-2*lower)
    need(total<=Q(1,64),"candidate box exceeds exact isolation radius")


def check_tree(census,nodes,packed):
    faces,edges=geometry(census)
    need(trig(CAP/2,1)[0]>CANDIDATE_TEST,"candidate cap too low")
    check_candidate_theorem()
    seen=set()
    goals=Counter()
    result=[None]*len(nodes)
    def go(idx,lo,hi):
        need(type(idx) is int and 0<=idx<len(nodes) and idx not in seen,"bad branch index")
        seen.add(idx)
        n=nodes[idx]
        tag=n[0] if packed else n["kind"]
        goals[tag]+=1
        box=tighten(lo,hi)
        if tag=="EMPTY":
            need(box is None and (not packed or len(n)==1),"nonempty domain")
            result[idx]=[tag]
            return
        need(box is not None,"unrecorded empty domain")
        lo,hi=box
        if tag=="SPLIT":
            if packed:
                need(len(n)==5,"bad packed split")
                i,q,a,b=n[1:]
            else:
                i=n["axis"]+1
                q=n["mid"]
                a,b=n["children"]
            q=Q(q)
            need(type(i) is int and 0<i<10 and lo[i]<q<hi[i] and a!=b,"bad split")
            result[idx]=[tag,i,str(q),a,b]
            go(a,lo,hi[:i]+(q,)+hi[i+1:])
            go(b,lo[:i]+(q,)+lo[i+1:],hi)
        elif tag=="LOCAL":
            need(not packed or len(n)==1,"bad local leaf")
            local(lo,hi)
            result[idx]=[tag]
        elif tag=="DUAL":
            if packed:
                need(len(n)==2,"bad force leaf")
                cert=n[1]
            else:
                lam=n["lambda_num"]
                flow=[tuple(round(Q(x*PREC,10**36)) for x in row) for row in n["force_num"]]
                cert=lam,fix_flow(edges,flow,B)
            verify_leaf(B,edges,lo,hi,cert,CANDIDATE_TEST)
            result[idx]=[tag,cert]
        else:
            raise ArithmeticError(f"unknown leaf {tag}")
    go(0,(Q(0),)*10,(Q(0),)+(Q(1),)*9)
    need(len(seen)==len(nodes)==1831 and goals=={"SPLIT":915,"DUAL":837,"LOCAL":79},
         "candidate accounting")
    return result,dict(goals)


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--census",required=True)
    ap.add_argument("--convert",type=Path)
    ap.add_argument("--tree",type=Path,default=HERE/"candidate-712.json.gz")
    args=ap.parse_args()
    census=load_census(args.census)
    need(census["B"]==10,"candidate requires B10 census")
    if args.convert:
        raw=args.convert.read_bytes()
        need(sha256(raw).hexdigest()==SOURCE_HASH,"unpinned split/force data")
        d=json.loads(gzip.decompress(raw))
        need(d["schema"]=="candidate-arc-force-tree-v1" and Q(d["cap"])==CAP and
             d["flow_scale"]==10**36 and d["lambda_scale"]==PREC,"source schema")
        faces,_=geometry(census)
        need([tuple(x) for x in d["all_faces"]]==faces,"wrong source topology")
        tree,goals=check_tree(census,d["nodes"],False)
        with gzip.GzipFile(args.tree,"wb",mtime=0) as f:
            f.write((json.dumps(tree,separators=(",",":"))+"\n").encode())
    else:
        tree=json.loads(gzip.decompress(args.tree.read_bytes()))
        _,goals=check_tree(census,tree,True)
    print("N13 CANDIDATE 712 GLOBAL ARC COVER VERIFIED",goals)


if __name__=="__main__":
    main()
