# SPDX-License-Identifier: MIT
"""Native hybrid checker of the pinned n18 candidate tree's numeric witnesses."""
import argparse
from collections import Counter
from fractions import Fraction as Q
import gzip
from hashlib import sha256
import json
from pathlib import Path

from anchor_isolation import run as isolation
from candidate_force import f
from compare_census import candidate_code, load
from diskcover_n18_algebraic import FACES, SHA, isolate_radius, root_certificate

TREE_SHA = "b0b5add76b82c2682e8447d7721860524fcaafe158de1181fc71ffa1472a3c2b"
B = 12
TARGET = Q(7,60)
RHO = Q(1,10**80)


def anchor_bound(lo,hi,mid):
    """Upper bound squared displacement in ORIGINAL q0 gauge, or None."""
    ds=Q(0)
    for i,(l,h) in enumerate(zip(lo[1:],hi[1:])):
        if h-l>=Q(1,2):
            return None
        def dotlower(turn):
            return sum(min(a*u,a*v,b*u,b*v)
                       for j,x in enumerate(mid[i])
                       for a,b in [(x-RHO,x+RHO)]
                       for u,v in [f.trig(turn,j)])
        if dotlower((l+h)/2)<=0:
            return None
        ds+=2-2*min(dotlower(l),dotlower(h))
    return ds


def original_edges():
    return ([(i,B+i) for i in range(B)]
        + [(i,B+(i+1)%B) for i in range(B)]
        + [(B+18+k,B+i) for k,face in enumerate(FACES) for i in face])


def check(candidate,census,tree_path, negative_controls=False):
    f.check_caps()
    f.need(isolation(candidate)["anchor_distance_bound"]=="7/60","missing local proof")
    raw=Path(candidate).read_bytes()
    f.need(sha256(raw).hexdigest()==SHA,"candidate file hash mismatch")
    x,q,boxes=root_certificate(json.loads(raw))
    f.need(80 in boxes and Q(isolate_radius(x,q)[1])==f.U,"force target binding")
    mid=[(Q(x[i],q),Q(x[i+1],q)) for i in range(0,22,2)]

    key=candidate_code()
    orbits,_=load(Path(census),12,"dfs")
    f.need(key in orbits,"candidate missing from native census")
    raw=Path(tree_path).read_bytes()
    f.need(sha256(raw).hexdigest()==TREE_SHA,"source tree data hash mismatch")
    tree=json.loads(gzip.decompress(raw))
    f.need(tree.get("version")==1 and tree["faces"]==[list(row) for row in FACES],
           "mismatched original face labels")
    faces=sorted(sum(1<<i for i in face) for face in FACES)
    graph,dist=f.graph_data(B,faces)
    edges=original_edges()
    f.need(graph and len(edges)==90,"incorrect native graph size")
    # Interior face witness indices differ across face sorting. Canonicalize
    # one integer permutation of those indices before comparing rod sets.
    renum={B+18+k:B+18+faces.index(sum(1<<i for i in face))
           for k,face in enumerate(FACES)}
    f.need({frozenset(renum.get(x,x) for x in e) for e in edges}
           =={frozenset(e) for e in graph},"original rod graph differs from native graph")

    nodes=tree["nodes"]
    seen=set()
    counts=Counter()
    weakest=None
    max_local=Q(0)
    prior_prec,prior_root=f.PREC,f.ROOT_PREC
    f.PREC,f.ROOT_PREC=10**36,10**45
    f.support.cache_clear()
    def walk(idx,lo,hi):
        nonlocal weakest,max_local
        f.need(type(idx) is int and 0<=idx<len(nodes) and idx not in seen,"invalid or duplicate tree node")
        seen.add(idx)
        lo,hi=f.tighten(dist,lo,hi)
        f.need(all(a<=b for a,b in zip(lo,hi)),"source nonempty node now outside tightened root")
        node=nodes[idx]
        kind=node["kind"]
        counts[kind]+=1
        if kind=="SPLIT":
            f.need(type(node["axis"]) is int,"malformed split axis")
            axis=node["axis"]+1
            m=Q(node["mid"])
            children=f.children(lo,hi,axis,m)
            f.need(len(node["children"])==2,"split arity")
            for j,(l,h) in zip(node["children"],children,strict=True):
                walk(j,l,h)
        elif kind=="DUAL":
            # Recompute support halfplanes and exact divergence. Treat supplied
            # lambda/flows as hints only; derive support offsets independently.
            lam=node["lambda_num"]
            f.need(all(type(i) is int and i>=0 for i in lam),"malformed multiplier")
            margin=f.verify_leaf(B,edges,lo,hi,
                                 [[i*10**21 for i in lam],node["force_num"]])
            weakest=margin if weakest is None else min(weakest,margin)
        elif kind=="LOCAL":
            v=anchor_bound(lo,hi,mid)
            f.need(v is not None and v<=TARGET**2,"original-gauge local box exceeds 7/60")
            max_local=max(max_local,v)
        else:
            raise ArithmeticError("unknown or unresolved candidate node")

    try:
        walk(0,*f.rootbox(B))
        f.need(len(seen)==len(nodes),"unreachable nodes")
        f.need(counts["DUAL"]>0 and counts["LOCAL"]>0,"missing proof type")
        saved_counts=dict(counts)
        saved_size=len(seen)
        f.need(weakest>Q(2,10**8),"force margin below the reporting floor")
        f.need(max_local<Q(17,1250),"local displacement above the reporting ceiling")
        controls=0
        if negative_controls:
            seen.clear()
            nodes[0]["children"][0]=0
            try:
                walk(0,*f.rootbox(B))
            except ArithmeticError as exc:
                f.need("invalid or duplicate" in str(exc),"wrong cyclic tree rejection")
                controls+=1
            else:
                raise ArithmeticError("cyclic tree unexpectedly accepted")
            f.need(anchor_bound(*f.rootbox(B),mid) is None,"unrestricted root accepted as local")
            controls+=1
            try:
                f.verify_leaf(B,edges,*f.rootbox(B),[[0]*(B-1),[[0,0]]*len(edges)])
            except ArithmeticError as exc:
                f.need("no strict force separation" in str(exc),"wrong zero force rejection")
                controls+=1
            else:
                raise ArithmeticError("zero force unexpectedly accepted")
    finally:
        f.PREC,f.ROOT_PREC=prior_prec,prior_root
        f.support.cache_clear()
    return dict(status="candidate_orbit_only_full_angle_domain_excluded",
                witness_tree_sha256=TREE_SHA,candidate_stabilizer=key[1],
                count=saved_counts,nodes=saved_size,negative_controls_rejected=controls,
                strict_force_separation_floor="1/50000000",
                strict_local_squared_ceiling="17/1250",
                min_exact_force_separation_display=float(weakest),
                max_squared_anchor_displacement_display=float(max_local),
                anchor_distance_threshold=str(TARGET),
                force_radius_upper=str(f.U))


if __name__=="__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("candidate")
    p.add_argument("census")
    p.add_argument("tree")
    p.add_argument("--negative-controls", action="store_true")
    a=p.parse_args()
    print(json.dumps(check(a.candidate,a.census,a.tree,a.negative_controls),indent=2))
