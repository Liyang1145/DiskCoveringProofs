# SPDX-License-Identifier: MIT
"""Review pinned upstream numeric hints against a selected native n18 orbit.

No external verifier executes. Native radius and census checks remain the
authority; all support-plane, force, and split checks are recomputed.
"""
import argparse
from collections import Counter, defaultdict, deque
from fractions import Fraction as Q
import gzip
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path
import sys

from candidate_force import f
from compare_census import candidate_code
from force_census import load_census, need, write_json
from diskcover_n18_algebraic import SHA, isolate_radius, root_certificate

FOREST_SHA="925e901e6716a16a925f8f01cd24f1e3351fcb8714d5b1abe4265f36a3761696"


def canonical_code(faces,b):
    edge=defaultdict(set)
    for face in faces:
        for u,v in combinations(face,2):
            edge[frozenset((u,v))].add(face)
    forms=[]
    for direction in (-1,1):
        for start in range(b):
            label={(start+direction*i)%b:i for i in range(b)}
            a,v=start,(start+direction)%b
            f,=edge[frozenset((a,v))]
            seen={f}
            queue=deque([(f,a,v)])
            row=[]
            while queue:
                f,u,v=queue.popleft()
                w,=set(f)-{u,v}
                if w not in label:
                    label[w]=len(label)
                row.append(sum(1<<label[z] for z in f))
                for i,j in ((v,w),(w,u)):
                    for ff in edge[frozenset((i,j))]-seen:
                        seen.add(ff)
                        queue.append((ff,i,j))
            need(len(seen)==len(faces) and len(label)==18, "candidate traversal disconnected")
            forms.append(tuple(sorted(row)))
    best=min(forms)
    return best,forms.count(best)


def read_forest(path):
    f.need(sha256(path.read_bytes()).hexdigest()==FOREST_SHA,"unpinned numeric hints")
    with gzip.open(path,"rt",encoding="utf-8") as source:
        header=json.loads(source.readline())
        f.need(header["version"]==1 and header["cases"]==16219,"wrong forest metadata")
        for i,line in enumerate(source):
            entry=json.loads(line)
            yield entry
        f.need(i+1==header["cases"],"forest row count")


def replay_row(b,faces,nodes):
    masks=sorted(sum(1<<i for i in face) for face in faces)
    _,dist=f.graph_data(b,masks)
    edges=([(i,b+i) for i in range(b)]+[(i,b+(i+1)%b) for i in range(b)]
           +[(b+18+j,b+i) for j,face in enumerate(faces) for i in face])
    seen=set()
    work=[(0,*f.rootbox(b))]
    status=Counter()
    weakest=None
    while work:
        index,lo,hi=work.pop()
        f.need(type(index) is int and 0<=index<len(nodes) and index not in seen,"bad tree index")
        seen.add(index)
        lo,hi=f.tighten(dist,lo,hi)
        node=nodes[index]
        kind=node["kind"]
        status[kind]+=1
        if kind=="EMPTY":
            f.need(any(a>z for a,z in zip(lo,hi)),"false empty leaf")
            continue
        f.need(all(a<=z for a,z in zip(lo,hi)),"empty input for nonempty leaf or split")
        if kind=="SPLIT":
            axis=node["axis"]
            f.need(type(axis) is int,"bad split axis")
            child=f.children(lo,hi,axis+1,Q(node["mid"]))
            f.need(len(node["children"])==2,"split arity")
            work.extend((j,a,z) for j,(a,z) in zip(node["children"],child,strict=True))
        elif kind=="DUAL":
            lam=node["lambda_num"]
            f.need(all(type(i) is int and i>=0 for i in lam),"bad multiplier")
            margin=f.verify_leaf(b,edges,lo,hi,[[i*10**21 for i in lam],node["force_num"]])
            weakest=margin if weakest is None else min(weakest,margin)
        else:
            raise ArithmeticError("unresolved or unsupported leaf")
    f.need(len(seen)==len(nodes) and (weakest is None or weakest>0),"unreachable or unseparated")
    return {"nodes":len(nodes),"count":dict(status)}


def verify_loaded_witness(b, canonical_faces, original_faces, nodes):
    faces=[tuple(face) for face in original_faces]
    key,_=canonical_code(faces,b)
    f.need(key==canonical_faces,"standalone force witness orbit mismatch")
    p, q=f.PREC,f.ROOT_PREC
    f.PREC,f.ROOT_PREC=10**36,10**45
    f.support.cache_clear()
    try:
        return replay_row(b,faces,nodes)
    finally:
        f.PREC,f.ROOT_PREC=p,q
        f.support.cache_clear()


def replay(candidate,census,forest,requested,include_witness=False):
    raw=candidate.read_bytes()
    f.need(sha256(raw).hexdigest()==SHA,"unpinned candidate root")
    x,q,_=root_certificate(json.loads(raw))
    f.need(Q(isolate_radius(x,q)[1])==f.U,"force bound differs from root upper endpoint")
    f.check_caps()
    rows=load_census(census)
    cand=candidate_code()[0]
    targets={}
    for b,i in requested:
        f.need(b in (11,12,13) and 0<=i<len(rows[b]),"requested orbit index out of range")
        key=rows[b][i]
        f.need(b!=12 or key!=cand,"use the separate candidate replay")
        f.need((b,key) not in targets,"duplicate requested orbit")
        targets[b,key]=i
    todo_owners={b for b,_ in targets}
    prior_prec,prior_root=f.PREC,f.ROOT_PREC
    f.PREC,f.ROOT_PREC=10**36,10**45
    f.support.cache_clear()
    accepted=[]
    try:
        for entry in read_forest(forest):
            b=entry["B"]
            if b not in todo_owners:
                continue
            faces=[tuple(row) for row in entry["faces"]]
            key,stabilizer=canonical_code(faces,b)
            idx=targets.pop((b,key),None)
            if idx is None:
                continue
            f.need(stabilizer==entry["stabilizer"],"source stabilizer mismatch")
            result=replay_row(b,faces,entry["nodes"])
            record={"owners":b,"index":idx,"native_faces":key,
                    "source_residual_index":entry["residual_index"],**result}
            if include_witness:
                record["source_faces"]=faces
                record["witness_nodes"]=entry["nodes"]
            accepted.append(record)
            print(f"{b}:{idx} exactly replayed",file=sys.stderr,flush=True)
            if not targets:
                break
    finally:
        f.PREC,f.ROOT_PREC=prior_prec,prior_root
        f.support.cache_clear()
    f.need(not targets,"requested native orbit missing from numeric hint forest")
    return {"status":"exact_force_replay_only_for_listed_native_orbits",
            "source_sha256":FOREST_SHA,"rows":sorted(accepted,key=lambda d:(d["owners"],d["index"]))}


if __name__=="__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("root",type=Path)
    p.add_argument("census",type=Path)
    p.add_argument("forest",type=Path)
    p.add_argument("output",type=Path)
    p.add_argument("orbit",nargs="+",type=lambda s:tuple(map(int,s.split(":"))))
    p.add_argument("--include-witness",action="store_true")
    a=p.parse_args()
    result=replay(a.root,a.census,a.forest,a.orbit,a.include_witness)
    write_json(a.output,result)
    print(json.dumps(result,indent=2))
