"""Propose and recheck complete force trees for selected enumerated n21 types.

No inference from an incomplete probe to a full family exclusion is allowed.
All successful trees are replayed over the original necessary angle root.
"""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
import argparse
import gzip
import hashlib
import json
import time
import candidate_tree as configured

ROOT = Path(__file__).resolve().parent
EV = ROOT/"evidence"
G,C = configured.G,configured.C
if not __debug__:
    raise RuntimeError("Assertions must be enabled")


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def make(b,faces,limit):
    mat = G.bounds(b,faces)
    lo,hi = G.rootbox(mat)
    solver = G.Solver(b,faces)
    nodes = [None]
    todo = [(0,lo,hi)]
    while todo and len(nodes) <= limit:
        index,lo,hi = todo.pop()
        box = G.tighten(mat,lo,hi)
        if box is None:
            nodes[index] = {"kind":"EMPTY"}
            continue
        lo,hi = box
        cert,x,status = solver.solve_slsqp(lo,hi,maxiter=100)
        if cert is None and status["radius"] > float(G.RU)+1e-6 and not status["success"]:
            cert,x,status = solver.solve_slsqp(lo,hi,maxiter=350)
        if cert is not None:
            assert C.check(b,solver.ed,lo,hi,cert) > 0
            nodes[index] = {"kind":"DUAL","certificate":cert}
        else:
            import numpy as np
            widths = [h-l for l,h in zip(lo,hi)]
            q = np.array(x[:2*(b-1)]).reshape(-1,2)
            deficits = 1-np.sum(q*q,axis=1)
            axis = max(range(b-1),key=lambda j:max(0,float(deficits[j])) if widths[j]>F(1,10**12) else -1)
            if deficits[axis] < 1e-10:
                axis = max(range(b-1),key=lambda j:widths[j])
            cut = (lo[axis]+hi[axis])/2
            assert lo[axis] < cut < hi[axis]
            a = len(nodes)
            nodes.extend([None,None])
            nodes[index] = {"kind":"SPLIT","axis":axis,"mid":str(cut),"children":[a,a+1]}
            left_hi,right_lo = list(hi),list(lo)
            left_hi[axis],right_lo[axis] = cut,cut
            todo.extend([(a+1,right_lo,list(hi)),(a,list(lo),left_hi)])
    if todo:
        return None,{"pending_boxes":len(todo),"nodes_proposed":len(nodes)}
    return nodes,None


def verify(b,faces,nodes):
    mat = G.bounds(b,faces)
    ed = G.edges(b,faces)
    lo,hi = G.rootbox(mat)
    todo = [(0,lo,hi)]
    seen = set()
    counts = Counter()
    minimum = None
    while todo:
        index,lo,hi = todo.pop()
        assert type(index) is int and 0 <= index < len(nodes) and index not in seen
        seen.add(index)
        node = nodes[index]
        box = G.tighten(mat,lo,hi)
        if node["kind"] == "EMPTY":
            assert box is None
        else:
            assert box is not None
            lo,hi = box
            if node["kind"] == "DUAL":
                margin = C.check(b,ed,lo,hi,node["certificate"])
                assert margin > 0
                minimum = margin if minimum is None else min(minimum,margin)
            else:
                assert node["kind"] == "SPLIT"
                axis,cut,children = node["axis"],F(node["mid"]),node["children"]
                assert type(axis) is int and 0 <= axis < b-1
                assert len(children) == 2 and children[0] != children[1]
                assert lo[axis] < cut < hi[axis]
                left_hi,right_lo = list(hi),list(lo)
                left_hi[axis],right_lo[axis] = cut,cut
                todo.extend([(children[0],list(lo),left_hi),(children[1],right_lo,list(hi))])
        counts[node["kind"]] += 1
    assert seen == set(range(len(nodes))) and minimum is not None
    return {"verified":True,"nodes":len(seen),"counts":dict(counts),"minimum_margin":str(minimum)}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--family",type=Path,required=True)
    parser.add_argument("--output",type=Path,required=True)
    parser.add_argument("--start",type=int,default=0)
    parser.add_argument("--count",type=int,default=100)
    parser.add_argument("--node-limit",type=int,default=500)
    parser.add_argument("--checkpoint-every",type=int,default=20)
    args = parser.parse_args()
    assert not args.output.exists()
    args.output.mkdir(parents=True)
    census = json.loads(args.family.read_text())
    assert census["complete"] and census["N"] == 21 and census["screen"]
    b = census["B"]
    assert census["caps"] == configured.constants["angle_caps"]
    outcomes = []
    stop = min(len(census["survivors"]),args.start+args.count)
    for index in range(args.start,stop):
        row = census["survivors"][index]
        faces = [sorted(v for v in range(21) if mask>>v&1) for mask in row["faces"]]
        start = time.time()
        nodes,pending = make(b,faces,args.node_limit)
        if nodes is None:
            outcome = {"index":index,"status":"pending",**pending}
        else:
            report = verify(b,faces,nodes)
            payload = {"N":21,"B":b,"index":index,"faces":faces,"nodes":nodes,
                       "family_sha256":sha(args.family),"constants_sha256":sha(EV/"angle-constants.json"),
                       "scope":"one enumerated topology, whole necessary angle domain"}
            path = args.output/f"case-{index:07}.json.gz"
            with gzip.open(path,"wt",encoding="utf8") as target:
                json.dump(payload,target,separators=(",",":"))
            outcome = {"index":index,"status":"proved-excluded",**report,"certificate_sha256":sha(path)}
        outcome["seconds"] = time.time()-start
        outcomes.append(outcome)
        if len(outcomes)%args.checkpoint_every == 0 or index+1 == stop:
            (args.output/"SUMMARY.json").write_text(json.dumps({
                "B":b,"family_orbits":census["orbits"],"tested_cases":outcomes,
                "family_sha256":sha(args.family),"family_exclusion_complete":False,
                "global_optimality_proved":False,"scope":"selected types; complete family set requires separate aggregation audit"
            },indent=2),encoding="utf8")
            print("N21 noncandidate",b,"checked",len(outcomes),"last",index,outcome["status"],
                  "pending",sum(r["status"]=="pending" for r in outcomes),flush=True)


if __name__ == "__main__":
    main()
