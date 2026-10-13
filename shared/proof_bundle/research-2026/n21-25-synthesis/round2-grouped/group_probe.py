"""Exact full-domain force probes on canonical boundary-exposed partial graphs.

Each accepted tree transfers by its explicit face map to every group member.
Partial graph failures/pending are not claims about existence of true covers.
"""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
import argparse
import gzip
import hashlib
import importlib.util
import json
import sys
import time

ROOT=Path(__file__).resolve().parent
PARENT=ROOT.parent
N21=PARENT.parent/"n21-global"
if not __debug__:
    raise RuntimeError("Assertions must be enabled")
sys.path.insert(0,str(N21))
import noncandidate_probe as base
G,C=base.G,base.C
original_N=G.N


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def setup(B,masks,centers):
    faces=[[i for i in range(centers) if mask>>i&1] for mask in masks]
    assert all(len(face)==3 for face in faces)
    V=B+centers+len(faces)
    edges=[(i,B+i) for i in range(B)]+[(i,B+(i+1)%B) for i in range(B)]
    edges += [(B+centers+k,B+j) for k,face in enumerate(faces) for j in face]
    assert set(x for e in edges for x in e)==set(range(V))
    G.N,C.N,G.V,C.V=centers,centers,V,V
    def edge_fn(b,f):
        assert b==B and f==faces
        return edges
    G.edges=edge_fn
    return faces,edges,V


def make_tree(B,faces,limit,route_numeric_feasible=False):
    """Proof tree proposal, optionally decline numerically realizable weakenings."""
    mat=G.bounds(B,faces);lo,hi=G.rootbox(mat)
    solver=G.Solver(B,faces);nodes=[None];pending=[(0,lo,hi)]
    while pending and len(nodes)<=limit:
        index,lo,hi=pending.pop()
        box=G.tighten(mat,lo,hi)
        if box is None:
            nodes[index]={"kind":"EMPTY"};continue
        lo,hi=box
        certificate,x,status=solver.solve_slsqp(lo,hi,maxiter=100)
        if certificate is None and status["radius"]>float(G.RU)+1e-6 and not status["success"]:
            certificate,x,status=solver.solve_slsqp(lo,hi,maxiter=350)
        if certificate is not None:
            assert C.check(B,solver.ed,lo,hi,certificate)>0
            nodes[index]={"kind":"DUAL","certificate":certificate}
            continue
        if index==0 and route_numeric_feasible and hasattr(solver,"fixed_unit_anchor_proposal"):
            numeric=solver.fixed_unit_anchor_proposal(x)
            if numeric is not None and numeric["radius_float"]<float(G.RU)-1e-5:
                return None,{"pending_boxes":1,"nodes_proposed":1,
                    "routing_reason":"weaker graph has untrusted numerical unit-anchor realization below U; add constraints",
                    "numerical_diagnostic":numeric,"not_a_verified_counterexample":True}
        import numpy as np
        widths=[h-l for l,h in zip(lo,hi)]
        if max(widths)<=0:
            return None,{"pending_boxes":1,"nodes_proposed":len(nodes),"routing_reason":"unsolved zero-width domain"}
        q=np.array(x[:2*(B-1)]).reshape(-1,2);deficits=1-np.sum(q*q,axis=1)
        axis=max(range(B-1),key=lambda j:max(0,float(deficits[j])) if widths[j]>F(1,10**12) else -1)
        if deficits[axis]<1e-10 or widths[axis]<=0:
            axis=max(range(B-1),key=lambda j:widths[j])
        cut=(lo[axis]+hi[axis])/2
        assert lo[axis]<cut<hi[axis]
        a=len(nodes);nodes.extend([None,None])
        nodes[index]={"kind":"SPLIT","axis":axis,"mid":str(cut),"children":[a,a+1]}
        left=list(hi);right=list(lo);left[axis]=cut;right[axis]=cut
        pending.extend([(a+1,right,list(hi)),(a,list(lo),left)])
    if pending:
        return None,{"pending_boxes":len(pending),"nodes_proposed":len(nodes)}
    return nodes,None


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--groups",type=Path,required=True)
    parser.add_argument("--output",type=Path,required=True)
    parser.add_argument("--limit",type=int,default=500)
    parser.add_argument("--count",type=int,default=100)
    parser.add_argument("--start",type=int,default=0)
    parser.add_argument("--solver",choices=("slsqp","clarabel"),default="slsqp")
    parser.add_argument("--only-pending-from",type=Path)
    parser.add_argument("--checkpoint-every",type=int,default=100)
    parser.add_argument("--route-numeric-feasible",action="store_true")
    args=parser.parse_args()
    assert not args.output.exists()
    args.output.mkdir(parents=True)
    dataset=json.loads(args.groups.read_text())
    assert dataset["verified_embeddings"] and dataset["N"]==21
    B=dataset["B"]
    membership=Counter(bind["group"] for bind in dataset["bindings"])
    dataset_hash=sha(args.groups)
    source_hash=sha(Path(__file__))
    constants_hash=sha(N21/"evidence/angle-constants.json")
    if args.solver=="clarabel":
        from conic_proposals import make_solver_class
        G.Solver=make_solver_class(G,C)
    chosen=dataset["groups"][args.start:args.start+args.count]
    if args.only_pending_from is not None:
        previous=json.loads(args.only_pending_from.read_text())
        assert previous["groups_sha256"]==dataset_hash
        pending={row["group"] for row in previous["outcomes"] if row["status"]=="pending"}
        chosen=[row for row in chosen if row["id"] in pending]
    known_attained=None
    if B==13:
        from boundary_groups import canonical_partial
        source=json.loads((N21/"evidence/core-system.json").read_text())
        full=[sum(1<<j for j in face) for face in source["all_faces"]]
        code,_,_=canonical_partial(B,full,dataset.get("minimum_boundary_vertices_in_retained_faces",1))
        known_attained=next((row["id"] for row in dataset["groups"] if tuple(row["faces"])==code),None)
        assert known_attained is not None or not dataset["full_catalog_scanned"]
    outcomes=[];start=time.time()
    totals=Counter();covered_members=0
    ledger=(args.output/"outcomes.jsonl").open("w",encoding="utf8")
    for row in chosen:
        faces,edges,V=setup(B,row["faces"],row["centers"])
        nodes,pending=make_tree(B,faces,args.limit,args.route_numeric_feasible)
        if nodes is None:
            outcome={"group":row["id"],"status":"pending",**pending}
        else:
            assert row["id"]!=known_attained,"Exact known attaining graph must not be strictly excluded"
            checked=base.verify(B,faces,nodes)
            target=args.output/f"group-{row['id']:07}.json.gz"
            payload={"B":B,"N":21,"partial_centers":row["centers"],"partial_vertices":V,
                     "faces":row["faces"],"nodes":nodes,"radius_upper":str(G.RU),
                     "constants_sha256":constants_hash,
                     "group_dataset_sha256":dataset_hash,
                     "scope":"weakened boundary-exposed graph on whole necessary angle domain"}
            with gzip.open(target,"wt",encoding="utf8") as stream:
                json.dump(payload,stream,separators=(",",":"))
            members=membership[row["id"]]
            outcome={"group":row["id"],"status":"excluded","verified":True,
                     "checked_catalog_members":members,**checked,"tree_sha256":sha(target)}
        outcomes.append(outcome)
        totals[outcome["status"]]+=1
        covered_members+=outcome.get("checked_catalog_members",0)
        ledger.write(json.dumps(outcome,separators=(",",":"))+"\n")
        report={"N":21,"B":B,"outcomes":outcomes,
                "excluded_group_count":totals["excluded"],
                "pending_group_count":totals["pending"],
                "catalog_member_exclusions":covered_members,
                "groups_sha256":dataset_hash,"source_sha256":source_hash,
                "whole_catalog_exclusion_proved":False,"global_optimality_proved":False}
        if len(outcomes)%args.checkpoint_every==0 or row["id"]==chosen[-1]["id"]:
            ledger.flush()
            (args.output/"PROGRESS.json").write_text(json.dumps({
                "N":21,"B":B,"checked_groups":len(outcomes),"requested_groups":len(chosen),
                "excluded_groups":report["excluded_group_count"],"pending_groups":report["pending_group_count"],
                "catalog_member_exclusions":report["catalog_member_exclusions"],
                "complete":False,"global_optimality_proved":False
            },indent=2),encoding="utf8")
            print("Group probe B",B,"done",len(outcomes),
                  "excluded",totals["excluded"],
                  "pending",totals["pending"],
                  "seconds",round(time.time()-start,2),flush=True)
    report={"N":21,"B":B,"outcomes":outcomes,
            "excluded_group_count":totals["excluded"],
            "pending_group_count":totals["pending"],
            "catalog_member_exclusions":covered_members,
            "groups_sha256":dataset_hash,"source_sha256":source_hash,
            "proposal_solver":args.solver,"known_attained_group_control":known_attained,
            "whole_catalog_exclusion_proved":False,"global_optimality_proved":False}
    ledger.flush();ledger.close()
    report["requested_group_checks_completed"]=len(outcomes)==len(chosen)
    report["outcome_ledger_sha256"]=sha(args.output/"outcomes.jsonl")
    (args.output/"SUMMARY.json").write_text(json.dumps(report,indent=2),encoding="utf8")


if __name__=="__main__":
    main()
