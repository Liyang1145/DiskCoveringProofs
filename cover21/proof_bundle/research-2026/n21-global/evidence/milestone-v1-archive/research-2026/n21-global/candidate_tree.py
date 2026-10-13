"""Discover and exactly recheck a candidate-only n21 angle tree.

Uses inspected upstream numeric/force code configured with NEW N21 constants.
Never accepts an incomplete tree, and never proves other topology classes.
"""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
import argparse
import gzip
import hashlib
import importlib
import json
import math
import os
import sys
import time
os.environ["OPENBLAS_NUM_THREADS"] = "1"
os.environ["OMP_NUM_THREADS"] = "1"
import numpy as np

ROOT = Path(__file__).resolve().parent
EV = ROOT/"evidence"
UPSTREAM = ROOT.parent/"disk-cover-proof-library/external/pinned/cover20/proof_bundle"
if not __debug__:
    raise RuntimeError("Assertions must be enabled")
sys.path.insert(0,str(UPSTREAM/"core"))
sys.path.insert(0,str(UPSTREAM/"discovery"))
G = importlib.import_module("force20")
C = importlib.import_module("compact_force20")
T = importlib.import_module("exact_arcs")
constants = json.loads((EV/"angle-constants.json").read_text())
assert constants["verified"]
G.N,C.N = 21,21
G.V,C.V = 61,61
G.A,G.C,G.C6 = constants["angle_caps"]
G.D = constants["angle_scale"]
G.RU = C.RU = F(constants["radius_upper"])
data = json.loads((EV/"core-system.json").read_text())
root = json.loads((EV/"core-root.json").read_text())
B,FACES = data["B"],data["all_faces"]
midpoint = [F(int(v),int(root["Qx"])) for v in root["xnum"]]
small = F(1,10**80)
anchors = [[(midpoint[2*(i-1)+j]-small,midpoint[2*(i-1)+j]+small) for j in (0,1)]
           for i in range(1,B)]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def interval_dot(a,b):
    values = []
    for x,y in zip(a,b):
        products = [xx*yy for xx in x for yy in y]
        values.append((min(products),max(products)))
    return sum(x[0] for x in values),sum(x[1] for x in values)


def unit(u):
    return [(F(a,T.SCALE),F(b,T.SCALE)) for a,b in T.sincos_turn(u)]


def local(lo,hi):
    distance = F(0)
    for l,h,anchor in zip(lo,hi,anchors):
        if h-l >= F(1,2) or interval_dot(unit((l+h)/2),anchor)[0] <= 0:
            return None
        lower = min(interval_dot(unit(l),anchor)[0],interval_dot(unit(h),anchor)[0])
        distance += 2-2*lower
    return F(1,100)-distance


def validate_embedding():
    assert len(FACES) == 27
    full_edges = {frozenset(e) for e in G.edges(B,FACES)}
    witness_index = {tuple(face):i for i,face in enumerate(FACES)}
    core_to_full = {int(v):int(k) for k,v in data["old_node_to_core"].items()}
    for j,face in enumerate(data["active_faces"]):
        old = B+21+j
        core_to_full[data["old_node_to_core"][str(old)]] = B+21+witness_index[tuple(face)]
    assert all(frozenset((core_to_full[u],core_to_full[v])) in full_edges for u,v in data["edges"])


def generate(path,node_limit,resume=None):
    assert not path.exists()
    validate_embedding()
    mat = G.bounds(B,FACES)
    lo,hi = G.rootbox(mat)
    solver = G.Solver(B,FACES)
    nodes = [None]
    stack = [(0,lo,hi,0)]
    counts = Counter()
    start = time.time()
    if resume is not None:
        with gzip.open(resume,"rt",encoding="utf8") as source:
            previous = json.load(source)
        assert not previous["complete"] and previous["faces"] == FACES
        assert previous["root_sha256"] == sha(EV/"core-root.json")
        assert previous["constants_sha256"] == sha(EV/"angle-constants.json")
        assert previous["local_sha256"] == sha(EV/"local-isolation-verified.json")
        nodes = previous["nodes"]
        stack = [(p["index"],list(map(F,p["lo"])),list(map(F,p["hi"])),p["depth"])
                 for p in previous["pending"]]
        assert {i for i,node in enumerate(nodes) if node is None} == {p[0] for p in stack}
        counts = Counter(previous["counts"])
    while stack:
        if len(nodes) > node_limit:
            break
        index,lo,hi,depth = stack.pop()
        box = G.tighten(mat,lo,hi)
        if box is None:
            nodes[index] = {"kind":"EMPTY"}
            counts["EMPTY"] += 1
            continue
        lo,hi = box
        margin = local(lo,hi)
        if margin is not None and margin > 0:
            nodes[index] = {"kind":"LOCAL"}
            counts["LOCAL"] += 1
            continue
        certificate,x,status = solver.solve_slsqp(lo,hi,maxiter=100)
        if certificate is None and status["radius"] > float(G.RU)+1e-6 and not status["success"]:
            certificate,x,status = solver.solve_slsqp(lo,hi,maxiter=350)
        if certificate is not None:
            assert C.check(B,solver.ed,lo,hi,certificate) > 0
            nodes[index] = {"kind":"DUAL","certificate":certificate}
            counts["DUAL"] += 1
        else:
            assert depth <= 80, "Deep unresolved branch; do not silently accept"
            widths = [h-l for l,h in zip(lo,hi)]
            q = np.array(x[:2*(B-1)]).reshape(-1,2)
            deficits = 1-np.sum(q*q,axis=1)
            axis = max(range(B-1),key=lambda j:max(0,float(deficits[j])) if widths[j]>F(1,10**12) else -1)
            if deficits[axis] < 1e-10:
                axis = max(range(B-1),key=lambda j:widths[j])
            cut = (lo[axis]+hi[axis])/2
            assert lo[axis] < cut < hi[axis]
            a = len(nodes)
            nodes.extend([None,None])
            nodes[index] = {"kind":"SPLIT","axis":axis,"mid":str(cut),"children":[a,a+1]}
            left_hi,right_lo = list(hi),list(lo)
            left_hi[axis],right_lo[axis] = cut,cut
            stack.extend([(a+1,right_lo,list(hi),depth+1),(a,list(lo),left_hi,depth+1)])
            counts["SPLIT"] += 1
        if (sum(counts.values())%50)==0:
            print("N21 candidate tree",len(nodes),"nodes",dict(counts),
                  "pending",len(stack),"seconds",round(time.time()-start,2),flush=True)
    complete = not stack
    output = {"N":21,"B":B,"faces":FACES,"nodes":nodes,"complete":complete,
              "pending":[{"index":i,"lo":list(map(str,l)),"hi":list(map(str,h)),"depth":d}
                         for i,l,h,d in stack],"counts":dict(counts),
              "root_sha256":sha(EV/"core-root.json"),"constants_sha256":sha(EV/"angle-constants.json"),
              "local_sha256":sha(EV/"local-isolation-verified.json"),"global_optimality_proved":False,
              "seconds":time.time()-start,"source_sha256":sha(Path(__file__))}
    if resume is not None:
        output["resume_input_sha256"] = sha(resume)
    with gzip.open(path,"wt",encoding="utf8") as target:
        json.dump(output,target,separators=(",",":"))
    print("Candidate proposal saved; complete",complete,"pending",len(stack),flush=True)


def verify(path,report_path=None):
    validate_embedding()
    with gzip.open(path,"rt",encoding="utf8") as source:
        tree = json.load(source)
    assert tree["N"] == 21 and tree["B"] == B and tree["faces"] == FACES
    assert tree["root_sha256"] == sha(EV/"core-root.json")
    assert tree["constants_sha256"] == sha(EV/"angle-constants.json")
    assert tree["local_sha256"] == sha(EV/"local-isolation-verified.json")
    assert tree["complete"] and not tree["pending"], "Incomplete candidate tree cannot certify all angles"
    mat = G.bounds(B,FACES)
    edges = G.edges(B,FACES)
    lo,hi = G.rootbox(mat)
    todo = [(0,lo,hi)]
    seen = set()
    counts = Counter()
    while todo:
        index,lo,hi = todo.pop()
        assert type(index) is int and 0 <= index < len(tree["nodes"]) and index not in seen
        seen.add(index)
        node = tree["nodes"][index]
        box = G.tighten(mat,lo,hi)
        if node["kind"] == "EMPTY":
            assert box is None
        else:
            assert box is not None
            lo,hi = box
            if node["kind"] == "SPLIT":
                axis,cut,children = node["axis"],F(node["mid"]),node["children"]
                assert type(axis) is int and 0 <= axis < B-1
                assert len(children) == 2 and children[0] != children[1]
                assert lo[axis] < cut < hi[axis]
                left_hi,right_lo = list(hi),list(lo)
                left_hi[axis],right_lo[axis] = cut,cut
                todo.extend([(children[0],list(lo),left_hi),(children[1],right_lo,list(hi))])
            elif node["kind"] == "DUAL":
                assert C.check(B,edges,lo,hi,node["certificate"]) > 0
            else:
                assert node["kind"] == "LOCAL"
                margin = local(lo,hi)
                assert margin is not None and margin > 0
        counts[node["kind"]] += 1
    assert seen == set(range(len(tree["nodes"])))
    report = {"verified":True,"scope":"single candidate topology on full necessary angle domain only",
              "nodes":len(seen),"counts":dict(counts),"tree_sha256":sha(path),
              "global_optimality_proved":False}
    destination = EV/"candidate-tree-verified.json" if report_path is None else report_path
    destination.write_text(json.dumps(report,indent=2),encoding="utf8")
    print("N21 CANDIDATE FULL ANGLE DOMAIN VERIFIED; other topology types remain",flush=True)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--generate",action="store_true")
    parser.add_argument("--node-limit",type=int,default=1000)
    parser.add_argument("--output",type=Path,default=EV/"candidate-tree-round1.json.gz")
    parser.add_argument("--resume",type=Path)
    args = parser.parse_args()
    if args.generate:
        generate(args.output,args.node_limit,args.resume)
    with gzip.open(args.output,"rt",encoding="utf8") as source:
        complete = json.load(source)["complete"]
    if complete:
        verify(args.output)
    else:
        print("Not certified: candidate tree has unresolved branches",flush=True)


if __name__ == "__main__":
    main()
