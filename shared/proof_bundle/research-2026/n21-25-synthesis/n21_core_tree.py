"""Relax the n21 tree to its positive core, deleting all slack-face constraints.

If complete, its lower bound applies to every full graph containing this exact
core after a proved labeling map. Catalogue-wide existence of that map is separate.
"""
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import sys

ROOT=Path(__file__).resolve().parent
N21=ROOT.parent/"n21-global"
if not __debug__:
    raise RuntimeError("Assertions must be enabled")


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--output",type=Path,required=True)
    parser.add_argument("--limit",type=int,default=12000)
    args=parser.parse_args()
    assert not args.output.exists()
    spec=importlib.util.spec_from_file_location("inspected_n21_tree_kernel",N21/"candidate_tree.py")
    T=importlib.util.module_from_spec(spec);spec.loader.exec_module(T)
    data=json.loads((N21/"evidence/core-system.json").read_text())
    b=data["B"];ed=data["edges"];v=data["G"]//2+1
    active=[]
    for face in data["active_faces"]:
        active.append(sorted(data["center_core_nodes"][j]-b for j in face))
    assert len(active)==14 and v==47 and len(ed)==68
    assert all(len(set(face))==3 and all(0<=j<20 for j in face) for face in active)
    def core_edges(bb,faces):
        assert bb==b and faces==active
        return [tuple(e) for e in ed]
    def validate_core():
        expected=[(i,b+i) for i in range(b)]+[(i,b+(i+1)%b) for i in range(b)]
        expected += [(b+20+k,b+j) for k,fa in enumerate(active) for j in fa]
        assert expected==[tuple(e) for e in ed]
        assert sorted({x for e in ed for x in e})==list(range(v))
    T.G.N,T.C.N=20,20
    T.G.V,T.C.V=v,v
    T.C.tree.cache_clear()
    T.G.edges=core_edges
    T.FACES=active
    T.validate_embedding=validate_core
    validate_core()
    T.generate(args.output,args.limit)
    import gzip
    with gzip.open(args.output,"rt",encoding="utf8") as source:
        result=json.load(source)
    if result["complete"]:
        report=args.output.with_suffix(".verified.json")
        T.verify(args.output,report_path=report)
        accepted=json.loads(report.read_text())
        accepted.update(scope="n21 68-positive-rod core on its entire relaxed necessary angle domain; slack centers/faces not needed",
                        source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                        reused_kernel_sha256=hashlib.sha256((N21/"candidate_tree.py").read_bytes()).hexdigest(),
                        graph_edges=68,graph_vertices=47,global_optimality_proved=False)
        report.write_text(json.dumps(accepted,indent=2),encoding="utf8")
        print("N21 WHOLE-ANGLE POSITIVE CORE LOWER BOUND CLOSED; catalogue core-embedding still open",flush=True)
    else:
        print("N21 CORE TREE INCOMPLETE; not a new accepted lower bound",flush=True)


if __name__=="__main__":
    main()
