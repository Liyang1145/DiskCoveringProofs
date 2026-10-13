"""Fresh replay of achieved joint milestones. Explicitly NOT a global-optimality replay."""
from pathlib import Path
import argparse
import importlib.util
import json
import shutil
import subprocess
import sys
import tempfile

ROOT=Path(__file__).resolve().parent
if not __debug__:
    raise RuntimeError("Assertions must be enabled")


def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    module=importlib.util.module_from_spec(spec);sys.modules[name]=module;spec.loader.exec_module(module)
    return module


def run(script,args):
    subprocess.run([sys.executable,"-B",str(ROOT/script),*map(str,args)],check=True)


def core_replay(out):
    N21=ROOT.parent/"n21-global"
    T=load("replayed_paid_core",N21/"candidate_tree.py")
    data=json.loads((N21/"evidence/core-system.json").read_text())
    b=data["B"];ed=data["edges"];v=data["G"]//2+1
    active=[sorted(data["center_core_nodes"][j]-b for j in face) for face in data["active_faces"]]
    def edges(bb,faces):
        assert bb==b and faces==active
        return [tuple(e) for e in ed]
    def binding():
        expected=[(i,b+i) for i in range(b)]+[(i,b+(i+1)%b) for i in range(b)]
        expected += [(b+20+k,b+j) for k,face in enumerate(active) for j in face]
        assert expected==[tuple(e) for e in ed]
    T.G.N,T.C.N,T.G.V,T.C.V=20,20,v,v
    T.C.tree.cache_clear();T.G.edges=edges;T.FACES=active;T.validate_embedding=binding
    T.verify(ROOT/"evidence/n21-positive-core-angle-tree.json.gz",report_path=out/"n21-core-angle-replayed.json")


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--output",type=Path,required=True)
    args=parser.parse_args()
    out=args.output.resolve()
    assert not out.exists()
    out.mkdir(parents=True)
    A=load("joint_exact_algebra",ROOT/"algebraic_roots.py")
    for n in (22,23,24):
        folder=out/f"n{n}";folder.mkdir()
        data,z,rho=A.verify(n,folder);A.upper(n,data,z,rho,folder)
        # Local script has one-shot output protection. Replay in a disposable
        # copy of inputs, never overwrite archived mathematical certificates.
        with tempfile.TemporaryDirectory(prefix=f"joint_local_n{n}_") as tmp:
            temp=Path(tmp);target=temp/f"evidence/n{n}"
            target.mkdir(parents=True)
            for name in ("core-system.json","core-root.json"):
                shutil.copy2(ROOT/f"evidence/n{n}"/name,target/name)
            (target/"algebraic-check1").mkdir()
            shutil.copy2(ROOT/f"evidence/n{n}/algebraic-check1/root-verified.json",
                         target/"algebraic-check1/root-verified.json")
            L=load(f"replay_local_{n}",ROOT/"local_certificates.py")
            L.ROOT=temp
            old=sys.argv
            try:
                sys.argv=["local_certificates.py","--n",str(n)]
                L.main()
            finally:
                sys.argv=old
            report=target/"local-isolation-certificate.json"
            assert report.read_bytes()==(ROOT/f"evidence/n{n}/local-isolation-certificate.json").read_bytes()
            shutil.copy2(report,folder/report.name)
    run("n25_algebraic_upper.py",["--output",out/"n25-algebraic"])
    run("n25_core_analysis.py",["--output",out/"n25-core"])
    run("boundary_lens_area.py",["--output",out/"n21-B12-lens-area.json"])
    run("core_reduction.py",["--output",out/"core-reduction"])
    core_replay(out)
    report={"verified_replay_of_achieved_milestones":True,
            "global_optimality_proved_for_any_new_n":False,
            "proofs_remaining":["n21 all competing types B13/B14","n22/23/24/25 complete unrestricted lower bounds"]}
    (out/"SUMMARY.json").write_text(json.dumps(report,indent=2),encoding="utf8")
    print("JOINT ACHIEVED MILESTONES FRESH REPLAY PASS; GLOBAL GOAL STILL INCOMPLETE",flush=True)


if __name__=="__main__":
    main()
