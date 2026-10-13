"""Fail-closed regressions supplement n21 milestones, not exhaustive software proof."""
from pathlib import Path
from fractions import Fraction as F
from copy import deepcopy
import gzip
import importlib.util
import json
import shutil
import subprocess
import sys
import tempfile
import candidate_tree as tree

ROOT = Path(__file__).resolve().parent
EV = ROOT/"evidence"
if not __debug__:
    raise RuntimeError("Assertions must be enabled")


def must_reject(fn,label):
    try:
        fn()
    except (AssertionError,ValueError,KeyError,TypeError,IndexError):
        return label
    raise RuntimeError("Bad input was accepted: "+label)


def main():
    tests = []
    with gzip.open(EV/"candidate-tree-round2.json.gz","rt",encoding="utf8") as source:
        original = json.load(source)
    assert original["complete"]
    # Reconstruct the first exact force leaf's angle box.
    mat = tree.G.bounds(tree.B,tree.FACES)
    lo,hi = tree.G.rootbox(mat)
    todo = [(0,lo,hi)]
    selected = None
    while todo:
        index,lo,hi = todo.pop()
        lo,hi = tree.G.tighten(mat,lo,hi)
        node = original["nodes"][index]
        if node["kind"] == "DUAL":
            selected = lo,hi,node["certificate"]
            break
        if node["kind"] == "SPLIT":
            axis,cut = node["axis"],F(node["mid"])
            left_hi,right_lo = list(hi),list(lo)
            left_hi[axis],right_lo[axis] = cut,cut
            todo.extend([(node["children"][0],list(lo),left_hi),(node["children"][1],right_lo,list(hi))])
    assert selected is not None
    lo,hi,certificate = selected
    edges = tree.G.edges(tree.B,tree.FACES)
    assert tree.C.check(tree.B,edges,lo,hi,certificate) > 0
    bad = deepcopy(certificate)
    bad["l"][0] = -1
    tests.append(must_reject(lambda:tree.C.check(tree.B,edges,lo,hi,bad),"negative_force_multiplier"))
    bad = deepcopy(certificate)
    bad["q"] = 0
    tests.append(must_reject(lambda:tree.C.check(tree.B,edges,lo,hi,bad),"zero_force_denominator"))
    with tempfile.TemporaryDirectory(prefix="n21-negative-") as temp:
        directory = Path(temp)
        for label,change in (
            ("unresolved_tree",lambda t:t.update(complete=False)),
            ("duplicate_children",lambda t:t["nodes"][0].update(children=[1,1])),
            ("whole_domain_mislabeled_local",lambda t:t["nodes"].__setitem__(0,{"kind":"LOCAL"})),
            ("wrong_constants_binding",lambda t:t.update(constants_sha256="0"*64)),
        ):
            badtree = deepcopy(original)
            change(badtree)
            p = directory/(label+".json.gz")
            with gzip.open(p,"wt",encoding="utf8") as target:
                json.dump(badtree,target)
            tests.append(must_reject(lambda:tree.verify(p),label))
        roots = directory/"root"
        roots.mkdir()
        for name in ("core-system.json","core-root.json"):
            shutil.copy2(EV/name,roots/name)
        badroot = json.loads((roots/"core-root.json").read_text())
        badroot["xnum"][0] = str(int(badroot["xnum"][0])+int(badroot["Qx"])//1000)
        (roots/"core-root.json").write_text(json.dumps(badroot),encoding="utf8")
        spec = importlib.util.spec_from_file_location("n21_bad_root_probe",ROOT/"root_certificate.py")
        root_module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(root_module)
        root_module.EV = roots
        tests.append(must_reject(root_module.verify,"corrupted_root_coordinate"))
    result = subprocess.run([sys.executable,"-O",str(ROOT/"root_certificate.py")],
                            stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    assert result.returncode != 0 and b"Assertions must be enabled" in result.stderr
    tests.append("optimized_python_rejected")
    output = {"verified":True,"tests":tests,"count":len(tests),"global_optimality_proved":False}
    (EV/"negative-checks.json").write_text(json.dumps(output,indent=2),encoding="utf8")
    print("N21 fail-closed regression:",len(tests),"PASS",flush=True)


if __name__ == "__main__":
    main()
