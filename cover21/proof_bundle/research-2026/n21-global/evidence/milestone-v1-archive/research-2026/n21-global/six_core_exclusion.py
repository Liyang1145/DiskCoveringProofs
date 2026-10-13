"""Self-contained strict six-disk auxiliary exclusion at radius 2771/5000.

Uses only three hexagon triangulations and exact force trees. No assertion that
the exact six-disk optimum is computed here, and no old literature value trusted.
"""
from pathlib import Path
from fractions import Fraction as F
from math import ceil
import gzip
import hashlib
import importlib.util
import json
import argparse
import mpmath as mp
import candidate_tree as conf
import noncandidate_probe as probe

ROOT = Path(__file__).resolve().parent
EV = ROOT/"evidence"
if not __debug__:
    raise RuntimeError("Assertions must be enabled")
G,C = conf.G,conf.C
Q = F(2771,5000)
D = 10**7


def gap_bounds(b,faces):
    assert b == 6
    G.edges(b,faces)
    mat = [[10**9]*b for _ in range(b)]
    for i in range(b):
        mat[i][i] = 0
        j = (i+1)%b
        mat[i][j] = min(mat[i][j],G.A-(D if j==0 else 0))
        mat[j][i] = min(mat[j][i],D if j==0 else 0)
    for k in range(b):
        for i in range(b):
            for j in range(b):
                mat[i][j] = min(mat[i][j],mat[i][k]+mat[k][j])
    assert all(mat[i][i] == 0 for i in range(b))
    return mat


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--replay",action="store_true")
    args = parser.parse_args()
    path = EV/"six-core-exclusion"
    if not args.replay:
        assert not path.exists()
        path.mkdir()
    source = ROOT.parent/"n13-global/independent_checks.py"
    spec = importlib.util.spec_from_file_location("six_aux_trig",source)
    trig = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(trig)
    mp.mp.dps = 50
    cap = ceil(mp.asin(mp.mpf(Q.numerator)/Q.denominator)/mp.pi*D)+1
    sine = trig.trig(F(cap,2*D))[1]
    assert Q < F(sine[0],trig.S60)
    assert Q < F(trig.trig(F(1,10))[1][0],trig.S60) # five boundary disks insufficient
    constants = json.loads((EV/"angle-constants.json").read_text())
    u = F(constants["radius_upper"])
    assert u/(1-2*u) < Q < 1
    G.N,C.N,G.V,C.V = 6,6,16,16
    G.A,G.D,G.RU,C.RU = cap,D,Q,Q
    G.bounds = gap_bounds
    C.tree.cache_clear()
    input_path = EV/"peeling-round1/N6-B6-noscreen.json"
    census = json.loads(input_path.read_text())
    assert census["complete"] and not census["screen"] and census["orbits"] == 3
    assert sum(12//row["stabilizer"] for row in census["survivors"]) == 14
    reports = []
    for index,row in enumerate(census["survivors"]):
        faces = [sorted(v for v in range(6) if mask>>v&1) for mask in row["faces"]]
        target = path/f"hexagon-{index}.json.gz"
        if args.replay:
            with gzip.open(target,"rt",encoding="utf8") as stream:
                tree = json.load(stream)
            assert tree["B"] == tree["N"] == 6 and tree["radius"] == str(Q)
            assert tree["gap_cap"] == cap and tree["scale"] == D and tree["faces"] == faces
            nodes = tree["nodes"]
        else:
            nodes,pending = probe.make(6,faces,10000)
            assert nodes is not None, ("six-core branch pending",index,pending)
            with gzip.open(target,"wt",encoding="utf8") as stream:
                json.dump({"B":6,"N":6,"radius":str(Q),"gap_cap":cap,"scale":D,
                           "faces":faces,"nodes":nodes},stream,separators=(",",":"))
        report = probe.verify(6,faces,nodes)
        report.update(index=index,tree_sha256=hashlib.sha256(target.read_bytes()).hexdigest())
        reports.append(report)
        print("SIX DISK STRICT AUXILIARY EXCLUSION",index,"PASS",report["nodes"],flush=True)
    result = {"verified":True,"proposition":"No six equal disks of radius strictly below 2771/5000 cover the closed unit disk",
              "radius":str(Q),"gap_scale":D,"gap_cap":cap,"topology_orbits":3,"fixed_boundary_labeled_triangulations":14,
              "trees":reports,"n21_minimum_interior_cells":7,"n21_maximum_boundary_cells":14,
              "n21_remaining_families":[[12,9],[13,8],[14,7]],
              "strict_core_ratio_gap":str(Q-u/(1-2*u)),
              "scope":"auxiliary strict lower bound and necessary n21 reduction; not six-disk exact optimum or n21 global optimum",
              "six_census_sha256":hashlib.sha256(input_path.read_bytes()).hexdigest(),
              "constants_sha256":hashlib.sha256((EV/"angle-constants.json").read_bytes()).hexdigest(),
              "source_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "global_optimality_proved":False}
    (path/("REPLAY.json" if args.replay else "VERIFIED.json")).write_text(json.dumps(result,indent=2),encoding="utf8")
    print("N21 CORE CUT STRENGTHENED: at least 7 interior disks, 12<=B<=14",flush=True)


if __name__ == "__main__":
    main()
