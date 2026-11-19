# SPDX-License-Identifier: MIT
"""Replay the native n16 global proof from two pinned candidate input files."""
import argparse
import json
import hashlib
from fractions import Fraction as Q
from pathlib import Path
import subprocess
import sys
import tempfile

from anchor_isolation import require
from candidate_data_replay import check as candidate_check
from compare_census import SCALE, CAPS, TRIAL, verify as census_check
from force_exclusion import U as force_upper
from verify_native_n16_attainment import ROOT_SHA, T, root_box, check_cover

ROOT=Path(__file__).resolve().parents[2]
HERE=Path(__file__).resolve().parent
PEEL="cover21/proof_bundle/research-2026/n21-global/peel21.cpp"
PEEL_SHA="7063d6fbd45786696873b13c5d8b07e657bcdf47c685b0aae8392876373e53d0"


def replay(root_input,tree_input):
    raw=root_input.read_bytes()
    require(hashlib.sha256(raw).hexdigest()==ROOT_SHA,"wrong root input")
    x,rho,_=root_box(json.loads(raw))
    require(0<x[T]-rho<x[T]+rho<force_upper**2<TRIAL**2,
            "lower/upper root and trial thresholds disagree")
    check_cover(x,rho)
    source=(ROOT/PEEL).read_bytes() if (ROOT/PEEL).is_file() else subprocess.check_output(
        ["git","show",f"HEAD:{PEEL}"],cwd=ROOT)
    require(hashlib.sha256(source).hexdigest()==PEEL_SHA,"native peeler changed")
    with tempfile.TemporaryDirectory(prefix="n16-proof-") as path:
        out=Path(path)
        (out/"peel.cpp").write_bytes(source)
        subprocess.run(["g++","-O3","-std=c++17",str(out/"peel.cpp"),"-o",str(out/"peel")],check=True)
        for b in (11,12):
            for mode in ("dfs","audit"):
                subprocess.run([str(out/"peel"),"16",str(b),str(out/f"{mode}-{b}.json"),
                                str(SCALE),*(str(k) for k in CAPS),"0",mode],check=True)
        census=census_check(out)
        expected=json.loads((HERE/"census_receipt.json").read_text())
        require(census==expected,"native census receipt differs")
        for b in (11,12):
            subprocess.run([sys.executable,str(HERE/"force_exclusion.py"),
                            str(HERE/f"force_b{b}.json.gz"),"--census",str(out/f"dfs-{b}.json"),
                            "--complete-noncandidate"],check=True)
        candidate=candidate_check(root_input,out/"dfs-12.json",tree_input,True)
    return dict(n=16,status="exact_global_proof_replayed",
                result="r_D(16)=sqrt(t_*), same isolated root as the attaining construction",
                noncandidate_orbits=sum(x["orbits"] for x in census)-1,
                candidate=candidate)


if __name__=="__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("root_input",type=Path)
    p.add_argument("tree_input",type=Path)
    a=p.parse_args()
    print(json.dumps(replay(a.root_input,a.tree_input),indent=2))
