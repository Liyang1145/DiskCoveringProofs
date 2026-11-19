# SPDX-License-Identifier: MIT
"""Replay the exact n18 result, including a fresh native census."""
import argparse
from concurrent.futures import ThreadPoolExecutor
from fractions import Fraction as Q
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import tempfile

from compare_census import CAPS, ORIGIN, SCALE, U, need, verify
from diskcover_n18_algebraic import check as attaining
from replay_force_archive import replay as continuous

ROOT=Path(__file__).resolve().parents[2]
HERE=Path(__file__).resolve().parent
PEEL="cover21/proof_bundle/research-2026/n21-global/peel21.cpp"


def replay(root_input,tree_input,archive,workers):
    need(1<=workers<=6,"worker count")
    upper=attaining(root_input,negative_controls=True)
    bounds=upper["candidate_radius_strict_interval"]
    need(Q(0)<Q(bounds[0])<Q(bounds[1])<U,"candidate/census radius mismatch")
    source=(ROOT/PEEL).read_bytes() if (ROOT/PEEL).is_file() else subprocess.check_output(
        ["git","show",f"HEAD:{PEEL}"],cwd=ROOT)
    need(sha256(source).hexdigest()==ORIGIN,"changed native peeler")
    with tempfile.TemporaryDirectory(prefix="n18-proof-") as path:
        out=Path(path)
        (out/"peel.cpp").write_bytes(source)
        subprocess.run(["g++","-O3","-std=c++17",str(out/"peel.cpp"),"-o",str(out/"peel")],check=True)
        def peel(key):
            b,mode=key
            subprocess.run([str(out/"peel"),"18",str(b),str(out/f"{mode}-{b}.json"),
                            str(SCALE),*(str(k) for k in CAPS),"0",mode],check=True)
        with ThreadPoolExecutor(max_workers=min(workers,6)) as pool:
            list(pool.map(peel,[(b,mode) for b in (11,12,13) for mode in ("dfs","audit")]))
        census=verify(out)
        need(census==json.loads((HERE/"census_receipt.json").read_text()),"native census receipt mismatch")
        lower=continuous(out,root_input,tree_input,archive,workers=workers)
    need(lower["status"]=="all_n18_topologies_excluded_below_exact_candidate",
         "lower exclusion not complete")
    return {"n":18,"status":"exact_global_proof_replayed",
            "exact_radius":"sqrt(t_*), same certified isolated root as the attaining construction",
            "strict_radius_interval":bounds,"native_topologies":14559,"continuous_proof":lower}


if __name__=="__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("root_input",type=Path)
    p.add_argument("tree_input",type=Path)
    p.add_argument("--archive",type=Path,default=HERE/"force_all_families.json.gz")
    p.add_argument("--workers",type=int,default=4,help="workers for native census and exact proof replay")
    a=p.parse_args()
    print(json.dumps(replay(a.root_input,a.tree_input,a.archive,a.workers),indent=2))
