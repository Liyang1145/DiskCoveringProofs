# SPDX-License-Identifier: MIT
"""Fresh native census and exact global replay for nineteen disks."""
import argparse
from hashlib import sha256
from pathlib import Path
import json
import subprocess
import sys
import tempfile

ROOT=Path(__file__).resolve().parents[2]
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/"tools"))
from diskcover_n19_upper import check_n19_upper
from compare_census import caps

PEEL="cover21/proof_bundle/research-2026/n21-global/peel21.cpp"
PEEL_SHA="7063d6fbd45786696873b13c5d8b07e657bcdf47c685b0aae8392876373e53d0"


def replay(workers):
    if workers<1:
        raise ValueError("workers must be positive")
    upper=check_n19_upper()
    if upper["upper_squared"]!="1/13":
        raise ArithmeticError("unexpected attaining construction radius")
    caps()
    if (ROOT/PEEL).is_file():
        source=(ROOT/PEEL).read_bytes()
    else:
        source=subprocess.check_output(["git","show",f"HEAD:{PEEL}"],cwd=ROOT)
    if sha256(source).hexdigest()!=PEEL_SHA:
        raise ArithmeticError("modified native peeler")
    with tempfile.TemporaryDirectory(prefix="n19-proof-") as path:
        out=Path(path)
        (out/"peel.cpp").write_bytes(source)
        subprocess.run(["g++","-O3","-std=c++17",str(out/"peel.cpp"),"-o",str(out/"peel")],check=True)
        from concurrent.futures import ThreadPoolExecutor
        def run(key):
            b,mode=key
            subprocess.run([str(out/"peel"),"19",str(b),str(out/f"{mode}-{b}.json"),
                            "100000","8946","18717","31284","0",mode],check=True)
        with ThreadPoolExecutor(max_workers=min(workers,6)) as pool:
            list(pool.map(run,[(b,mode) for b in (12,13,14) for mode in ("dfs","audit")]))
        subprocess.run([sys.executable,str(HERE/"replay_force_archive.py"),
                        str(out),"--workers",str(workers)],check=True)
    return dict(n=19,status="exact_global_proof_replayed",radius_exact="1/sqrt(13)",
                radius_squared="1/13",native_orbits=23535)


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workers",type=int,default=4)
    print(json.dumps(replay(parser.parse_args().workers),indent=2))
