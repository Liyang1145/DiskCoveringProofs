"""Replay the verified claims in the n=27 core-search proof bundle."""
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
from tempfile import TemporaryDirectory

def invoke(cmd,root,env=None):
    r=subprocess.run(list(map(str,cmd)),cwd=root,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,
                     encoding="utf-8",env=env)
    print("$ "+" ".join(map(str,cmd)),flush=True)
    print(r.stdout,end="",flush=True)
    r.check_returncode()
    return r.stdout


def check_manifest(root):
    data=json.loads((root/"MANIFEST.json").read_text(encoding="utf-8"))
    for entry in data["files"]:
        p=root/entry["path"]
        raw=p.read_bytes()
        if len(raw)!=entry["bytes"] or hashlib.sha256(raw).hexdigest()!=entry["sha256"]:
            raise ValueError(f"file integrity check failed for {p}")
    return data


def main():
    root=Path(__file__).resolve().parent
    data=check_manifest(root)
    source=root/"anchor-search"
    sys.path.insert(0,str(source))
    from inner13_tables import generate
    from polar_tables import INNER13_LOWER
    for script in ["verify_domains.js","verify_norm_order.js"]:
        invoke(["node",source/script],root)
    for script in ["verify_core_count.py","verify_radial_core.py"]:
        invoke([sys.executable,"-B",source/script],root)
    with TemporaryDirectory(prefix="replay-",dir=root) as folder:
        tmp=Path(folder)
        env={**os.environ,"TEMP":str(tmp),"TMP":str(tmp),"TMPDIR":str(tmp)}
        exe=tmp/("interval13.exe" if os.name=="nt" else "interval13")
        invoke(["g++","-std=c++20","-O3","-DCOVER27_DISKS=13","-DCOVER27_BOUNDARY=10",
                source/"interval_search.cpp","-o",exe],root,env)

        def band(b):
            table=tmp/f"band-{b}.txt"
            generate(table,INNER13_LOWER,b,360,96,0,24)
            text=invoke([exe,table,0],root)
            if not re.search(r"^excluded$",text,re.M):
                raise ValueError(f"band {b} has no exclusion verdict")

        with ThreadPoolExecutor(max_workers=2) as pool:
            list(pool.map(band,(0,1)))
    for name in data["radial_certificates"]:
        path=root/"radial-proofs"/name
        invoke([sys.executable,"-B",source/"verify_outer_radial.py",path],root)
    print("PASS: independently reproduced the auxiliary 13-disk lower bound and the listed radial exclusions.")


if __name__=="__main__":
    main()
