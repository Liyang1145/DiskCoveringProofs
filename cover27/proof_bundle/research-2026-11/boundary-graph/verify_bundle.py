"""Replay the supplemental graph, radial and translated-core certificates."""
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory


def run(root, *args):
    subprocess.run(list(map(str,args)),cwd=root,check=True)


def same_file(actual, expected):
    if actual.read_bytes()!=expected.read_bytes():
        raise ValueError(f"regenerated catalog differs from {expected.name}")


def main():
    root=Path(__file__).resolve().parent
    data=json.loads((root/"MANIFEST.json").read_text(encoding="utf-8"))
    for item in data["files"]:
        path=root/item["path"]
        raw=path.read_bytes()
        if len(raw)!=item["bytes"] or sha256(raw).hexdigest()!=item["sha256"]:
            raise ValueError(f"integrity check failed for {path}")

    src=root/"anchor-search"
    for script in ("verify_domains.js","verify_norm_order.js","verify_two_hop.js",
                   "verify_apex_norms.js","verify_boundary_neighbors.js","verify_owned_radial.js",
                   "verify_b18_translated_core.js"):
        run(root,"node",src/script)
    run(root,sys.executable,"-B",src/"verify_expanded_core_count.py",root/"B14-expanded-core-count.json")
    run(root,sys.executable,"-B",src/"verify_far_inner.py",root/"B14-far-inner.json")

    with TemporaryDirectory(prefix="circle-cover-27-graph-") as name:
        tmp=Path(name)
        degrees=tmp/"B14-residual-degrees.json"
        run(root,"node",root/"verify_boundary14_degree_cap.js",degrees)
        for script,catalog,extra in [
            ("verify_boundary_walk.py","B14-boundary-apex-patterns.json",()),
            ("verify_boundary_residual.py","B14-low-degree-annuli.json",()),
            ("verify_boundary_degree_profiles.py","B14-degree-and-apex.json",(degrees,)),
        ]:
            out=tmp/catalog
            run(root,sys.executable,"-B",src/script,*extra,"--output",out)
            same_file(out,root/catalog)
    print("PASS: the B=14 boundary graph and B=18 translated-core certificates reproduce.")


if __name__=="__main__":
    main()
