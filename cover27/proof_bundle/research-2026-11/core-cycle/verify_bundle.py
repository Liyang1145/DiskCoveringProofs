"""Replay the conditional area and core-cycle certificates."""
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory


def main():
    root=Path(__file__).resolve().parent
    manifest=json.loads((root/"MANIFEST.json").read_text(encoding="utf-8"))
    for file in manifest["files"]:
        path=root/file["path"]
        contents=path.read_bytes()
        if len(contents)!=file["bytes"] or sha256(contents).hexdigest()!=file["sha256"]:
            raise ValueError(f"file integrity check failed for {path}")

    def node(script,*args):
        subprocess.run(["node",str(root/script),*map(str,args)],cwd=root,check=True)

    def python(script,*args):
        subprocess.run([sys.executable,"-B",str(root/"anchor-search"/script),*map(str,args)],
                       cwd=root,check=True)

    for name in ("verify_domains.js","verify_norm_order.js","verify_two_hop.js",
                 "verify_boundary_neighbors.js","verify_core_radius.js",
                 "verify_ten_core_metric.js","verify_translated_core.js"):
        node(Path("anchor-search")/name)
    node("verify_boundary14_shared_angles_229360.js")
    python("verify_expanded_core_count.py",root/"B14-expanded-core-count.json")
    python("verify_far_inner.py",root/"B14-far-inner.json")
    python("verify_ten_boundary_neighbors.py")
    python("verify_b14_core_marks.py")

    with TemporaryDirectory(prefix="circle-cover-27-cycle-") as folder:
        tmp=Path(folder)
        degree=tmp/"B14-residual-degrees.json"
        node("verify_boundary14_degree_cap.js",degree)
        for script,catalog in (("verify_b14_incidence.py","B14-incidence.json"),
                               ("verify_b14_ten_ring.py","B14-ten-ring.json")):
            output=tmp/catalog
            python(script,degree,"--output",output)
            if output.read_bytes()!=(root/catalog).read_bytes():
                raise ValueError(f"regenerated catalog differs from {catalog}")
    print("PASS: conditional area exclusions and the B=14 core-cycle catalogs reproduce.")


if __name__=="__main__":
    main()
