"""Fresh stdlib-only acceptance of n22..25 candidate-core entire-angle trees."""
from pathlib import Path
from fractions import Fraction as F
from math import isqrt
import argparse
import gzip
import hashlib
import json
import sys
import exact_graph as exact

ROOT = Path(__file__).resolve().parent
SYN = ROOT.parent
sys.path.insert(0, str(exact.kernel.ARCS))
import exact_arcs as arcs
assert __debug__


def sha(path):
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def dot(a, b):
    products = [tuple(x*y for x in iv for y in jv) for iv, jv in zip(a, b)]
    return sum(min(p) for p in products), sum(max(p) for p in products)


def local(anchors, radius):
    def unit(turn):
        return [(F(lo, arcs.SCALE), F(hi, arcs.SCALE)) for lo, hi in arcs.sincos_turn(turn)]
    def check(lo, hi):
        assert len(lo) == len(hi) == len(anchors)
        squared = F(0)
        for l, h, anchor in zip(lo, hi, anchors):
            if h-l >= F(1, 2) or dot(unit((l+h)/2), anchor)[0] <= 0:
                return None
            endpoint = min(dot(unit(l), anchor)[0], dot(unit(h), anchor)[0])
            squared += 2-2*endpoint
        return radius**2-squared
    return check


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, choices=(22, 23, 24, 25), required=True)
    ap.add_argument("--tree", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    n = args.n
    constantspath = SYN / f"evidence/core-reduction/constants/n{n}.json"
    constants = json.loads(constantspath.read_text())
    assert constants["verified"] and constants["N"] == n
    if n < 25:
        folder = SYN / f"evidence/n{n}"
        systempath, rootpath = folder / "core-system.json", folder / "core-root.json"
        localpath = folder / "local-isolation-certificate.json"
        data, root, isolation = (json.loads(p.read_text()) for p in (systempath, rootpath, localpath))
        paidroot = json.loads((folder / "algebraic-check1/root-verified.json").read_text())
        assert paidroot["verified"] and paidroot["root_sha256"] == isolation["root_sha256"] == sha(rootpath)
        assert isolation["verified"] and F(isolation["isolation_margin"]) > 0
        B = data["B"]
        N = data["G"]//2+1-B-len(data["active_faces"])
        masks = sorted(sum(1 << (data["center_core_nodes"][v]-B) for v in face) for face in data["active_faces"])
        midpoint = [F(int(v), int(root["Qx"])) for v in root["xnum"]]
        rho = F(1, 10**80)
        anchors = [[(midpoint[2*(i-1)+axis]-rho, midpoint[2*(i-1)+axis]+rho)
                    for axis in (0, 1)] for i in range(1, B)]
    else:
        systempath = rootpath = ROOT / "evidence/n25-isolation-exact-resume1/rotated-geometry.json"
        localpath = ROOT / "evidence/n25-isolation-exact-resume1/VERIFIED.json"
        geometry, isolation = (json.loads(p.read_text()) for p in (systempath, localpath))
        assert isolation["verified"] and isolation["rotated_geometry_sha256"] == sha(rootpath)
        assert F(isolation["isolation_margin"]) > 0
        B, N = 16, 25
        masks = sorted(sum(1 << v for v in face) for face in geometry["faces"])
        scale = 10**80
        lower = isqrt(2*scale*scale)
        assert lower**2 < 2*scale*scale < (lower+1)**2
        def enclosure(value):
            a, b = map(F, value)
            first, last = a+b*F(lower, scale), a+b*F(lower+1, scale)
            return min(first, last), max(first, last)
        anchors = [[enclosure(v) for v in p] for p in geometry["points_Qsqrt2"][1:16]]
    with gzip.open(args.tree, "rt", encoding="utf8") as stream:
        tree = json.load(stream)
    assert tree["complete"] and not tree["pending"]
    assert (tree["N"], tree["B"], tree["core_centers"], tree["faces"]) == (n, B, N, masks)
    assert tree["root_sha256"] == sha(rootpath) and tree["system_sha256"] == sha(systempath)
    assert tree["local_sha256"] == sha(localpath) and tree["constants_sha256"] == sha(constantspath)
    result = exact.verify(B, N, masks, tree["nodes"], constants,
                          local=local(anchors, F(isolation["anchor_radius"])))
    result.update(N=n, B=B, tree_sha256=sha(args.tree),
                  exact_checker_sha256=sha(ROOT / "exact_graph.py"),
                  force_kernel_sha256=sha(SYN / "round2-grouped/partial_force_exact.py"),
                  source_sha256=sha(Path(__file__)), local_certificate_sha256=sha(localpath),
                  scope="specified positive-core entire necessary angle domain",
                  no_optimizer_imported=True, global_optimality_proved=False)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2), encoding="utf8")
    print("N", n, "stdlib-only whole-angle fresh replay PASS", result["nodes"], flush=True)


if __name__ == "__main__":
    main()
