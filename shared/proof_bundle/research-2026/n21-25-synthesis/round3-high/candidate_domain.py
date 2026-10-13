"""Propose and exactly verify per-n positive-core whole-angle lower bounds.

n22..24 use isolated KKT root inputs; n25 uses exact algebraic geometry and
stress isolation.  This never proves a complete arbitrary-cover optimum alone.
"""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
from types import SimpleNamespace
import argparse
import gzip
import hashlib
import json
from math import isqrt
import sys
import time
import numpy as np
import exact_graph as exact

ROOT = Path(__file__).resolve().parent
SYN = ROOT.parent
sys.path.insert(0, str(SYN / "round2-grouped"))
from conic_proposals import make_solver_class
kernel = exact.kernel
sys.path.insert(0, str(kernel.ARCS))
import compact_force20 as C
import exact_arcs as arcs
assert __debug__


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def interval_dot(a, b):
    products = [tuple(x*y for x in iv for y in jv) for iv, jv in zip(a, b)]
    return sum(min(p) for p in products), sum(max(p) for p in products)


def local_checker(B, root, radius):
    midpoint = [F(v, int(root["Qx"])) for v in map(int, root["xnum"])]
    eps = F(1, 10**80)
    anchors = [[(midpoint[2*(i-1)+j]-eps, midpoint[2*(i-1)+j]+eps) for j in (0, 1)]
               for i in range(1, B)]
    return local_from_anchors(anchors, radius)


def local_from_anchors(anchors, radius):
    def unit(turn):
        return [(F(lo, arcs.SCALE), F(hi, arcs.SCALE)) for lo, hi in arcs.sincos_turn(turn)]
    def local(lo, hi):
        distance = F(0)
        for l, h, anchor in zip(lo, hi, anchors):
            if h-l >= F(1, 2) or interval_dot(unit((l+h)/2), anchor)[0] <= 0:
                return None
            lower = min(interval_dot(unit(l), anchor)[0], interval_dot(unit(h), anchor)[0])
            distance += 2-2*lower
        return radius**2-distance
    return local


def configure(B, N, masks, constants):
    faces, edges, V = exact.graph(B, N, masks)
    G = SimpleNamespace(N=N, V=V, RU=F(constants["radius_upper"]),
                        QA=arcs.QA, QB=arcs.QB, arc_halfplane=arcs.arc_halfplane)
    def edgefn(b, f):
        assert b == B and f == faces
        return edges
    G.edges = edgefn
    C.N, C.V, C.RU = N, V, G.RU
    C.tree.cache_clear()
    solver = make_solver_class(G, C)(B, faces)
    return faces, edges, V, solver


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, choices=(22, 23, 24, 25), required=True)
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--limit", type=int, default=30001)
    ap.add_argument("--resume", type=Path)
    args = ap.parse_args()
    assert not args.output.exists()
    args.output.mkdir(parents=True)
    constants_path = SYN / f"evidence/core-reduction/constants/n{args.n}.json"
    constants = json.loads(constants_path.read_text())
    if args.n < 25:
        folder = SYN / f"evidence/n{args.n}"
        systempath, rootpath = folder / "core-system.json", folder / "core-root.json"
        local_path = folder / "local-isolation-certificate.json"
        data = json.loads(systempath.read_text())
        root = json.loads(rootpath.read_text())
    else:
        systempath = rootpath = ROOT / "evidence/n25-isolation-exact-resume1/rotated-geometry.json"
        local_path = ROOT / "evidence/n25-isolation-exact-resume1/VERIFIED.json"
        algebraic = json.loads(systempath.read_text())
        data = {"B": 16, "G": 144, "active_faces": algebraic["faces"],
                "center_core_nodes": list(range(16, 41)), "edges": algebraic["edges"]}
    certificate = json.loads(local_path.read_text())
    assert constants["verified"] and certificate["verified"]
    binding_key = "root_sha256" if args.n < 25 else "rotated_geometry_sha256"
    assert certificate[binding_key] == sha(rootpath)
    assert certificate["geometry_dimension"] == data["G"] and F(certificate["isolation_margin"]) > 0
    B = data["B"]
    N = (data["G"] // 2 + 1) - B - len(data["active_faces"])
    masks = sorted(sum(1 << (data["center_core_nodes"][v]-B) for v in face)
                   for face in data["active_faces"])
    faces, edges, V, solver = configure(B, N, masks, constants)
    # Sorting center-face masks changes their witness ordering; each witness
    # is free, so an explicit reindexing establishes the same core rod graph.
    boundary = edges[:2*B]
    assert boundary == [tuple(e) for e in data["edges"][:2*B]]
    old_faces = [sorted(data["center_core_nodes"][v]-B for v in face)
                 for face in data["active_faces"]]
    assert sorted(old_faces) == sorted(faces) and len(set(map(tuple, old_faces))) == len(faces)
    for j, face in enumerate(old_faces):
        assert data["edges"][2*B+3*j:2*B+3*j+3] == [[B+N+j, B+k] for k in face]
    if args.n < 25:
        local = local_checker(B, root, F(certificate["anchor_radius"]))
    else:
        scale = 10**80
        sqrtlow = isqrt(2*scale*scale)
        assert sqrtlow**2 < 2*scale*scale < (sqrtlow+1)**2
        def enclosure(value):
            a, b = map(F, value)
            bounds = [a+b*F(sqrtlow, scale), a+b*F(sqrtlow+1, scale)]
            return min(bounds), max(bounds)
        anchors = [[enclosure(value) for value in p]
                   for p in algebraic["points_Qsqrt2"][1:16]]
        local = local_from_anchors(anchors, F(certificate["anchor_radius"]))
    mat = kernel.angle_bounds(B, N, faces, constants)
    D = constants["angle_scale"]
    lo, hi = exact.rootbox(mat, D)
    nodes, stack = [None], [(0, lo, hi)]
    if args.resume is not None:
        with gzip.open(args.resume, "rt", encoding="utf8") as stream:
            previous = json.load(stream)
        assert not previous["complete"] and previous["N"] == args.n
        assert previous["B"] == B and previous["core_centers"] == N and previous["faces"] == masks
        assert previous["root_sha256"] == sha(rootpath) and previous["system_sha256"] == sha(systempath)
        assert previous["constants_sha256"] == sha(constants_path) and previous["local_sha256"] == sha(local_path)
        nodes = previous["nodes"]
        stack = [(p["index"], list(map(F, p["lo"])), list(map(F, p["hi"]))) for p in previous["pending"]]
        assert {i for i, node in enumerate(nodes) if node is None} == {p[0] for p in stack}
    counts = Counter(node["kind"] for node in nodes if node is not None)
    started = time.monotonic()
    while stack and len(nodes) <= args.limit:
        index, lo, hi = stack.pop()
        box = kernel.tighten(mat, lo, hi, D)
        if box is None:
            nodes[index] = {"kind": "EMPTY"}
            counts["EMPTY"] += 1
            continue
        lo, hi = box
        margin = local(lo, hi)
        if margin is not None and margin > 0:
            nodes[index] = {"kind": "LOCAL"}
        else:
            force, x, status = solver.solve_slsqp(lo, hi)
            if force is not None:
                assert kernel.force_margin(B, V, edges, lo, hi, force, F(constants["radius_upper"])) > 0
                nodes[index] = {"kind": "DUAL", "certificate": force}
            else:
                widths = [h-l for l, h in zip(lo, hi)]
                q = np.asarray(x[:2*(B-1)]).reshape(-1, 2)
                deficits = 1-np.sum(q*q, axis=1)
                axis = max(range(B-1), key=lambda j: max(0., float(deficits[j])) if widths[j] > F(1, 10**12) else -1)
                if deficits[axis] < 1e-10 or widths[axis] <= 0:
                    axis = max(range(B-1), key=lambda j: widths[j])
                assert widths[axis] > 0
                cut = (lo[axis]+hi[axis])/2
                child = len(nodes)
                nodes.extend([None, None])
                nodes[index] = {"kind": "SPLIT", "axis": axis, "mid": str(cut), "children": [child, child+1]}
                left, right = list(hi), list(lo)
                left[axis], right[axis] = cut, cut
                stack.extend([(child+1, right, list(hi)), (child, list(lo), left)])
        counts[nodes[index]["kind"]] += 1
        if sum(counts.values()) % 500 == 0:
            print("N", args.n, "core-angle", len(nodes), "pending", len(stack), "seconds",
                  round(time.monotonic()-started, 2), flush=True)
    payload = {"N": args.n, "B": B, "core_centers": N, "faces": masks, "nodes": nodes,
               "complete": not stack,
               "pending": [{"index": i, "lo": list(map(str, l)), "hi": list(map(str, h))} for i, l, h in stack],
               "root_sha256": sha(rootpath), "system_sha256": sha(systempath),
               "constants_sha256": sha(constants_path), "local_sha256": sha(local_path),
               "global_optimality_proved": False}
    if args.resume is not None:
        payload["resume_input_sha256"] = sha(args.resume)
    path = args.output / "core-angle-tree.json.gz"
    with gzip.open(path, "wt", encoding="utf8") as stream:
        json.dump(payload, stream, separators=(",", ":"))
    if not stack:
        result = exact.verify(B, N, masks, nodes, constants, local=local)
        result.update(N=args.n, B=B, scope="positive-core entire necessary angle domain only",
                      tree_sha256=sha(path), global_optimality_proved=False)
        (args.output / "VERIFIED.json").write_text(json.dumps(result, indent=2), encoding="utf8")
        print("N", args.n, "positive-core whole-angle lower theorem PASS", result, flush=True)
    else:
        print("N", args.n, "core-angle PENDING; no whole-domain theorem", flush=True)


if __name__ == "__main__":
    main()
