"""Stdlib-only leaf math and COMPLETE paid/unpaid partition for a smaller core."""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
from math import isqrt
import argparse
import gzip
import json
import sys
import exact_graph as exact
from replay_candidate import local
from stream_catalog import sha, no_duplicate_keys

ROOT = Path(__file__).resolve().parent
assert __debug__


def read(path):
    return json.loads(path.read_text(encoding="utf8"), object_pairs_hook=no_duplicate_keys)


def inputs(sign):
    assert type(sign) is int and sign in (-1, 1)
    paths = {
        "constants": ROOT.parent / "evidence/core-reduction/constants/n25.json",
        "local": ROOT / "evidence/n25-endpoint-core-isolation-resume1/REPORT.json",
        "geometry": ROOT / "evidence/n25-isolation-exact-resume1/rotated-geometry.json",
        "fibre": ROOT / "evidence/n25-stress-freedom-exact-resume1/VERIFIED.json",
        "character": ROOT / "evidence/n25-stress-character-resume2.json",
    }
    constants, certificate, geometry, fibre, character = (
        read(paths[key]) for key in ("constants", "local", "geometry", "fibre", "character"))
    assert all(row["verified"] for row in (constants, certificate, fibre, character))
    assert constants["N"] == certificate["N"] == 25
    assert certificate["geometry_sha256"] == sha(paths["geometry"])
    assert certificate["fibre_report_sha256"] == sha(paths["fibre"])
    assert certificate["stress_character_sha256"] == sha(paths["character"])
    assert certificate["source_sha256"] == sha(ROOT / "n25_endpoint_core_isolation.py")
    assert certificate["rounding_source_sha256"] == sha(ROOT / "n25_anchor_isolation.py")
    choices = [row for row in certificate["cores"] if row["parameter_sign"] == sign]
    assert len(choices) == 1
    core = choices[0]
    assert core["verified"] and (core["G"], core["core_nodes"], core["positive_rods"]) == (120, 61, 92)
    assert core["positive_leading_principal_minors"] == 120
    assert F(core["isolation_margin"]) == F(1, 25000)
    assert F(core["anchor_radius"]) == F(1, 50)
    assert core["old_nodes_retained"][:41] == list(range(41))
    assert core["points_Qsqrt2"][:41] == geometry["points_Qsqrt2"][:41]
    oldfaces = core["old_face_indices_retained"]
    assert core["faces"] == [geometry["faces"][i] for i in oldfaces]
    masks = sorted(sum(1 << v for v in face) for face in core["faces"])
    assert len(set(masks)) == 20
    faces, edges, V = exact.graph(16, 25, masks)
    assert V == 61 and len(edges) == 92
    assert core["edges"][:32] == [list(e) for e in edges[:32]]
    assert sorted(map(sorted, core["faces"])) == sorted(faces)
    scale = 10**80
    lower = isqrt(2*scale*scale)
    assert lower**2 < 2*scale*scale < (lower+1)**2
    def enclosure(value):
        a, b = map(F, value)
        first, last = a+b*F(lower, scale), a+b*F(lower+1, scale)
        return min(first, last), max(first, last)
    anchors = [[enclosure(v) for v in point] for point in core["points_Qsqrt2"][1:16]]
    bound = {key: sha(path) for key, path in paths.items()}
    bound.update(exact_checker=sha(ROOT / "exact_graph.py"),
                 force_kernel=sha(ROOT.parent / "round2-grouped/partial_force_exact.py"),
                 trig_source=sha(exact.kernel.ARCS / "exact_arcs.py"),
                 anchor_checker=sha(ROOT / "replay_candidate.py"))
    return constants, masks, local(anchors, F(core["anchor_radius"])), bound, core


def replay(tree):
    sign = tree["parameter_sign"]
    constants, masks, anchorcheck, bound, core = inputs(sign)
    assert tree["input_sha256"] == bound
    assert (tree["N"], tree["B"], tree["core_centers"], tree["faces"]) == (25, 16, 25, masks)
    B, N = 16, 25
    faces, edges, V = exact.graph(B, N, masks)
    matrix = exact.kernel.angle_bounds(B, N, faces, constants)
    scale = constants["angle_scale"]
    lo, hi = exact.rootbox(matrix, scale)
    pending = tree["pending"]
    unpaid = {row["index"]: row for row in pending}
    assert len(unpaid) == len(pending)
    assert all(type(i) is int for i in unpaid)
    nodes, seen, stack = tree["nodes"], set(), [(0, lo, hi)]
    counts = Counter()
    minimumforce = minimumlocal = None
    while stack:
        i, lo, hi = stack.pop()
        assert type(i) is int and 0 <= i < len(nodes) and i not in seen
        seen.add(i)
        node = nodes[i]
        if node is None:
            assert i in unpaid
            assert unpaid[i]["lo"] == list(map(str, lo)) and unpaid[i]["hi"] == list(map(str, hi))
            counts["PENDING"] += 1
            continue
        assert i not in unpaid and node["kind"] in ("EMPTY", "SPLIT", "DUAL", "LOCAL")
        box = exact.kernel.tighten(matrix, lo, hi, scale)
        if node["kind"] == "EMPTY":
            assert box is None
        else:
            assert box is not None
            lo, hi = box
            if node["kind"] == "DUAL":
                margin = exact.kernel.force_margin(B, V, edges, lo, hi, node["certificate"],
                                                   F(constants["radius_upper"]))
                assert margin > 0
                minimumforce = margin if minimumforce is None else min(minimumforce, margin)
            elif node["kind"] == "LOCAL":
                margin = anchorcheck(lo, hi)
                assert margin is not None and margin > 0
                minimumlocal = margin if minimumlocal is None else min(minimumlocal, margin)
            else:
                axis, cut, children = node["axis"], F(node["mid"]), node["children"]
                assert type(axis) is int and 0 <= axis < B-1 and lo[axis] < cut < hi[axis]
                assert len(children) == 2 and children[0] != children[1]
                assert all(type(j) is int and 0 <= j < len(nodes) for j in children)
                left, right = list(hi), list(lo)
                left[axis], right[axis] = cut, cut
                stack.extend([(children[0], list(lo), left), (children[1], right, list(hi))])
        counts[node["kind"]] += 1
    assert seen == set(range(len(nodes)))
    assert {i for i, node in enumerate(nodes) if node is None} == set(unpaid)
    assert tree["complete"] == (not unpaid)
    return {"verified": True, "N": N, "B": B, "parameter_sign": sign,
            "nodes": len(nodes), "counts": dict(counts), "pending_boxes": len(unpaid),
            "minimum_force_margin": None if minimumforce is None else str(minimumforce),
            "minimum_local_margin": None if minimumlocal is None else str(minimumlocal),
            "paid_unpaid_partition_complete": True, "entire_angle_domain_proved": not unpaid,
            "input_sha256": bound, "global_optimality_proved": False,
            "scope": "specified endpoint core paid/unpaid continuous-domain partition only"}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--tree", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    with gzip.open(args.tree, "rt", encoding="utf8") as stream:
        tree = json.load(stream, object_pairs_hook=no_duplicate_keys)
    result = replay(tree)
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath"))
    result.update(tree_sha256=sha(args.tree), source_sha256=sha(Path(__file__)),
                  no_optimizer_imported=True)
    args.output.write_text(json.dumps(result, indent=2), encoding="utf8")
    print("N25 reduced-core independent exact partition PASS; pending",
          result["pending_boxes"], flush=True)


if __name__ == "__main__":
    main()
