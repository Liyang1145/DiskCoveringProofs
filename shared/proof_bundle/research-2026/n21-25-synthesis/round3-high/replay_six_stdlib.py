"""Independent hexagon census and stateless exact six-disk tree replay.

The gap cap is checked exactly, not generated with an inverse trig optimizer.
Only adjacent gap bounds are used: four/six-rod caps for n22 MUST NOT be used
at the larger six-disk radius. The actual-cover reduction is a written lemma.
"""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
from functools import lru_cache
import argparse
import gzip
import json
import sys
import exact_graph as exact
from stream_catalog import sha, no_duplicate_keys

ROOT = Path(__file__).resolve().parent
WORK = ROOT.parents[2]
SOURCE = ROOT.parent.parent / "n21-global/evidence"
sys.path.insert(0, str(exact.kernel.ARCS))
import exact_arcs as arcs
assert __debug__


@lru_cache(None)
def polygons(vertices):
    if len(vertices) < 3:
        return {()}
    out = set()
    for k in range(1, len(vertices)-1):
        triangle = sum(1 << v for v in (vertices[0], vertices[k], vertices[-1]))
        for left in polygons(vertices[:k+1]):
            for right in polygons(vertices[k:]):
                out.add(tuple(sorted(left+right+(triangle,))))
    return out


def orbit(code):
    out = []
    for sign in (1, -1):
        for shift in range(6):
            out.append(tuple(sorted(sum(1 << ((shift+sign*v) % 6)
                                        for v in range(6) if mask >> v & 1)
                                    for mask in code)))
    return out


def verify(faces, nodes, cap, D, U):
    masks = sorted(sum(1 << v for v in face) for face in faces)
    _, edges, V = exact.graph(6, 6, masks)
    matrix = [[10**9]*6 for _ in range(6)]
    for i in range(6):
        matrix[i][i] = 0
        j = (i+1) % 6
        matrix[i][j] = min(matrix[i][j], cap-(D if j == 0 else 0))
        matrix[j][i] = min(matrix[j][i], D if j == 0 else 0)
    for k in range(6):
        for i in range(6):
            for j in range(6):
                matrix[i][j] = min(matrix[i][j], matrix[i][k]+matrix[k][j])
    assert all(matrix[i][i] == 0 for i in range(6))
    lo, hi = exact.rootbox(matrix, D)
    todo, seen, counts, minimum = [(0, lo, hi)], set(), Counter(), None
    while todo:
        index, lo, hi = todo.pop()
        assert type(index) is int and 0 <= index < len(nodes) and index not in seen
        seen.add(index)
        node = nodes[index]
        assert node["kind"] in ("EMPTY", "SPLIT", "DUAL")
        box = exact.kernel.tighten(matrix, lo, hi, D)
        if node["kind"] == "EMPTY":
            assert box is None
        else:
            assert box is not None
            lo, hi = box
            if node["kind"] == "DUAL":
                margin = exact.kernel.force_margin(6, V, edges, lo, hi, node["certificate"], U)
                assert margin > 0
                minimum = margin if minimum is None else min(minimum, margin)
            else:
                axis, cut, children = node["axis"], F(node["mid"]), node["children"]
                assert type(axis) is int and 0 <= axis < 5 and lo[axis] < cut < hi[axis]
                assert len(children) == 2 and children[0] != children[1]
                assert all(type(j) is int and 0 <= j < len(nodes) for j in children)
                left, right = list(hi), list(lo)
                left[axis], right[axis] = cut, cut
                todo.extend(((children[0], list(lo), left), (children[1], right, list(hi))))
        counts[node["kind"]] += 1
    assert seen == set(range(len(nodes))) and minimum is not None
    return {"verified": True, "nodes": len(nodes), "counts": dict(counts),
            "minimum_margin": str(minimum), "vertices": V, "edges": len(edges)}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    Q, cap, D = F(2771, 5000), 1869759, 10**7
    sine = arcs.sincos_turn(F(cap, 2*D))[1]
    assert Q < F(sine[0], arcs.SCALE)
    assert Q < F(arcs.sincos_turn(F(1, 10))[1][0], arcs.SCALE)
    alltypes = polygons(tuple(range(6)))
    assert len(alltypes) == 14
    classes = {min(orbit(code)) for code in alltypes}
    assert len(classes) == 3
    catpath = SOURCE / "peeling-round1/N6-B6-noscreen.json"
    census = json.loads(catpath.read_text(), object_pairs_hook=no_duplicate_keys)
    assert census["complete"] and not census["screen"] and census["orbits"] == 3
    represented, reports = set(), []
    for index, row in enumerate(census["survivors"]):
        code = tuple(row["faces"])
        assert code in alltypes
        representative = min(orbit(code))
        assert representative not in represented
        represented.add(representative)
        stabilizer = sum(value == code for value in orbit(code))
        assert row["stabilizer"] == stabilizer and 12 % stabilizer == 0
        faces = [[v for v in range(6) if mask >> v & 1] for mask in code]
        path = SOURCE / f"six-core-exclusion/hexagon-{index}.json.gz"
        with gzip.open(path, "rt", encoding="utf8") as stream:
            tree = json.load(stream, object_pairs_hook=no_duplicate_keys)
        assert (tree["B"], tree["N"], tree["faces"]) == (6, 6, faces)
        assert F(tree["radius"]) == Q and tree["gap_cap"] == cap and tree["scale"] == D
        report = verify(faces, tree["nodes"], cap, D, Q)
        report.update(index=index, stabilizer=stabilizer, tree_sha256=sha(path))
        reports.append(report)
    assert represented == classes
    assert sum(12//row["stabilizer"] for row in reports) == 14
    result = {"verified": True, "radius": str(Q), "gap_cap": cap, "gap_scale": D,
              "independently_enumerated_fixed_boundary_types": 14,
              "topology_orbits": 3, "trees": reports, "six_census_sha256": sha(catpath),
              "no_optimizer_imported": True,
              "actual_cover_reduction_is_separate_written_lemma": True,
              "force_kernel_sha256": sha(ROOT.parent / "round2-grouped/partial_force_exact.py"),
              "trig_source_sha256": sha(exact.kernel.ARCS / "exact_arcs.py"),
              "source_sha256": sha(Path(__file__)), "global_optimality_proved": False}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2), encoding="utf8")
    print("Six-disk independent 14-type census + 3 exact trees stdlib PASS", flush=True)


if __name__ == "__main__":
    main()
