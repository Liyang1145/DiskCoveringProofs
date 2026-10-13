"""Old-format equivalence, rejection tests and known attainment controls."""
from pathlib import Path
from fractions import Fraction as F
import argparse
import copy
import gzip
import json
import bounded_exact as E
import exact_graph as exact
from actual_norm_bounds import constants as norm_constants
from bounded_proposals import Solver
from stream_catalog import sha

ROOT = Path(__file__).resolve().parent
assert __debug__


def rejects(action):
    try:
        action()
    except (AssertionError, ValueError, KeyError, RuntimeError):
        return True
    return False


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    tests = []
    folder = ROOT.parent / "round2-grouped/evidence/B14-full-root-resume1"
    for path in sorted(folder.glob("group-*.json.gz"))[:20]:
        with gzip.open(path, "rt") as stream:
            tree = json.load(stream)
        assert len(tree["nodes"]) == 1 and tree["nodes"][0]["kind"] == "DUAL"
        B, N = tree["B"], tree["partial_centers"]
        constants, radii, premise = norm_constants(21, B, N, len(tree["faces"]))
        faces, edges, V = exact.graph(B, N, tree["faces"])
        matrix = exact.kernel.angle_bounds(B, N, faces, constants)
        lo, hi = exact.rootbox(matrix, constants["angle_scale"])
        lo, hi = exact.kernel.tighten(matrix, lo, hi, constants["angle_scale"])
        old = tree["nodes"][0]["certificate"]
        new = copy.deepcopy(old)
        new["b"] += [0]*(2*(V-B))
        original_margin = exact.kernel.force_margin(B, V, edges, lo, hi, old, F(constants["radius_upper"]))
        new_margin = E.force_margin(B, V, edges, lo, hi, new, F(constants["radius_upper"]), radii)
        assert original_margin == new_margin > 0
        assert rejects(lambda: E.force_margin(B, V, edges, lo, hi, old, F(constants["radius_upper"]), radii))
        zeros = {key: ([0]*len(value) if isinstance(value, list) else value) for key, value in new.items()}
        assert rejects(lambda: E.force_margin(B, V, edges, lo, hi, zeros, F(constants["radius_upper"]), radii))
        result = E.verify(21, B, N, tree["faces"], [{"kind": "BDUAL", "certificate": new}])
        assert result["verified"]
        tests.append({"old_tree_sha256": sha(path), "exact_margin_equal": True,
                      "truncated_support_rejected": True, "zero_force_rejected": True})
    assert len(tests) == 20
    controls = []
    for n in (22, 25):
        if n == 22:
            data = json.loads((ROOT.parent / "evidence/n22/core-system.json").read_text())
            B, N, raw = 14, 22, data["all_faces"]
        else:
            data = json.loads((ROOT.parent / "evidence/n25-algebraic-upper-round2/geometry.json").read_text())
            B, N, raw = 16, 25, data["faces"]
        masks = sorted(sum(1 << v for v in face) for face in raw)
        solver = Solver(n, B, N, masks)
        matrix = exact.kernel.angle_bounds(B, N, solver.faces, solver.constants)
        lo, hi = exact.rootbox(matrix, solver.constants["angle_scale"])
        lo, hi = exact.kernel.tighten(matrix, lo, hi, solver.constants["angle_scale"])
        force, x = solver.solve(lo, hi)
        assert force is None, "Known attaining cover cannot be strictly excluded by new norm cones"
        controls.append({"N": n, "known_attainment_not_excluded": True})
    result = {"verified": True, "old_format_equivalence_controls": tests,
              "known_attainment_controls": controls, "source_sha256": sha(Path(__file__)),
              "bounded_checker_sha256": sha(ROOT / "bounded_exact.py"),
              "not_a_proof_of_all_software_correctness": True, "global_optimality_proved": False}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2), encoding="utf8")
    print("New bounded-support exact format controls PASS", flush=True)


if __name__ == "__main__":
    main()
