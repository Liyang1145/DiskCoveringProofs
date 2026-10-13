"""Stdlib functional, exact-threshold and true recorded-attainer controls."""
from pathlib import Path
from fractions import Fraction as F
import argparse
import random
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / "round3-high"))
from stream_catalog import sha
from n25_outer_search import read, publish, bind, unchanged
from small_order_cover_origin import classify

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--core-inputs", type=Path, required=True)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    core_inputs = args.core_inputs.resolve()
    assert core_inputs.is_relative_to(ROOT)
    recovery_path = core_inputs / "VERIFIED.json"
    recovered = read(recovery_path)
    assert recovered["verified"] and recovered["schema"] == "isolated-selected-small-order-core-archive-byte-recovery-v1"
    assert recovered["source_sha256"] == sha(ROOT / "recover_selected_core_archive_inputs.py")
    unchanged(recovered["files_relative_to_workspace"])
    files, cases, rejected = {}, [], []
    rng = random.Random(23241005)
    for N, expected_U in ((23, F(249953776586051, 10**15)),
                          (24, F(61325412542131, 250000000000000))):
        constants_path = ROOT.parent / f"evidence/core-reduction/constants/n{N}.json"
        candidate_path = core_inputs / f"n{N}/core-system.json"
        constants, candidate = read(constants_path), read(candidate_path)
        assert constants["verified"] and constants["N"] == N
        assert F(constants["radius_upper"]) == expected_U < F(1, 4)
        B = candidate["B"]
        assert candidate["N"] == N
        full = sorted(sum(1 << v for v in face) for face in candidate["all_faces"])
        actual = classify(N, B, full, expected_U)
        boundary = (1 << B)-1
        outer = [mask for mask in full if mask & boundary]
        assert classify(N, B, outer, expected_U) == actual
        assert not actual["actual_cover_obstruction"] and actual["exposed_centers"] <= N-1
        cases.append({"N": N, "B": B, "recorded_attaining_full_graph_explicitly_retained": True,
                      "exposed_centers": actual["exposed_centers"], "strict_gap": str(1-4*expected_U)})
        # These arbitrary face lists test functionality, never full-family
        # coverage or the existence of any geometric disk cover.
        for used_internal in (list(range(B, N)), list(range(B, N-1))):
            faces = sorted((1 << 0) | (1 << 1) | (1 << v) for v in used_internal)
            result = classify(N, B, faces, expected_U)
            assert result["actual_cover_obstruction"] == (len(used_internal) == N-B)
        for _ in range(100):
            triangles = {sum(1 << v for v in rng.sample(range(N), 3)) for _ in range(rng.randrange(1, 40))}
            faces = sorted(triangles)
            exposed = set(range(B))
            for mask in faces:
                if mask & boundary:
                    exposed.update(v for v in range(N) if mask >> v & 1)
            result = classify(N, B, faces, expected_U)
            assert result["exposed_label_mask"] == sum(1 << v for v in exposed)
            assert result["actual_cover_obstruction"] == (len(exposed) == N)
        for radius in (F(1, 4), F(13, 50)):
            try:
                classify(N, B, full, radius)
            except AssertionError:
                rejected.append(f"N{N}-non-strict-radius-{radius}")
            else:
                raise AssertionError("quarter-radius equality was excluded")
        for path in (constants_path, candidate_path):
            bind(files, path)
    q, b, w, c, radius = F(1), F(3, 4), F(1, 2), F(1, 4), F(1, 4)
    assert abs(q-b) == abs(b-w) == abs(w-c) == abs(c) == radius
    for path in (Path(__file__), recovery_path, ROOT / "small_order_cover_origin.py",
                 ROOT / "refine_collar_origin.py", ROOT / "N23-N24-UNEXPOSED-ORIGIN-SOURCE.md",
                 ROOT / "N25-COLLAR-COVER-INTERFACE.md"):
        bind(files, path)
    unchanged(files)
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath"))
    output.mkdir()
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "N23-N24-actual-cover-origin-necessity-controls-v1",
        "recorded_attaining_cases": cases, "independent_random_face_union_controls": 200,
        "quarter_radius_local_equality_not_excluded": True, "negative_controls_rejected": rejected,
        "no_N25_optimality_or_force_theorem_used": True,
        "no_live_enumerator_kernel_or_existing_evidence_modified": True,
        "full_family_partition_and_actual_cover_transport_still_required": True,
        "source_sha256": sha(Path(__file__)), "files_relative_to_workspace": files,
        "global_optimality_proved": False,
    })
    print("N23/N24 origin necessity controls PASS; both recorded attaining full graphs retained", flush=True)


if __name__ == "__main__":
    main()
