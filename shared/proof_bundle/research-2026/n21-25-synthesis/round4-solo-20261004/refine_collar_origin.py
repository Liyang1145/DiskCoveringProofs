"""Independent complete residual partition by the actual-cover origin condition."""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
import argparse
import json
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha, no_duplicate_keys
from n25_outer_search import read, publish, bind, unchanged

assert __debug__


def radius_gate(U):
    assert F(0) < U < F(1, 4), "origin obstruction requires a strict quarter-radius gap"
    return F(1)-4*U


def exposed_mask(N, B, faces):
    assert 3 <= B <= N <= 25
    assert faces == sorted(set(faces))
    assert all(type(mask) is int and 0 < mask < 1 << N and mask.bit_count() == 3 for mask in faces)
    boundary = (1 << B)-1
    used = boundary
    for mask in faces:
        if mask & boundary:
            used |= mask
    return used


def controls(U):
    gap = radius_gate(U)
    assert F(1)-3*U > U and gap > 0
    geometry = read(HIGH.parent / "evidence/n25-algebraic-upper-round2/geometry.json")
    full = sorted(sum(1 << v for v in face) for face in geometry["faces"])
    outer = [mask for mask in full if mask & ((1 << 16)-1)]
    assert exposed_mask(25, 16, full) == exposed_mask(25, 16, outer)
    assert exposed_mask(25, 16, outer).bit_count() == 24
    assert exposed_mask(25, 16, outer) != (1 << 25)-1
    local = read(ROOT / "n25-B14-complete-g0-simple-hole-completions-20261005-v1/INPUT-COLLAR.json")
    assert local["centers"] == 25 and exposed_mask(25, 14, local["faces"]) == (1 << 25)-1
    for radius in (F(1, 4), F(13, 50)):
        try:
            radius_gate(radius)
        except AssertionError:
            pass
        else:
            raise AssertionError("origin condition applied beyond its strict radius range")
    # At r=1/4, q=1,b=3/4,w=1/2,c=1/4 meets every local rod
    # bound and c's disk reaches 0. Equality must not be excluded.
    q, b, w, c, r = F(1), F(3, 4), F(1, 2), F(1, 4), F(1, 4)
    assert abs(q-b) == abs(b-w) == abs(w-c) == abs(c) == r
    return {"known_N25_B16_attaining_graph_retained": True,
            "pure_internal_faces_not_counted_as_exposure": True,
            "real_N25_B14_V25_source_classified_as_cover_obstruction": True,
            "quarter_and_larger_radius_rejected": True,
            "quarter_radius_local_equality_control": True}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--parent", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    parent, output = args.parent.resolve(), args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    reportpath, residualpath = parent / "VERIFIED.json", parent / "RESIDUAL.jsonl"
    parent_report = read(reportpath)
    assert parent_report["verified"] and parent_report["schema"] == "complete-old-collar-independent-paid-partition-v1"
    assert parent_report["all_complete_parent_rows_processed_once"] and parent_report["N"] == 25
    assert parent_report["source_sha256"] == sha(ROOT / "filter_complete_collar_cached.py")
    assert sha(residualpath) == parent_report["residual_sha256"]
    unchanged(parent_report["files_relative_to_workspace"])
    constants_path = HIGH.parent / "evidence/core-reduction/constants/n25.json"
    constants = read(constants_path)
    assert constants["verified"] and constants["N"] == 25
    U = F(constants["radius_upper"])
    assert U == F(239146311738101, 10**15)
    gap, tested = radius_gate(U), controls(U)
    B = parent_report["B"]
    assert B in (14, 15, 16, 17)
    output.mkdir()
    counts = Counter()
    seen = paid = remaining = 0
    previous_id, previous_code = -1, None
    payments, targetpath = output / "ORIGIN-PAYMENTS.jsonl", output / "RESIDUAL.jsonl"
    with residualpath.open(encoding="ascii") as source, payments.open("x", encoding="ascii") as ledger, \
            targetpath.open("x", encoding="ascii") as target:
        header = json.loads(next(source), object_pairs_hook=no_duplicate_keys)
        assert header == {
            "schema": "complete-paid-old-collar-residual-v1", "N": 25, "B": B,
            "source_catalog_sha256": parent_report["parent_groups_sha256"],
            "members_are_weak_graphs_not_full_types": True,
        }
        target.write(json.dumps({
            "schema": "complete-collar-origin-refined-residual-v1", "N": 25, "B": B,
            "source_catalog_sha256": parent_report["parent_groups_sha256"],
            "parent_partition_sha256": sha(reportpath), "members_are_weak_graphs_not_full_types": True,
            "actual_cover_origin_necessity_applied": True,
        }, separators=(",", ":"))+"\n")
        for line in source:
            row = json.loads(line, object_pairs_hook=no_duplicate_keys)
            gid, centers, faces = row["id"], row["centers"], row["faces"]
            assert row["members"] == 1 and previous_id < gid < parent_report["parent_weak_graphs"]
            assert type(centers) is int and B <= centers <= 25
            assert faces and all(mask & ((1 << B)-1) for mask in faces)
            mask = exposed_mask(centers, B, faces)
            assert mask == (1 << centers)-1, "declared compressed centers not all exposed"
            code = tuple(faces)
            assert previous_code is None or previous_code < code
            previous_id, previous_code = gid, code
            counts[centers] += 1
            if mask == (1 << 25)-1:
                ledger.write(json.dumps({
                    "parent_group": gid, "kind": "actual-cover-origin-unexposed-center-obstruction",
                    "actual_cover_radius_lower": "1/4", "radius_upper": str(U), "strict_gap_1_minus_4U": str(gap),
                    "all_25_labels_appear_in_boundary_or_outer_faces": True,
                    "not_a_standalone_geometric_weak_graph_exclusion": True,
                }, separators=(",", ":"))+"\n")
                paid += 1
            else:
                target.write(json.dumps(row, separators=(",", ":"))+"\n")
                remaining += 1
            seen += 1
    assert seen == parent_report["residual_weak_graphs"] == paid+remaining == sum(counts.values())
    assert sha(residualpath) == parent_report["residual_sha256"]
    unchanged(parent_report["files_relative_to_workspace"])
    files = {}
    for path in (
        Path(__file__), constants_path, reportpath, residualpath,
        ROOT / "UNEXPOSED-ORIGIN-CENTER-SOURCE.md", ROOT / "N25-COLLAR-COVER-INTERFACE.md",
        ROOT / "n25-B14-complete-g0-simple-hole-completions-20261005-v1/INPUT-COLLAR.json",
        HIGH.parent / "evidence/n25-algebraic-upper-round2/geometry.json",
    ):
        bind(files, path)
    unchanged(files)
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "complete-collar-actual-cover-origin-refinement-v1",
        "N": 25, "B": B, "all_complete_parent_residual_rows_partitioned_once": True,
        "parent_residual_weak_graphs": seen, "origin_obstruction_paid": paid,
        "remaining_weak_graphs": remaining, "center_count_partition": dict(sorted(counts.items())),
        "radius_upper": str(U), "strict_gap_1_minus_4U": str(gap),
        "single_unexposed_center_norm_upper_bound_5U_minus_1": str(5*U-1),
        "single_unexposed_norm_bound_not_used_in_current_force_kernel": True,
        "actual_arbitrary_cover_condition_required": True,
        "not_a_standalone_geometric_weak_graph_exclusion": True,
        "source_cover_reduction_and_padding_preserves_origin_owner": True,
        "control_results": tested, "parent_report_sha256": sha(reportpath),
        "parent_residual_sha256": sha(residualpath), "origin_payments_sha256": sha(payments),
        "refined_residual_sha256": sha(targetpath), "files_relative_to_workspace": files,
        "source_sha256": sha(Path(__file__)),
        "all_other_residual_lower_bounds_not_paid_here": True, "global_optimality_proved": False,
    })
    print("Complete actual-cover origin refinement accepted:", paid, "cover obstructions;",
          remaining, "still pending;", dict(sorted(counts.items())), flush=True)


if __name__ == "__main__":
    main()
