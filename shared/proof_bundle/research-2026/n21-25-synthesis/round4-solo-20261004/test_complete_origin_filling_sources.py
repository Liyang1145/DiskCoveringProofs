"""Finite exact-parent source-binding controls; no new graph lower bounds."""
from copy import deepcopy
from pathlib import Path
import argparse
import json
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / "round3-high"))
from stream_catalog import sha
from n25_outer_search import publish
from audit_complete_origin_fillings import match_family_source

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    catalogpath = ROOT / "n25-B15-degree-origin-complete-search-20261005-v1/UNION/CATALOG.jsonl"
    with catalogpath.open(encoding="ascii") as stream:
        next(stream)
        actual = json.loads(next(stream))
    row = {"parent_index": actual["id"], "centers": actual["centers"], "faces": actual["faces"]}
    digest = "finite-source-binding-fixture-not-a-production-snapshot"
    collar = {"N": 25, "B": 15, "centers": row["centers"], "faces": row["faces"],
              "complete_parent_index": row["parent_index"], "source_snapshot_sha256": digest}
    payload = {"N": 25, "B": 15, "collar_centers": row["centers"], "collar_faces": row["faces"]}
    match_family_source(row, collar, payload, 25, 15, digest)
    rejected = []
    for label, side, field, value in (
        ("wrong-collar-N", "collar", "N", 24),
        ("wrong-collar-B", "collar", "B", 16),
        ("wrong-collar-centers", "collar", "centers", row["centers"]-1),
        ("omitted-outer-face", "collar", "faces", row["faces"][:-1]),
        ("wrong-parent-index", "collar", "complete_parent_index", row["parent_index"]+1),
        ("wrong-snapshot-sha", "collar", "source_snapshot_sha256", "wrong"),
        ("wrong-proof-N", "payload", "N", 24),
        ("wrong-proof-B", "payload", "B", 16),
        ("wrong-proof-centers", "payload", "collar_centers", row["centers"]-1),
        ("wrong-proof-face", "payload", "collar_faces", row["faces"][:-1]),
    ):
        changed_collar, changed_payload = deepcopy(collar), deepcopy(payload)
        (changed_collar if side == "collar" else changed_payload)[field] = value
        try:
            match_family_source(row, changed_collar, changed_payload, 25, 15, digest)
        except AssertionError:
            rejected.append(label)
        else:
            raise AssertionError(("source mismatch accepted", label))
    output.mkdir()
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "complete-origin-filling-parent-source-binding-controls-v1",
        "finite_real_B15_union_graph_source_positive": True,
        "all_original_outer_faces_must_match_not_just_a_subgraph": True,
        "negative_controls_rejected": rejected,
        "source_sha256": sha(Path(__file__)),
        "snapshot_source_sha256": sha(ROOT / "snapshot_complete_origin_pending.py"),
        "worker_source_sha256": sha(ROOT / "pay_complete_origin_pending.py"),
        "merge_source_sha256": sha(ROOT / "audit_complete_origin_fillings.py"),
        "source_catalog_sha256": sha(catalogpath),
        "no_new_force_or_topological_completeness_theorem_in_this_adapter": True,
        "frozen_kernel_and_attaining_controls_separately_required": True,
        "not_a_full_parent_scan_or_mathematical_payment": True, "global_optimality_proved": False,
    })
    print("Complete-origin filling exact-parent source controls PASS:", len(rejected), "rejections", flush=True)


if __name__ == "__main__":
    main()
