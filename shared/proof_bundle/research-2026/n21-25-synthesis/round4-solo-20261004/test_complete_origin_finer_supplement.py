"""Finite ledger and exact conditional-source refusal controls."""
from io import StringIO
from copy import deepcopy
from pathlib import Path
import argparse
import json
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / "round3-high"))
from stream_catalog import sha
from n25_outer_search import publish
from audit_complete_origin_finer_supplement import valid_payment_partition, full_filling_source

assert __debug__


def encoded(rows):
    return StringIO("".join(json.dumps(row)+"\n" for row in rows))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    paid = [{"parent_index": 0}, {"parent_index": 2}]
    pending = [{"parent_index": 1}, {"parent_index": 3}]
    assert [row[0] for row in valid_payment_partition(4, encoded(paid), encoded(pending))] == list(range(4))
    rejected = []
    for label, badpaid, badpending in (
        ("missing-paid-row", paid[:-1], pending),
        ("missing-pending-row", paid, pending[:-1]),
        ("overlap-paid-pending", paid, [{"parent_index": 0}]+pending),
        ("duplicate-paid-row", paid[:1]+paid, pending),
        ("duplicate-pending-row", paid, pending[:1]+pending),
        ("unordered-paid-row", list(reversed(paid)), pending),
        ("extra-ledger-row", paid+[{"parent_index": 4}], pending),
        ("boolean-parent-index", [{"parent_index": False}, paid[1]], pending),
    ):
        try:
            list(valid_payment_partition(4, encoded(badpaid), encoded(badpending)))
        except AssertionError:
            rejected.append(label)
        else:
            raise AssertionError(("invalid ledger accepted", label))
    row = {"centers": 16, "faces": [3 | (1 << 15)]}
    digest = "finite-constant-identifier"
    payload = {"N": 25, "B": 15, "collar_centers": 16, "collar_faces": row["faces"],
               "constants_sha256": digest,
               "source_sha256": sha(ROOT / "prove_linked_general_collar.py"),
               "kernel_sha256": sha(ROOT / "linked_general_collar_kernel.py")}
    replay = {"N": 25, "B": 15, "collar_centers": 16, "collar_faces": row["faces"],
              "verified": True, "all_full_simple_disk_completions_strictly_paid": True,
              "source_sha256": sha(ROOT / "replay_refined_linked_leaves.py")}
    full_filling_source(row, payload, replay, 25, 15, digest)
    for label, source, field, value in (
        ("wrong-proof-N", "payload", "N", 24),
        ("wrong-proof-B", "payload", "B", 14),
        ("wrong-proof-centers", "payload", "collar_centers", 17),
        ("wrong-proof-faces", "payload", "collar_faces", []),
        ("wrong-constants", "payload", "constants_sha256", "wrong"),
        ("wrong-kernel", "payload", "kernel_sha256", "wrong"),
        ("wrong-replay-faces", "replay", "collar_faces", []),
        ("actual-pending-family", "replay", "all_full_simple_disk_completions_strictly_paid", False),
    ):
        alteredpayload, alteredreplay = deepcopy(payload), deepcopy(replay)
        (alteredpayload if source == "payload" else alteredreplay)[field] = value
        try:
            full_filling_source(row, alteredpayload, alteredreplay, 25, 15, digest)
        except AssertionError:
            rejected.append(label)
        else:
            raise AssertionError(("invalid conditional source accepted", label))
    output.mkdir()
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "complete-parent-finer-supplement-finite-controls-v1",
        "finite_full_index_partition_positive": True, "finite_conditional_source_positive": True,
        "negative_controls_rejected": rejected,
        "source_sha256": sha(Path(__file__)),
        "audit_source_sha256": sha(ROOT / "audit_complete_origin_finer_supplement.py"),
        "no_production_parent_lower_bound_or_family_paid_by_controls": True,
        "global_optimality_proved": False,
    })
    print("Complete-parent finer supplement controls PASS:", len(rejected), "rejections", flush=True)


if __name__ == "__main__":
    main()
