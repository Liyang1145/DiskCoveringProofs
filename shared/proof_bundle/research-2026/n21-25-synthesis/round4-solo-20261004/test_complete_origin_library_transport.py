"""Finite parent partition/source-corruption controls; no theorem payment."""
from pathlib import Path
from io import StringIO
from copy import deepcopy
import argparse
import json
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / "round3-high"))
from stream_catalog import sha
from n25_outer_search import publish
from audit_complete_origin_library_transport import valid_payment_partition, pending_source

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    paid, pending = [{"parent_index": 0}, {"parent_index": 2}], [{"parent_index": 1}]

    def invoke(pays=paid, unresolved=pending, total=3):
        def stream(rows):
            return StringIO("".join(json.dumps(row)+"\n" for row in rows))
        return list(valid_payment_partition(total, stream(pays), stream(unresolved)))

    assert [index for index, _, _ in invoke()] == [0, 1, 2]
    rejected = []
    cases = (
        ("missing-paid-row", {"pays": paid[:-1]}),
        ("missing-pending-row", {"unresolved": []}),
        ("duplicate-paid-row", {"pays": paid[:1]+paid}),
        ("duplicate-pending-row", {"unresolved": pending+pending}),
        ("overlap-paid-pending-row", {"unresolved": [{"parent_index": 0}]+pending}),
        ("out-of-order-paid-row", {"pays": list(reversed(paid))}),
        ("out-of-range-tail", {"unresolved": pending+[{"parent_index": 3}]}),
        ("bool-instead-of-integer-index", {"pays": [{"parent_index": False}, paid[1]]}),
    )
    for label, kwargs in cases:
        try:
            invoke(**kwargs)
        except (AssertionError, ValueError, TypeError, IndexError):
            rejected.append(label)
        else:
            raise AssertionError(("bad parent partition accepted", label))
    row = {"id": 1, "centers": 18, "faces": [65539, 131084]}
    unresolved = {"parent_index": 1, "centers": 18, "faces": row["faces"],
                  "batch": 0, "group": 1, "not_a_geometric_exclusion": True}
    original = {"parent_index": 1, "centers": 18, "faces": row["faces"],
                "source_batch": 0, "source_local_group": 1}
    pending_source(row, unresolved, original)
    for label, field, value in (
        ("wrong-parent-index", "parent_index", 2),
        ("bool-parent-index", "parent_index", True),
        ("wrong-source-center-count", "centers", 19),
        ("changed-source-face", "faces", [65539]),
        ("wrong-original-batch", "batch", 1),
        ("wrong-original-local-group", "group", 2),
        ("pending-claimed-as-geometric-exclusion", "not_a_geometric_exclusion", False),
    ):
        changed = deepcopy(unresolved)
        changed[field] = value
        try:
            pending_source(row, changed, original)
        except AssertionError:
            rejected.append(label)
        else:
            raise AssertionError(("bad pending source accepted", label))
    output.mkdir()
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "complete-origin-library-parent-merge-controls-v1",
        "negative_controls_rejected": rejected,
        "source_sha256": sha(Path(__file__)),
        "audit_source_sha256": sha(ROOT / "audit_complete_origin_library_transport.py"),
        "conditional_exact_outer_transport_controls_required_separately": True,
        "functional_partition_fixtures_not_planar_types_or_payments": True,
        "global_optimality_proved": False,
    })
    print("Complete-parent library merge controls PASS:", len(rejected), "rejections", flush=True)


if __name__ == "__main__":
    main()
