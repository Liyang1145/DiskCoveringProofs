"""Finite full-source selection/map corruptions; not planar-family payments."""
from copy import deepcopy
from io import StringIO
from pathlib import Path
import argparse
import json
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / "round3-high"))
from stream_catalog import sha
from n25_outer_search import publish
from audit_n23_B15_effective_outer_payment import scan

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    faces = sorted([3 | (1 << 15), 12 | (1 << 16)])
    full = sorted(faces+[(1 << 17) | (1 << 18) | (1 << 19)])
    rows = [(index, {"stabilizer": 1, "faces": full}) for index in range(4)]
    mapping = {"centers": list(range(17)), "anchors": list(range(15)), "orientation": 1, "shift": 0}
    groups = [{"id": 0, "centers": 17, "faces": faces, "members": 1},
              {"id": 1, "centers": 17, "faces": faces, "members": 2}]
    bindings = [{"index": 1, "group": 0, "map": mapping},
                {"index": 2, "group": 1, "map": mapping},
                {"index": 3, "group": 1, "map": mapping}]

    def invoke(binds=bindings, source=rows, pair=(1, 2, 3), old=(1, 3), graphgroups=groups,
               total=4, expected=2):
        ledger, residual = StringIO(), StringIO()
        text = "".join(json.dumps(row, separators=(",", ":"))+"\n" for row in binds)
        result = scan(iter(source), StringIO(text), iter(pair), iter(old), graphgroups,
                      {0: "finite-tree-identifier-not-a-proof"}, total, expected, ledger, residual)
        return result, ledger.getvalue(), residual.getvalue()

    (counts, binding_count), payments, pending = invoke()
    assert binding_count == 3
    assert counts == {"unpaid_actual_face_center_anchor_maps_checked": 2,
                      "additional_strict_outer_types": 1, "pending": 1}
    assert json.loads(payments)["index"] == 1 and json.loads(pending)["index"] == 3
    rejected = []
    cases = []
    cases.append(("missing-original-binding", {"binds": bindings[:-1]}))
    cases.append(("duplicate-original-binding", {"binds": bindings[:1]+bindings}))
    cases.append(("extra-original-binding", {"binds": bindings+[deepcopy(bindings[-1])]}))
    cases.append(("wrong-selected-source-index", {"pair": (0, 2, 3)}))
    cases.append(("unpaid-source-not-outer-selected", {"old": (0, 3)}))
    cases.append(("declared-unpaid-count-wrong", {"expected": 3}))
    cases.append(("source-count-truncated", {"source": rows[:-1]}))
    cases.append(("source-index-gap", {"source": rows[:2]+[(3, rows[2][1]), (4, rows[3][1])]}))
    for label, field, value in (
        ("center-map-collision", "centers", list(range(16))+[15]),
        ("wrong-anchor-map", "anchors", [1]+list(range(1, 15))),
        ("wrong-reflection-anchor-shift", "orientation", -1),
        ("wrong-root-shift", "shift", 1),
    ):
        changed = deepcopy(bindings)
        changed[0]["map"][field] = value
        cases.append((label, {"binds": changed}))
    changedgroups = deepcopy(groups)
    changedgroups[0]["faces"] = faces[:-1]
    cases.append(("omitted-original-outer-face", {"graphgroups": changedgroups}))
    changedgroups = deepcopy(groups)
    changedgroups[1]["members"] += 1
    cases.append(("wrong-group-members", {"graphgroups": changedgroups}))
    for label, kwargs in cases:
        try:
            invoke(**kwargs)
        except (AssertionError, ValueError, IndexError):
            rejected.append(label)
        else:
            raise AssertionError(("invalid effective source map accepted", label))
    output.mkdir()
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "N23-effective-outer-full-source-payment-finite-controls-v1",
        "all_original_indices_scanned_unpaid_maps_checked_and_no_old_paid_recount": True,
        "pure_internal_face_omitted_from_exposed_image": True,
        "negative_controls_rejected": rejected,
        "source_sha256": sha(Path(__file__)),
        "audit_source_sha256": sha(ROOT / "audit_n23_B15_effective_outer_payment.py"),
        "frozen_mapping_checker_sha256": sha(ROOT.parent / "round3-high/audit_streamed_hierarchy.py"),
        "functional_fixtures_not_planar_types_or_mathematical_payment": True,
        "global_optimality_proved": False,
    })
    print("Effective N23 outer full-source payment controls PASS:", len(rejected), "rejections", flush=True)


if __name__ == "__main__":
    main()
