"""Finite source-selection corruption controls, not geometric proof payments."""
from copy import deepcopy
from io import StringIO
from pathlib import Path
import argparse
import json

from extract_n23_actual_residual_types import extract, ROOT, HIGH
from stream_catalog import sha
from n25_outer_search import publish

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    # Functional masks are intentionally not claimed to be planar disk types.
    N, B = 7, 3
    faces = sorted([11, 13, 19, 22, 35, 37, 70, 88, 104])
    exposed = [mask for mask in faces if mask & 7]
    mapping = {"centers": list(range(7)), "anchors": list(range(3)),
               "orientation": 1, "shift": 0}
    groups = [{"id": 0, "centers": 7, "faces": exposed, "members": 1},
              {"id": 1, "centers": 7, "faces": exposed, "members": 2}]
    rows = [(index, {"faces": faces, "stabilizer": 1}) for index in range(4)]
    binds = [{"index": index, "group": int(index != 1), "map": mapping}
             for index in (1, 2, 3)]

    def invoke(source=rows, bindings=binds, pair=(1, 2, 3), pending=(1, 3),
               graphgroups=groups, expected=2, total=4):
        stream = StringIO("".join(json.dumps(row)+"\n" for row in bindings))
        result = StringIO()
        counts = extract(iter(source), stream, iter(pair), iter(pending), graphgroups,
                         total, expected, result, N=N, B=B)
        return counts, [json.loads(line) for line in result.getvalue().splitlines()]

    counts, actual = invoke()
    assert counts == (3, 2, {0: 1, 1: 1})
    assert [row["index"] for row in actual] == [1, 3]
    assert all(row["faces"] == faces and row["pure_internal_faces"] == [88, 104]
               for row in actual)
    cases = [
        ("missing-original-binding", {"bindings": binds[:-1]}),
        ("duplicate-original-binding", {"bindings": binds[:1]+binds}),
        ("extra-original-binding", {"bindings": binds+[deepcopy(binds[-1])]}),
        ("residual-outside-outer-parent", {"pending": (0, 3)}),
        ("residual-count-mismatch", {"expected": 3}),
        ("residual-index-duplicate", {"pending": (1, 1, 3)}),
        ("residual-index-reversed", {"pending": (3, 1)}),
        ("source-truncation", {"source": rows[:-1]}),
        ("source-index-gap", {"source": rows[:2]+[(3, rows[2][1])]}),
        ("pair-index-mismatch", {"pair": (0, 2, 3)}),
    ]
    for label, field, value in (
        ("center-collision", "centers", [0, 1, 2, 3, 4, 5, 5]),
        ("wrong-anchor", "anchors", [1, 1, 2]),
        ("wrong-reflection-edge-anchor", "orientation", -1),
        ("wrong-boundary-shift", "shift", 1),
    ):
        changed = deepcopy(binds)
        changed[0]["map"][field] = value
        cases.append((label, {"bindings": changed}))
    for label, change in (
        ("omitted-pure-internal-face", faces[:-1]),
        ("duplicate-full-face", faces[:-1]+[faces[-2]]),
        ("wrong-exposed-face", sorted([mask if mask != 11 else 7 for mask in faces])),
        ("out-of-range-center-mask", faces[:-1]+[137]),
    ):
        changed = deepcopy(rows)
        changed[1][1]["faces"] = change
        cases.append((label, {"source": changed}))
    changedgroups = deepcopy(groups)
    changedgroups[1]["members"] += 1
    cases.append(("wrong-original-group-member-count", {"graphgroups": changedgroups}))
    rejected = []
    for label, kwargs in cases:
        try:
            invoke(**kwargs)
        except (AssertionError, ValueError, IndexError):
            rejected.append(label)
        else:
            raise AssertionError(("invalid full-type extraction accepted", label))
    output.mkdir()
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "N23-actual-full-residual-extraction-controls-v1",
        "negative_controls_rejected": rejected,
        "pure_internal_faces_preserved_positive_control": True,
        "old_paid_source_rows_not_selected": True,
        "source_sha256": sha(Path(__file__)),
        "extractor_source_sha256": sha(ROOT / "extract_n23_actual_residual_types.py"),
        "frozen_mapping_checker_sha256": sha(HIGH / "audit_streamed_hierarchy.py"),
        "functional_masks_not_asserted_planar_or_geometric": True,
        "global_optimality_proved": False,
    })
    print("N23 actual complete residual extraction controls passed:", len(rejected), flush=True)


if __name__ == "__main__":
    main()
