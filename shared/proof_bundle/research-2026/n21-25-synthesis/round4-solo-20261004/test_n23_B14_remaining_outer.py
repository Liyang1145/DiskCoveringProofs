"""Real finite source controls for current-residual-only full outer grouping."""
from pathlib import Path
from copy import deepcopy
from io import StringIO
import argparse
import json

from group_n23_B14_remaining_outer import (
    ROOT, HIGH, BinaryRows, independent_mask, group_remaining, sha, publish, check_map)

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--catalog", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    catalogpath, output = args.catalog.resolve(), args.output.resolve()
    assert catalogpath.is_relative_to(ROOT) and output.is_relative_to(ROOT) and not output.exists()
    catalog = BinaryRows(catalogpath)
    iterator = iter(catalog.rows())
    rows = [next(iterator) for _ in range(32)]
    catalog.stream.close()
    eligible = [index for index, row in rows if independent_mask(row["faces"]) != (1 << 23)-1]
    selected = eligible[::2]
    assert len(selected) > 2 and len(selected) < len(eligible)

    def invoke(source=rows, pending=selected, expected=len(selected), total=32):
        result = StringIO()
        groups, count = group_remaining(iter(source), iter(pending), total, expected, result)
        return groups, count, [json.loads(line) for line in result.getvalue().splitlines()]

    groups, count, bindings = invoke()
    assert count == len(selected) == sum(group["members"] for group in groups)
    assert [row["index"] for row in bindings] == selected
    for binding in bindings:
        check_map(23, 14, groups[binding["group"]], binding["map"],
                  set(rows[binding["index"]][1]["faces"]), 1)
    cases = [
        ("duplicate-current-pending", {"pending": selected[:1]+selected}),
        ("reversed-current-pending", {"pending": list(reversed(selected))}),
        ("missing-current-pending", {"pending": selected[:-1]}),
        ("wrong-declared-pending-count", {"expected": len(selected)+1}),
        ("truncated-original-source", {"source": rows[:-1]}),
        ("original-source-index-gap", {"source": rows[:10]+rows[11:]}),
        ("pending-outside-original-source", {"pending": selected+[32]}),
    ]
    obstruction = next(index for index, row in rows if independent_mask(row["faces"]) == (1 << 23)-1)
    cases.append(("already-origin-excluded-type-reintroduced",
                  {"pending": sorted(selected+[obstruction]), "expected": len(selected)+1}))
    changed = deepcopy(rows)
    changed[selected[0]][1]["faces"].pop()
    cases.append(("original-complete-face-omitted", {"source": changed}))
    rejected = []
    for label, kwargs in cases:
        try:
            invoke(**kwargs)
        except (AssertionError, ValueError, IndexError, StopIteration):
            rejected.append(label)
        else:
            raise AssertionError(("invalid full outer residual selection accepted", label))
    output.mkdir()
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "N23-B14-verified-residual-full-outer-selection-controls-v1",
        "real_original_full_types_in_fixture": 32,
        "only_declared_current_residual_indices_selected_positive_control": True,
        "one_boundary_faces_preserved_and_actual_full_exposed_map_checked": True,
        "negative_controls_rejected": rejected,
        "source_sha256": sha(Path(__file__)),
        "group_source_sha256": sha(ROOT / "group_n23_B14_remaining_outer.py"),
        "frozen_mapping_checker_sha256": sha(HIGH / "audit_streamed_hierarchy.py"),
        "finite_selection_controls_not_lower_bound_proofs": True,
        "global_optimality_proved": False,
    })
    print("N23/B14 actual residual all-exposed controls passed:", len(rejected), flush=True)


if __name__ == "__main__":
    main()
