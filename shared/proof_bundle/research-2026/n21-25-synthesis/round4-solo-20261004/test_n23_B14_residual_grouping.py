"""Real finite original-row selection controls, no whole-family payment."""
from copy import deepcopy
from io import StringIO
from pathlib import Path
import argparse
import json

from group_n23_B14_origin_residual import (
    ROOT, HIGH, BinaryRows, group_selected, independent_mask, header, read, publish, sha)

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
    digest = sha(catalogpath)
    pendingrows = [{"index": index, "exposed_mask": independent_mask(row["faces"])}
                   for index, row in rows if independent_mask(row["faces"]) != (1 << 23)-1]
    assert len(pendingrows) > 2

    def invoke(source=rows, selected=pendingrows, expected=len(pendingrows),
               first=header("not-paid-by-origin-condition", digest), total=32):
        pending = StringIO(json.dumps(first)+"\n"+"".join(json.dumps(row)+"\n" for row in selected))
        destination = StringIO()
        groups, count = group_selected(iter(source), pending, digest, total, expected, destination)
        return groups, count, [json.loads(line) for line in destination.getvalue().splitlines()]

    groups, count, bindings = invoke()
    assert count == len(pendingrows) == sum(group["members"] for group in groups)
    assert [row["index"] for row in bindings] == [row["index"] for row in pendingrows]
    cases = [
        ("missing-real-residual", {"selected": pendingrows[:-1]}),
        ("duplicate-real-residual", {"selected": pendingrows[:1]+pendingrows}),
        ("reversed-selection", {"selected": list(reversed(pendingrows))}),
        ("wrong-count", {"expected": count+1}),
        ("truncated-original-source", {"source": rows[:-1]}),
        ("source-index-gap", {"source": rows[:10]+rows[11:]}),
        ("wrong-parent-header", {"first": header("actual-cover-origin-obstruction", digest)}),
    ]
    changed = deepcopy(pendingrows)
    changed[0]["exposed_mask"] ^= 1 << 22
    cases.append(("wrong-actual-exposed-label-mask", {"selected": changed}))
    obstruction = next(index for index, row in rows if independent_mask(row["faces"]) == (1 << 23)-1)
    changed = sorted(pendingrows+[{"index": obstruction, "exposed_mask": (1 << 23)-1}],
                     key=lambda row: row["index"])
    cases.append(("reintroducing-already-origin-excluded-type", {"selected": changed}))
    changedsource = deepcopy(rows)
    changedsource[pendingrows[0]["index"]][1]["faces"].pop()
    cases.append(("omitted-original-full-face", {"source": changedsource}))
    rejected = []
    for label, kwargs in cases:
        try:
            invoke(**kwargs)
        except (AssertionError, ValueError, IndexError, StopIteration):
            rejected.append(label)
        else:
            raise AssertionError(("bad original residual selection accepted", label))
    output.mkdir()
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "N23-B14-original-origin-residual-group-selection-controls-v1",
        "real_original_full_types_in_finite_fixture": 32,
        "actual_finite_residual_members": count, "negative_controls_rejected": rejected,
        "catalog_sha256": digest, "source_sha256": sha(Path(__file__)),
        "group_source_sha256": sha(ROOT / "group_n23_B14_origin_residual.py"),
        "finite_selection_controls_not_new_lower_bounds": True,
        "global_optimality_proved": False,
    })
    print("N23/B14 actual residual grouping controls passed:", len(rejected), flush=True)


if __name__ == "__main__":
    main()
