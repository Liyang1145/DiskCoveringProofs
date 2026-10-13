"""Small disjoint-index union controls; no production mathematics."""
from io import StringIO
from pathlib import Path
import argparse
import json
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / "round3-high"))
from stream_catalog import sha
from n25_outer_search import publish
from merge_n23_B15_origin_pair import indices, merge_indices

assert __debug__


def stream(values):
    return StringIO("".join(json.dumps({"index": value})+"\n" for value in values))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    target = StringIO()
    result = merge_indices(indices(stream([0, 2, 4]), 5), indices(stream([0, 1, 4]), 5), 5, 3, 3, target)
    assert result == {"pending": 2, "actual-cover-origin-obstruction": 2,
                      "additional-strict-pair-force": 1, "overlap_not_counted_twice": 1}
    assert [json.loads(line)["index"] for line in target.getvalue().splitlines()] == [0, 4]
    rejected = []
    for label, left, right in (
        ("duplicate-origin-index", [0, 0, 4], [0, 1, 4]),
        ("out-of-order-origin-index", [2, 0, 4], [0, 1, 4]),
        ("duplicate-pair-index", [0, 2, 4], [0, 1, 1]),
        ("out-of-range-index", [0, 2, 5], [0, 1, 4]),
        ("negative-index", [-1, 2, 4], [0, 1, 4]),
        ("boolean-index", [False, 2, 4], [0, 1, 4]),
        ("missing-origin-index", [0, 4], [0, 1, 4]),
        ("extra-pair-index", [0, 2, 4], [0, 1, 2, 4]),
    ):
        try:
            merge_indices(indices(stream(left), 5), indices(stream(right), 5), 5, 3, 3, StringIO())
        except AssertionError:
            rejected.append(label)
        else:
            raise AssertionError(("invalid partition accepted", label))
    output.mkdir()
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "N23-origin-pair-disjoint-index-union-finite-controls-v1",
        "positive_overlap_deducted_once": True, "negative_controls_rejected": rejected,
        "source_sha256": sha(Path(__file__)), "merge_source_sha256": sha(ROOT / "merge_n23_B15_origin_pair.py"),
        "not_a_production_catalog_scan_or_payment": True, "global_optimality_proved": False,
    })
    print("N23 origin/pair disjoint-index controls PASS:", len(rejected), "rejections", flush=True)


if __name__ == "__main__":
    main()
