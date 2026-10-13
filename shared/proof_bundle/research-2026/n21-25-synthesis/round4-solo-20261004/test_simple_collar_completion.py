"""Compare all handled collar fibers against frozen complete small catalogs."""
from pathlib import Path
from collections import defaultdict
from copy import deepcopy
import argparse
import json
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from paid_binary_residual import BinaryRows, verify_merge
from group_catalog import canonical, validate
from stream_catalog import sha
from complete_simple_collar import simple_holes, enumerate_completions

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    base = ROOT / "outer-collar-controls-v3-deep-internal"
    controls = json.loads((base / "VERIFIED.json").read_text())
    assert controls["verified"] and controls["all_full_reference_outer_restrictions_present"]
    cases, positive = [], None
    for N, B in ((3, 3), (5, 3), (6, 4), (7, 4), (8, 5), (9, 6), (10, 3), (10, 4)):
        reference = base / f"N{N}-B{B}-full-reference.bin"
        header, _ = verify_merge(reference)
        fibers, sizes = defaultdict(set), {}
        for index, row in BinaryRows(reference).rows():
            full = tuple(row["faces"])
            code, mapping = canonical(N, B, full, 1)
            fibers[code].add(full)
            sizes[code] = len(mapping["centers"])
        handled = unhandled = compared = max_new = max_holes = total_calls = 0
        for code, expected in fibers.items():
            centers = sizes[code]
            try:
                holes = simple_holes(centers, B, list(code))
            except AssertionError:
                unhandled += 1
                continue
            actual, maps, calls = enumerate_completions(N, B, centers, list(code), holes, 0)
            assert set(actual) == expected, ("completion fiber omitted or added a full graph", N, B, code)
            for full, mapping in maps.items():
                validate(N, B, code, mapping, full)
            handled += 1
            compared += len(expected)
            total_calls += calls
            max_new, max_holes = max(max_new, N-centers), max(max_holes, len(holes))
            if holes:
                positive = (N, B, centers, list(code), holes)
        cases.append({
            "N": N, "B": B, "reference_complete_graphs": header["orbits"],
            "distinct_outer_collars": len(fibers), "handled_simple_hole_collars": handled,
            "unhandled_collars_not_excluded": unhandled,
            "full_graphs_in_exactly_compared_fibers": compared,
            "all_handled_complete_fibers_equal": True,
            "largest_missing_inner_budget": max_new, "largest_hole_count": max_holes,
            "completion_calls": total_calls, "reference_sha256": sha(reference),
        })
        print("Complete collar fiber comparison PASS:", N, B, handled, "handled collars;",
              compared, "full graphs;", unhandled, "unhandled", flush=True)
    assert positive is not None and any(row["largest_missing_inner_budget"] > 0 for row in cases)
    N, B, centers, code, holes = positive
    rejected = []
    try:
        enumerate_completions(N, B, centers, code, holes, 1)
    except AssertionError:
        rejected.append("finite-node-budget")
    else:
        raise AssertionError("node-limited completion accepted")
    for label, faces in (("duplicate-face", sorted(code+[code[0]])),
                         ("missing-boundary-star", code[1:])):
        try:
            simple_holes(centers, B, faces)
        except AssertionError:
            rejected.append(label)
        else:
            raise AssertionError(("malformed collar accepted", label))
    args.output.write_text(json.dumps({
        "verified": True, "schema": "simple-collar-completion-controls-v1",
        "source_sha256": sha(Path(__file__)),
        "completion_source_sha256": sha(ROOT / "complete_simple_collar.py"),
        "source_controls_sha256": sha(base / "VERIFIED.json"),
        "cases": cases, "all_handled_fibers_exactly_equal_to_full_reference": True,
        "negative_controls_rejected": rejected,
        "pinched_or_nonmanifold_collars_never_claimed_excluded": True,
        "global_optimality_proved": False,
    }, indent=2)+"\n", encoding="utf8")


if __name__ == "__main__":
    main()
