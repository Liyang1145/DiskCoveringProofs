"""Actual accepted source identity refusals and own-order mathematical positive."""
from copy import deepcopy
from pathlib import Path
import argparse
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha
from n25_outer_search import publish, read
import small_order_collar_lower_pipeline as pipeline

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", required=True, type=Path)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    stage = ROOT / "n24-B16-s1"
    record = pipeline.source_gate(stage)
    refusals = []
    def reject(name, function):
        try:
            function()
        except (AssertionError, KeyError, ValueError):
            refusals.append(name)
        else:
            raise AssertionError("bad input accepted: "+name)
    for field, value in (
        ("verified", False), ("schema", "complete-cover-origin-collar-sorted-chunks-v1"),
        ("N", 25), ("complete_recorded_necessary_outer_family", False),
        ("actual_native_successful_terminal_and_exact_source_inputs_rechecked", False),
        ("all_declared_sorted_slabs_and_full_union_independently_verified", False),
        ("weak_graph_rows_not_full_type_lower_bound_payments", False),
        ("source_sha256", "0"*64), ("catalog_sha256", "0"*64),
        ("union_report_sha256", "0"*64), ("global_optimality_proved", True),
        ("unique_necessary_weak_graphs", -1)):
        bad = deepcopy(record)
        bad[field] = value
        reject("source-"+field, lambda bad=bad: pipeline.source_record_gate(bad, stage))
    iterator = pipeline.rows(stage, record, True)
    row = next(iterator)
    iterator.close()
    for field, value in (
        ("id", 1), ("members", 2), ("centers", 24), ("faces", []),
        ("faces", row["faces"]+[row["faces"][-1]]),
        ("faces", [1 << row["centers"]]),
        ("faces", [3]), ("faces", list(reversed(row["faces"])))):
        bad = deepcopy(row)
        bad[field] = value
        reject("row-"+field+"-"+str(len(refusals)), lambda bad=bad: pipeline.row_gate(bad, 24, 16, 0))
    from probe_collar_batches import make
    import exact_graph as exact
    from fractions import Fraction as F
    constants = read(ROOT.parent / "evidence/core-reduction/constants/n24.json")
    nodes, failure = make(16, row["centers"], row["faces"], constants, 31, route_weak=True)
    assert nodes is not None, failure
    result = exact.verify(16, row["centers"], row["faces"], nodes, constants)
    assert result["verified"] and F(result["minimum_force_margin"]) > 0
    wrong = deepcopy(constants)
    wrong["radius_upper"] = "1/2"
    reject("wrong-own-order-radius", lambda: exact.verify(
        16, row["centers"], row["faces"], nodes, wrong))
    output.mkdir()
    publish(output / "VERIFIED.json", {
        "verified": True, "real_source_record_and_row_refusals_passed": True,
        "negative_controls_rejected": refusals,
        "real_own_order_positive_tree_replayed": True,
        "positive_parent_index": row["id"], "positive_exact_result": result,
        "source_acceptance_sha256": sha(stage / "ACCEPTED/SOURCE-ACCEPTED.json"),
        "source_sha256": sha(ROOT / "small_order_collar_lower_pipeline.py"),
        "control_source_sha256": sha(Path(__file__)),
        "controls_not_whole_family_lower_payments": True,
        "global_optimality_proved": False,
    })
    print("Small-order lower pipeline controls accepted:", len(refusals),
          "refusals and actual own-order strict positive", flush=True)


if __name__ == "__main__":
    main()
