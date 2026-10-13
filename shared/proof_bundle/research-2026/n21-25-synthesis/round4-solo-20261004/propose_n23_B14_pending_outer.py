"""Strict force proposals only for whole groups still unpaid by the first outer stage."""
from pathlib import Path
from collections import Counter
from fractions import Fraction as F
import argparse
import gzip
import sys
import json
import time

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha
from n25_outer_search import read, publish
from probe_collar_batches import make
import exact_graph as exact

assert __debug__


def select_pending(data, receipt):
    assert (data["N"], data["B"], data["threshold"]) == (23, 14, 1)
    assert (receipt["N"], receipt["B"]) == (23, 14)
    assert receipt["requested_groups_complete"]
    groups, outcomes = data["groups"], receipt["outcomes"]
    assert [g["id"] for g in groups] == list(range(data["group_count"]))
    assert [r["group"] for r in outcomes] == list(range(data["group_count"]))
    assert all(r["status"] in ("excluded", "pending") for r in outcomes)
    paid = {r["group"] for r in outcomes if r["status"] == "excluded"}
    selected = [g for g, r in zip(groups, outcomes, strict=True) if r["status"] == "pending"]
    assert len(paid) == receipt["excluded_groups"]
    assert len(selected) == receipt["pending_groups"]
    assert sum(groups[g]["members"] for g in paid) == receipt["catalog_members_excluded"]
    assert sum(g["members"] for g in groups) == data["selected_types"]
    return selected, paid


def main():
    ap = argparse.ArgumentParser()
    for name in ("parent", "groups", "previous-stage", "output"):
        ap.add_argument("--"+name, type=Path, required=True)
    ap.add_argument("--limit", type=int, default=511)
    args = ap.parse_args()
    parent, groupspath, previous, output = (
        getattr(args, name.replace("-", "_")).resolve()
        for name in ("parent", "groups", "previous-stage", "output"))
    assert all(path.is_relative_to(ROOT) for path in (parent, groupspath, previous, output))
    assert not output.exists() and 31 < args.limit <= 10001
    accepted, data, old = map(read, (parent / "VERIFIED.json", groupspath, previous / "SUMMARY.json"))
    assert accepted["verified"]
    assert accepted["schema"] == "N23-B14-current-residual-full-outer-disjoint-payment-v1"
    assert accepted["source_sha256"] == sha(ROOT / "audit_n23_B14_full_outer_payment.py")
    assert accepted["all_source_rows_previous_payment_partition_and_current_full_outer_maps_checked"]
    assert accepted["all_new_positive_full_outer_trees_freshly_exact_replayed_again"]
    assert accepted["previous_paid_types_not_reintroduced_or_recounted_as_new"]
    assert accepted["positive_groups"] == old["excluded_groups"]
    assert accepted["frozen_files"][str(groupspath)] == sha(groupspath)
    assert accepted["frozen_files"][str(previous / "SUMMARY.json")] == sha(previous / "SUMMARY.json")
    assert old["groups_sha256"] == sha(groupspath)
    assert old["source_sha256"] == sha(ROOT / "propose_isolated_small_order_groups.py")
    assert old["known_attaining_group_control"] is None
    selected, _ = select_pending(data, old)
    assert sum(g["members"] for g in selected) == accepted["pending_full_types"] > 0
    frozen = dict(accepted["frozen_files"])
    for path in (Path(__file__), parent / "VERIFIED.json", parent / "PENDING.jsonl",
                 groupspath, previous / "SUMMARY.json", ROOT / "probe_collar_batches.py",
                 HIGH / "candidate_domain.py", HIGH / "exact_graph.py"):
        frozen[str(path)] = sha(path)
    assert sha(parent / "PENDING.jsonl") == accepted["pending_sha256"]
    for path, digest in frozen.items():
        assert sha(path) == digest
    constantspath = ROOT.parent / "evidence/core-reduction/constants/n23.json"
    constants, constantshash = read(constantspath), sha(constantspath)
    assert constants["verified"] and constants["N"] == 23
    assert F(constants["radius_upper"]) == F(249953776586051, 10**15)
    digest = sha(groupspath)
    output.mkdir()
    publish(output / "INPUT-BINDINGS.json", {
        "N": 23, "B": 14, "selected_unpaid_group_ids": [g["id"] for g in selected],
        "parent_report_sha256": sha(parent / "VERIFIED.json"),
        "previous_stage_receipt_sha256": sha(previous / "SUMMARY.json"),
        "groups_sha256": digest, "force_limit": args.limit, "frozen_files": frozen,
        "no_previous_paid_group_reproposed": True,
        "source_sha256": sha(Path(__file__)), "global_optimality_proved": False,
    })
    outcomes, counts, associated, started = [], Counter(), 0, time.monotonic()
    for group in selected:
        gid = group["id"]
        nodes, failure = make(14, group["centers"], group["faces"], constants,
                              args.limit, route_weak=True)
        if nodes is None:
            outcome = {"group": gid, "status": "pending", **failure}
        else:
            result = exact.verify(14, group["centers"], group["faces"], nodes, constants)
            assert result["verified"] and F(result["minimum_force_margin"]) > 0
            path = output / f"group-{gid:07}.json.gz"
            with gzip.open(path, "xt", encoding="utf8") as stream:
                json.dump({
                    "N": 23, "B": 14, "partial_centers": group["centers"],
                    "faces": group["faces"], "nodes": nodes, "groups_sha256": digest,
                    "constants_sha256": constantshash, "radius_upper": constants["radius_upper"],
                }, stream, separators=(",", ":"))
            outcome = {"group": gid, "status": "excluded", "members": group["members"],
                       "tree_sha256": sha(path), **result}
            associated += group["members"]
        outcomes.append(outcome)
        counts[outcome["status"]] += 1
        print("N23/B14 actual unpaid whole-group followup", gid, len(outcomes), "/", len(selected),
              dict(counts), "seconds", round(time.monotonic()-started, 1), flush=True)
    for path, value in frozen.items():
        assert sha(path) == value
    publish(output / "SUMMARY.json", {
        "N": 23, "B": 14, "groups_sha256": digest, "outcomes": outcomes,
        "selected_unpaid_group_ids": [g["id"] for g in selected],
        "requested_unpaid_groups_complete": True, "excluded_groups": counts["excluded"],
        "pending_groups": counts["pending"], "catalog_members_excluded": associated,
        "parent_report_sha256": sha(parent / "VERIFIED.json"),
        "previous_stage_receipt_sha256": sha(previous / "SUMMARY.json"),
        "frozen_files": frozen, "source_sha256": sha(Path(__file__)),
        "fresh_independent_math_actual_source_maps_and_payment_adoption_still_required": True,
        "global_optimality_proved": False,
    })


if __name__ == "__main__":
    main()
