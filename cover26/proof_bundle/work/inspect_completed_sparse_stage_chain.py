"""Read-only association and per-family conservation, not a new acceptance."""

import argparse
from collections import Counter
import json
from pathlib import Path

import audit_conditional_stage_acceptance_contract as contract
import verify_conditional_force_stage as binding


def main():
    parser = argparse.ArgumentParser()
    for name in ("stage", "stage-replay", "catalog", "catalog-replay",
                 "contract-regression", "source-stage"):
        parser.add_argument("--"+name, type=Path, required=True)
    args = parser.parse_args()
    stage, manifest = binding.read(args.stage / "VERIFIED.json"), binding.read(args.stage / "MANIFEST.json")
    checker = contract.gate(stage, manifest)
    if (binding.sha(args.stage / checker) != stage["executed_checker_sha256"]
            or binding.read(args.stage_replay) != stage
            or binding.sha(args.stage_replay) != binding.sha(args.stage / "VERIFIED.json")
            or stage["source_acceptance_sha256"] != binding.sha(args.source_stage / "VERIFIED.json")):
        raise ValueError("actual completed sparse stage source/executor/publication association failed")
    catalog, replay = binding.read(args.catalog / "VERIFIED.json"), binding.read(args.catalog_replay)
    if (catalog != replay or catalog["verified"] is not True
            or catalog["source_stage_acceptance_sha256"] != binding.sha(args.stage / "VERIFIED.json")
            or catalog["executed_checker_sha256"] != binding.sha(args.catalog / "verify_terminal_catalog.py")
            or len(catalog["negative_controls_rejected"]) != 5):
        raise ValueError("actual original catalogue source/executor/publication association failed")
    regression = binding.read(args.contract_regression)
    if (regression["executed_diagnostic_sha256"] != binding.sha(contract.__file__)
            or regression["known_good_acceptance_sha256"] != binding.sha(args.stage / "VERIFIED.json")
            or regression["known_good_metadata_contract_passed"] is not True
            or regression["suspect_contract_rejected"] is not True
            or len(regression["guard_rejection_controls_passed"]) != 6):
        raise ValueError("actual completed sparse-stage contract controls changed")
    trace = binding.read(args.stage / "TRACE.json")
    incoming = binding.read(args.source_stage / "FRONTIER.json")
    frontier = binding.read(args.stage / "FRONTIER.json")
    events = trace["events"]
    if Counter(event["kind"] for event in events) != Counter(stage["event_counts"]):
        raise ValueError("completed stage actual trace/event counts differ")
    rows = []
    for b in (14, 15, 16, 17):
        source = sum(row["B"] == b for row in incoming["pending_states"])
        selected = [event for event in events if event["B"] == b]
        counts = Counter(event["kind"] for event in selected)
        children = sum(event["all_child_count"] for event in selected if event["kind"] == "split")
        strict = sum(counts[kind] for kind in ("force", "force_tree", "area"))
        final = sum(row["B"] == b for row in frontier["pending_states"])
        if source+children-counts["split"]-strict-counts["empty"] != final:
            raise ValueError("actual completed stage lost a family or immediate sibling")
        rows.append({"B": b, "source": source, "children": children, "split": counts["split"],
                     "strict": strict, "empty": counts["empty"], "frontier": final})
    if (len(events) != stage["native_events_independently_replayed"]
            or len(frontier["pending_states"]) != stage["conditional_frontier_pending_subtrees"]):
        raise ValueError("actual completed standalone stage count association failed")
    print(json.dumps({
        "read_only_actual_chain_association_passed": True,
        "not_a_complete_current_or_new_geometry_acceptance": True,
        "stage_acceptance_and_actual_publication_sha256": binding.sha(args.stage / "VERIFIED.json"),
        "catalogue_acceptance_sha256": binding.sha(args.catalog / "VERIFIED.json"),
        "actual_catalogue_publication_sha256": binding.sha(args.catalog_replay),
        "executor_contract_regression_sha256": binding.sha(args.contract_regression),
        "actual_per_family_conservation": rows,
        "new_strict_exclusions": sum(row["strict"] for row in rows),
        "actual_standalone_frontier": len(frontier["pending_states"]),
        "selected_candidate_type_paths": catalog["selected_candidate_type_paths"],
        "distinct_selected_canonical_types": catalog["distinct_selected_canonical_types"],
        "global_lower_bound_proved": False, "global_optimality_proved": False,
    }, indent=2), flush=True)


if __name__ == "__main__":
    main()
