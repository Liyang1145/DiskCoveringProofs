"""Whole actual-current source scan for six-target filled-ear mathematics."""

from collections import Counter
import json
from pathlib import Path

import n26_six_target_filled_ears as rule
import verify_conditional_force_stage as binding


def main():
    output = Path("outputs/n26-current28-six-target-filled-ear-mathematical-scan-v1.json")
    if output.exists():
        raise FileExistsError(output)
    folder = Path("outputs/n26-current28-closed-ear-source-geometry-v1")
    source_path = folder/"SOURCE-FRONTIER.json"
    old_general_path = Path("outputs/n26-current28-general-filled-boundary-ear-mathematical-scan-v1.json")
    source = binding.read(source_path)
    rule.family_gate(binding.read(folder/"FAMILY-CONSTANTS.json"))
    old_general = binding.read(old_general_path)
    old_indexes = set(row["actual_source_index"] for row in old_general["results"])
    paths = [source_path, folder/"MANIFEST.json", folder/"FAMILY-CONSTANTS.json",
             folder/"FAMILY-ACCEPTANCE.json", old_general_path, Path(__file__), Path(rule.__file__),
             Path("work/n26-six-core-target-filled-ear-proof.md"),
             Path("work/n26-closed-ear-core-capacity-proof.md"),
             Path("work/n26-embedded-dual-and-corner-starring-bridge-proof.md")]
    digests = {str(path): binding.sha(path) for path in paths}
    targets = rule.target_gate()
    results, cases = [], 0
    for index, row in enumerate(source["pending_states"]):
        found = rule.patches(row)
        if found:
            if row["terminal"]:
                raise AssertionError("a real complete candidate/competitor was marked impossible")
            # Any one sufficiently filled patch excludes the ENTIRE prefix.
            # Retain every recognition result, but count each prefix only once.
            selected = max(found, key=lambda patch: len(patch["actual_enclosed_nonowner_labels"]))
            distributions = rule.shadow_case_distributions(row, selected)
            count = sum(item["all_shadow_label_placements_checked"] for item in distributions)
            cases += count
            results.append({
                "actual_source_index": index, "B": row["B"], "prefix": row["prefix"],
                "actual_source_state": row, "all_qualifying_filled_patches": found,
                "selected_strongest_filled_patch": selected,
                "original_count_and_all_shadow_case_distributions": distributions,
                "original_count_and_shadow_cases_checked": count,
                "already_in_weaker4474_four_target_general_ear_scan": index in old_indexes,
            })
        if (index+1) % 1000 == 0:
            print(json.dumps({"six_target_actual_source_states_scanned": index+1,
                              "qualifying_whole_prefixes": len(results),
                              "formal_geometric_payments": 0}), flush=True)
    indexes = {row["actual_source_index"] for row in results}
    if not old_indexes <= indexes:
        raise AssertionError("six-target scan lost a weaker four-target obstruction")
    if any(binding.sha(path) != digest for path, digest in digests.items()):
        raise ValueError("six-target source or written mathematics changed")
    report = {
        "schema": "N26-current28-six-target-filled-boundary-ear-mathematical-scan-v1",
        "verified": False, "input_sha256": digests, "exact_six_core_target_identity_result": targets,
        "results": results, "entire_actual_current28_source_states_scanned": len(source["pending_states"]),
        "actual_qualifying_whole_prefixes": len(results),
        "weaker_four_target_general_ear_prefixes_retained": len(old_indexes),
        "additional_six_target_whole_prefixes_NOT_accepted": len(indexes-old_indexes),
        "qualifying_family_counts": dict(Counter(str(row["B"]) for row in results)),
        "all_original_count_and_shadow_label_cases_checked": cases,
        "prospective_frontier_NOT_current": len(source["pending_states"])-len(results),
        "complete_original_prefix_independent_replay_AND_geometry_admission_STILL_required": True,
        "current_formal_frontier_STILL": 11183, "candidate_whole_roots_STILL": 25,
        "new_formal_geometric_payments": 0, "global_lower_bound_proved": False,
        "global_optimality_proved": False, "n27_started": False,
    }
    with output.open("x", encoding="utf-8", newline="\n") as target:
        target.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({
        "six_core_target_filled_ear_mathematical_scan_completed": True,
        "qualifying_whole_prefixes": len(results), "additional_over_four_target_rule": len(indexes-old_indexes),
        "all_original_count_and_shadow_cases": cases,
        "prospective_frontier_NOT_current": len(source["pending_states"])-len(results),
        "formal_geometric_payments": 0, "candidate_whole_roots_removed": 0,
    }), flush=True)


if __name__ == "__main__":
    main()
