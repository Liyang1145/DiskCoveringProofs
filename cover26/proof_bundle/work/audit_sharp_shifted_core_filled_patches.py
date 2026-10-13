"""Full SIX-frontier scan; sharp arcs retain all first-shifted obligations."""

from collections import Counter
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_sharp_shifted_core_filled_patches as rule
import verify_conditional_force_stage as binding


def main():
    output = Path("outputs/n26-SIX-frontier-sharp-shifted-core-mathematical-scan-v1.json")
    if output.exists():
        raise FileExistsError(output)
    first_path = Path("outputs/n26-SIX-frontier-shifted-core-mathematical-scan-v1.json")
    first = binding.read(first_path)
    for path, digest in first["input_sha256"].items():
        if binding.sha(path) != digest:
            raise ValueError("first shifted scan evidence changed")
    source_path = Path("outputs/n26-current28-six-target-source-geometry-v1/FRONTIER.json")
    source = binding.read(source_path)
    first_keys = {(row["B"], tuple(row["prefix"])) for row in first["results"]}
    old_keys = {key for key, row in (
        ((item["B"], tuple(item["prefix"])), item) for item in first["results"])
        if row["already_in_queued_old_midarc_rule"]}
    if len(source["pending_states"]) != 5637 or len(first_keys) != 751 or len(old_keys) != 680:
        raise ValueError("sharp shifted scan changed actual source/first-mathematics identity")
    digests = {**first["input_sha256"], **{
        linux(path): binding.sha(path) for path in (
            first_path, Path(__file__), Path(rule.__file__),
            Path("work/n26-sharp-shifted-core-filled-patch-proof.md"))}}
    targets = {str(k): rule.target_gate(k) for k in rule.REQUIRED}
    results, modes = [], Counter()
    for index, row in enumerate(source["pending_states"]):
        key = row["B"], tuple(row["prefix"])
        left, right = rule.patches(row), rule.patches(row, independent_locator=True)
        if left != right:
            raise ValueError("distinct sharp shifted locators/topology gates disagree")
        if left:
            if row["terminal"]:
                raise ValueError("raw complete terminal unexpectedly excluded; retain and investigate")
            selected = max(left, key=lambda item: (
                item["required_DISTINCT_ORIGINAL_outside_nonowners"]
                - item["maximum_all_original_nonowner_slots_outside"],
                -item["outer_cycle_length"]))
            modes[str(selected["outer_cycle_length"])] += 1
            results.append({
                "actual_SIX_source_index": index, "B": row["B"], "prefix": row["prefix"],
                "actual_source_state": row, "all_qualifying_filled_patches": left,
                "selected_strongest_filled_patch": selected,
                "already_in_first_shifted_rule": key in first_keys,
                "already_in_queued_old_midarc_rule": key in old_keys,
            })
        if (index+1) % 500 == 0:
            print(json.dumps({"actual_SIX_prefixes_scanned": index+1,
                              "sharp_shifted_qualifying_prefixes": len(results),
                              "new_formal_payments": 0}), flush=True)
    keys = {(row["B"], tuple(row["prefix"])) for row in results}
    if not first_keys <= keys:
        raise ValueError("sharp shifted rule lost a first-shifted obstruction")
    if any(binding.sha(path) != digest for path, digest in digests.items()):
        raise ValueError("sharp shifted source/code/proof changed during scan")
    report = {
        "schema": "N26-SIX-frontier-sharp-shifted-core-mathematical-scan-v1",
        "verified": False, "input_sha256": digests,
        "exact_sharp_arc_continuous_disk_AND_target_inequalities": targets,
        "entire_actual_SIX_source_rows_scanned": len(source["pending_states"]),
        "qualifying_whole_prefixes": len(results),
        "qualifying_family_counts": dict(Counter(str(row["B"]) for row in results)),
        "selected_outer_cycle_length_counts": dict(modes),
        "all_first_shifted_obstructions_retained": len(first_keys),
        "all_queued_old_midarc_prefix_obstructions_retained": len(old_keys),
        "additional_beyond_first_shifted_NOT_admitted": len(keys-first_keys),
        "additional_beyond_queued_old_midarc_NOT_admitted": len(keys-old_keys),
        "prospective_frontier_NOT_current": len(source["pending_states"])-len(results),
        "results": results, "all_raw_complete_terminals_retained": True,
        "independent_full_source_reconstruction_AND_geometry_current_final_STILL_required": True,
        "candidate_whole_roots_removed": 0, "new_formal_geometric_payments": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "n27_started": False,
    }
    with output.open("x", encoding="utf-8", newline="\n") as stream:
        stream.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({key: value for key, value in report.items()
                      if key not in ("input_sha256", "results",
                                     "exact_sharp_arc_continuous_disk_AND_target_inequalities")}),
          flush=True)


if __name__ == "__main__":
    main()
