"""Full actual SIX-source scan of the NEW common-window union lemma."""

from collections import Counter
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_common_window_union_patches as rule
import verify_conditional_force_stage as binding


def main():
    output = Path("outputs/n26-SIX-common-window-union-filled-patches-mathematical-scan-v1.json")
    if output.exists():
        raise FileExistsError(output)
    source_path = Path("outputs/n26-current28-six-target-source-geometry-v1/FRONTIER.json")
    previous_path = Path("outputs/n26-SIX-frontier-sharp-shifted-core-mathematical-scan-v1.json")
    previous = binding.read(previous_path)
    for path, digest in previous["input_sha256"].items():
        if binding.sha(path) != digest:
            raise ValueError("new common-window scan changed prior actual source/math bindings")
    source = binding.read(source_path)
    if len(source["pending_states"]) != 5637:
        raise ValueError("common-window scan changed actual completed SIX source")
    old = {(row["B"], tuple(row["prefix"])) for row in previous["results"]}
    digests = {**previous["input_sha256"], **{
        linux(path): binding.sha(path) for path in (
            previous_path, Path(__file__), Path(rule.__file__),
            Path("work/n26-common-window-union-filled-patches-proof.md"))}}
    targets = {str(k): rule.target_gate(k) for k in rule.REQUIRED}
    results, modes, nonconsecutive, multiple = [], Counter(), 0, 0
    for index, row in enumerate(source["pending_states"]):
        first = rule.filled_patches(row)
        second = rule.filled_patches(row, independent=True)
        if first != second:
            raise ValueError("distinct cycle enumerators/face locators/topology gates disagree")
        windows = rule.obstructions(row, first)
        if windows:
            if row["terminal"]:
                raise ValueError("raw complete terminal unexpectedly excluded; preserve and investigate")
            selected = rule.select(windows)
            modes[str(selected["window_length"])] += 1
            nonconsecutive += selected["nonconsecutive_outer_polygon_used"]
            multiple += selected["multiple_filled_patches_used"]
            results.append({
                "actual_SIX_source_index": index, "B": row["B"], "prefix": row["prefix"],
                "actual_source_state": row, "all_certified_filled_patches": first,
                "all_qualifying_common_windows": windows, "selected_strongest_common_window": selected,
                "already_in_sharp_single_consecutive_patch_rule":
                    (row["B"], tuple(row["prefix"])) in old,
            })
        if (index+1) % 250 == 0:
            print(json.dumps({"actual_SIX_rows_scanned": index+1,
                              "common_window_union_obstructions": len(results),
                              "formal_payments": 0}), flush=True)
    keys = {(row["B"], tuple(row["prefix"])) for row in results}
    if not old <= keys or len(old) != 755:
        raise ValueError("common-window union rule lost a previous sharp single-patch obstruction")
    if any(binding.sha(path) != digest for path, digest in digests.items()):
        raise ValueError("common-window source/code/continuous proof changed during scan")
    report = {
        "schema": "N26-SIX-common-window-union-filled-patches-mathematical-scan-v1",
        "verified": False, "input_sha256": digests,
        "exact_sharp_continuous_disk_AND_target_inequalities": targets,
        "entire_actual_SIX_source_rows_scanned": 5637,
        "qualifying_whole_prefixes": len(results),
        "qualifying_family_counts": dict(Counter(str(row["B"]) for row in results)),
        "selected_window_length_counts": dict(modes),
        "selected_nonconsecutive_outer_polygon_obstructions": nonconsecutive,
        "selected_multiple_patch_UNION_obstructions": multiple,
        "all755_prior_sharp_single_patch_obstructions_retained": True,
        "additional_beyond_sharp_single_patch_NOT_admitted": len(keys-old),
        "additional_beyond_queued_old_midarc680_NOT_admitted": len(keys)-680,
        "prospective_frontier_NOT_current": 5637-len(results),
        "results": results,
        "independent_all_original_prefix_reconstruction_AND_geometry_current_final_STILL_required": True,
        "all_raw_complete_terminals_retained": True,
        "new_formal_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
    }
    with output.open("x", encoding="utf-8", newline="\n") as stream:
        stream.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({key: value for key, value in report.items()
                      if key not in ("input_sha256", "results",
                                     "exact_sharp_continuous_disk_AND_target_inequalities")}), flush=True)


if __name__ == "__main__":
    main()
