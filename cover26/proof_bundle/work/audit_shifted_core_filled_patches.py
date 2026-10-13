"""Full actual SIX-frontier scan of NEW shifted-core mathematics.

Never writes an acceptance, current, final or frozen source frontier.
"""

from collections import Counter
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_shifted_core_filled_patches as rule
import verify_conditional_force_stage as binding


def main():
    output = Path("outputs/n26-SIX-frontier-shifted-core-mathematical-scan-v1.json")
    if output.exists():
        raise FileExistsError(output)
    source_path = Path("outputs/n26-current28-six-target-source-geometry-v1/FRONTIER.json")
    current_path = Path("outputs/n26-current28-six-target-supplemental-current-v1.json")
    final_path = Path("outputs/n26-current28-six-target-supplemental-independent-final-v1.json")
    old_scan_path = Path("outputs/n26-current28-midarc-filled-patches-mathematical-scan-v1.json")
    source, current, final, old_scan = map(binding.read, (
        source_path, current_path, final_path, old_scan_path))
    if (
        final["current_audit_sha256"] != binding.sha(current_path)
        or current["files"].get(linux(source_path)) != binding.sha(source_path)
        or current["Rstar_conditional_frontier_pending_subtrees"] != 5637
        or len(source["pending_states"]) != 5637
        or current["global_lower_bound_proved"] is not False
        or source["radius_scope"] != binding.SCOPE
        or source["inherited_source_is_unconditional_at_U"] is not False
    ):
        raise ValueError("shifted scan requires the ACTUAL completed SIX source/current/final identity")
    paths = [source_path, current_path, final_path, old_scan_path, Path(__file__),
             Path(rule.__file__), Path("work/n26_midarc_filled_patches.py"),
             Path("work/audit_prefix_origin.py"), Path("work/audit_prefix_partition.py"),
             Path("work/n26-shifted-core-eight-seven-six-filled-patch-proof.md"),
             Path("work/n26-midarc-seven-and-six-target-filled-patch-proof.md"),
             Path("work/n26-embedded-dual-and-corner-starring-bridge-proof.md")]
    digests = {linux(path): binding.sha(path) for path in paths}
    old_keys = {(row["B"], tuple(row["prefix"])) for row in old_scan["results"]}
    targets = {str(k): rule.target_gate(k) for k in rule.REQUIRED}
    results, selected_modes, seen, old_remaining = [], Counter(), set(), set()
    for index, row in enumerate(source["pending_states"]):
        key = row["B"], tuple(row["prefix"])
        if key in seen:
            raise ValueError("duplicate actual shifted-core source prefix")
        seen.add(key)
        if key in old_keys:
            old_remaining.add(key)
        first, second = rule.patches(row), rule.patches(row, independent_locator=True)
        if first != second:
            raise ValueError("distinct shifted-core patch locators and topology gates disagree")
        if first:
            if row["terminal"]:
                raise ValueError("raw complete terminal unexpectedly excluded; do not delete it")
            selected = max(first, key=lambda item: (
                item["required_DISTINCT_ORIGINAL_outside_nonowners"]
                - item["maximum_all_original_nonowner_slots_outside"],
                -item["outer_cycle_length"]))
            selected_modes[str(selected["outer_cycle_length"])] += 1
            results.append({
                "actual_SIX_source_index": index, "B": row["B"], "prefix": row["prefix"],
                "actual_source_state": row, "all_qualifying_filled_patches": first,
                "selected_strongest_filled_patch": selected,
                "already_in_queued_old_midarc_rule": key in old_keys,
            })
        if (index+1) % 500 == 0:
            print(json.dumps({"actual_SIX_prefixes_scanned": index+1,
                              "new_rule_qualifying_prefixes": len(results),
                              "new_formal_payments": 0}), flush=True)
    selected_keys = {(row["B"], tuple(row["prefix"])) for row in results}
    if not old_remaining <= selected_keys or len(old_remaining) != 680:
        raise ValueError("new shifted-core rule lost an old obstruction or changed the real baseline")
    if any((b, prefix[:length]) in seen for b, prefix in seen for length in range(len(prefix))):
        raise ValueError("actual SIX source has overlapping ancestor/descendant ownership")
    if any(binding.sha(path) != digest for path, digest in digests.items()):
        raise ValueError("shifted-core source/code/proof changed during scan")
    report = {
        "schema": "N26-SIX-frontier-shifted-core-mathematical-scan-v1",
        "verified": False, "input_sha256": digests,
        "exact_continuous_disk_AND_rational_shifted_target_inequalities": targets,
        "entire_actual_SIX_source_rows_scanned": len(source["pending_states"]),
        "qualifying_whole_prefixes": len(results),
        "qualifying_family_counts": dict(Counter(str(row["B"]) for row in results)),
        "selected_outer_cycle_length_counts": dict(selected_modes),
        "all_queued_old_midarc_prefix_obstructions_retained": len(old_remaining),
        "additional_beyond_queued_old_midarc_NOT_admitted": len(selected_keys-old_remaining),
        "prospective_frontier_NOT_current": len(source["pending_states"])-len(results),
        "results": results,
        "all_raw_complete_terminals_retained": True,
        "independent_source_reconstruction_AND_geometry_current_final_STILL_required": True,
        "candidate_whole_roots_removed": 0, "new_formal_geometric_payments": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "n27_started": False,
    }
    with output.open("x", encoding="utf-8", newline="\n") as stream:
        stream.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({key: value for key, value in report.items()
                      if key not in ("input_sha256", "results",
                                     "exact_continuous_disk_AND_rational_shifted_target_inequalities")}),
          flush=True)


if __name__ == "__main__":
    main()
