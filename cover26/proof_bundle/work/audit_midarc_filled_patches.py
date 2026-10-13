"""Actual full source scan of NEW seven/six/five target midarc mathematics.

This is exploratory mathematical DATA, NOT a source geometry acceptance,
complete current, independent final or proof of n26 optimality.
"""

from collections import Counter
import json
from pathlib import Path

import n26_midarc_filled_patches as rule
import verify_conditional_force_stage as binding


def main():
    output = Path("outputs/n26-current28-midarc-filled-patches-mathematical-scan-v1.json")
    if output.exists():
        raise FileExistsError(output)
    source_path = Path("outputs/n26-conditional-force-stage-v28-sparse-v1/FRONTIER.json")
    six_path = Path("outputs/n26-current28-six-target-filled-ear-mathematical-scan-v1.json")
    quad_path = Path("outputs/n26-current28-five-target-filled-quadrilateral-mathematical-scan-v1.json")
    source, six, quad = binding.read(source_path), binding.read(six_path), binding.read(quad_path)
    six_indices = {row["actual_source_index"] for row in six["results"]}
    old_union = six_indices | {row["actual_source_index"] for row in quad["results"]}
    paths = [
        source_path, six_path, quad_path, Path(__file__), Path(rule.__file__),
        Path("work/n26-midarc-seven-and-six-target-filled-patch-proof.md"),
        Path("work/n26-embedded-dual-and-corner-starring-bridge-proof.md"),
        Path("work/audit_prefix_origin.py"),
    ]
    digests = {str(path): binding.sha(path) for path in paths}
    targets = {str(k): rule.target_gate(k) for k in rule.REQUIRED}
    results, chosen_modes = [], Counter()
    for index, row in enumerate(source["pending_states"]):
        first, second = rule.patches(row), rule.patches(row, independent_locator=True)
        if first != second:
            raise AssertionError("two distinct midarc locators/topology gates disagree")
        if first:
            if row["terminal"]:
                raise AssertionError("raw complete candidate/competitor falsely excluded by midarc")
            selected = max(first, key=lambda patch: (
                patch["required_DISTINCT_ORIGINAL_outside_nonowners"]
                - patch["maximum_all_original_nonowner_slots_outside"],
                -patch["outer_cycle_length"],
            ))
            chosen_modes[str(selected["outer_cycle_length"])] += 1
            results.append({
                "actual_source_index": index, "B": row["B"], "prefix": row["prefix"],
                "actual_source_state": row, "all_qualifying_filled_patches": first,
                "selected_strongest_filled_patch": selected,
                "already_in_frozen_six_triangle_rule": index in six_indices,
                "already_in_six_and_five_quad_union": index in old_union,
            })
        if (index+1) % 1000 == 0:
            print(json.dumps({
                "midarc_original_source_rows_scanned": index+1,
                "qualifying_prefixes": len(results), "formal_payments": 0,
            }), flush=True)
    indices = {row["actual_source_index"] for row in results}
    if not old_union <= indices:
        raise AssertionError("new midarc rule lost an older triangle/quadrilateral obstruction")
    if any(binding.sha(path) != digest for path, digest in digests.items()):
        raise ValueError("midarc source/code/continuous proof changed")
    report = {
        "schema": "N26-current28-midarc-filled-patches-mathematical-scan-v1",
        "verified": False, "input_sha256": digests,
        "exact_seven_six_five_target_inequalities": targets,
        "results": results, "entire_original_source_rows_scanned": len(source["pending_states"]),
        "qualifying_whole_prefixes": len(results),
        "qualifying_family_counts": dict(Counter(str(row["B"]) for row in results)),
        "selected_outer_cycle_length_counts": dict(chosen_modes),
        "old_frozen_six_triangle_prefixes_retained": len(six_indices),
        "old_six_and_five_quad_union_retained": len(old_union),
        "additional_beyond_frozen_six_triangles_NOT_accepted": len(indices-six_indices),
        "additional_beyond_six_and_five_quad_union_NOT_accepted": len(indices-old_union),
        "additional_beyond_frozen_six_actual_source_indices": sorted(indices-six_indices),
        "prospective_frontier_NOT_current": len(source["pending_states"])-len(results),
        "independent_entire_source_reconstruction_AND_geometry_current_final_STILL_required": True,
        "candidate_whole_roots_removed": 0, "new_formal_geometric_payments": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
    }
    with output.open("x", encoding="utf-8", newline="\n") as target:
        target.write(json.dumps(report, indent=2) + "\n")
    print(json.dumps({key: value for key, value in report.items()
                      if key not in ("input_sha256", "exact_seven_six_five_target_inequalities",
                                     "results", "additional_beyond_frozen_six_actual_source_indices")}),
          flush=True)


if __name__ == "__main__":
    main()
