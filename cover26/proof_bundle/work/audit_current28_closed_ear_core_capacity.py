"""Two-method mathematical scan of the ACTUAL current28 bound frontier.

No current join, payment, geometry promotion, or independent-final rerun.
"""

from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
import json
from pathlib import Path

from audit_prefix_origin import OriginReference
from audit_prefix_partition import linux
from audit_n26_closed_ear_core_capacity import ear_patch
from test_n26_closed_ear_core_capacity import independent_patch
import n26_force as force
import verify_conditional_force_stage as binding


def main():
    output = Path("outputs/n26-actual-current28-closed-ear-core-capacity-mathematical-audit-v1.json")
    if output.exists():
        raise FileExistsError(output)
    current_path = Path("outputs/n26-twenty-eighth-conditional-current-audit-v28-sparse-v1-strict-with-owned8-scope.json")
    final_path = Path("outputs/n26-twenty-eighth-conditional-final-digest-recheck-v28-sparse-v1-strict-with-owned8.json")
    expected_current = "d306ec18c476fc4dc40d19284cb0281db82e457201a97f85e361c1b37c6a17ea"
    expected_final = "e10b9530e365e29efab09a29c05f62baa9223b65abc5e5b2ebabc497bca0fe55"
    if binding.sha(current_path) != expected_current or binding.sha(final_path) != expected_final:
        raise ValueError("not the actual completed current28/independent-final pair")
    current, final = binding.read(current_path), binding.read(final_path)
    stage = Path("outputs/n26-conditional-force-stage-v28-sparse-v1")
    source, acceptance = stage/"FRONTIER.json", stage/"VERIFIED.json"
    paths = [source, acceptance, current_path, final_path, Path(__file__),
             Path("work/n26-closed-ear-core-capacity-proof.md"),
             Path("work/audit_n26_closed_ear_core_capacity.py"),
             Path("work/test_n26_closed_ear_core_capacity.py"),
             Path("outputs/n26-closed-ear-core-capacity-actual-state-audit-v1.json"),
             Path("outputs/n26-closed-ear-core-capacity-independent-audit-v1.json"),
             Path(force.__file__), Path("work/audit_prefix_origin.py"),
             Path("work/audit_prefix_partition.py")]
    digests = {str(path): binding.sha(path) for path in paths}
    accepted = binding.read(acceptance)
    if (final["current_audit_sha256"] != expected_current
            or final["all_current_file_digests_rehashed"] is not True
            or current["files"][linux(source)] != digests[str(source)]
            or current["files"][linux(acceptance)] != digests[str(acceptance)]
            or accepted["files"]["FRONTIER.json"] != digests[str(source)]
            or accepted["files"]["n26_force.py"] != digests[str(Path(force.__file__))]
            or final["candidate_angle_unresolved_closed_boxes"] != 25
            or final["global_lower_bound_proved"] is not False
            or final["global_optimality_proved"] is not False):
        raise ValueError("actual current28 source/final association or original scope changed")
    independent = binding.read(Path("outputs/n26-closed-ear-core-capacity-independent-audit-v1.json"))
    if (independent["actual_closed_ear_prefixes_independently_reconstructed_and_checked"] != 640
            or independent["frozen_geometric_reduction_proved"] is not False):
        raise ValueError("not the completed independent standalone rule control")
    rows = binding.read(source)["pending_states"]
    counts = Counter(row["B"] for row in rows)
    if (len(rows) != final["Rstar_conditional_frontier_pending_subtrees"]
            or counts != Counter({row["B"]: row["pending_subtrees"]
                                  for row in current["Rstar_conditional_frontier_families"]})):
        raise ValueError("actual formal current frontier counts/families changed")
    refs = {b: OriginReference(26, b, "dfs", caps=force.CAPS, scale=force.D) for b in counts}
    for ref in refs.values():
        ref.children = lru_cache(None)(ref.children)
    results = []
    for index, row in enumerate(rows):
        first, second = ear_patch(row), independent_patch(row)
        if first != second:
            raise AssertionError("two independent patch constructions disagree on actual current source")
        if first is None:
            continue
        ref, prefix = refs[row["B"]], tuple(row["prefix"])
        state = ref.resolve(prefix)
        if {"B": row["B"], **ref.entry(prefix, state, ref.children(state))} != row:
            raise ValueError("actual formal closed-ear state failed original exact reconstruction")
        results.append({
            "actual_formal_current28_source_index": index, "actual_source_state": row,
            "two_method_closed_patch_certificate": first,
            "whole_geometric_prefix_impossible_UNDER_EMBEDDED_PHYSICAL_SOURCE_HYPOTHESIS": True,
            "unrestricted_embedded_dual_and_starring_admission_NOT_performed": True,
            "formal_current_node_removed": False,
        })
    u = F(234701, 1000000)
    for text, digest in digests.items():
        if binding.sha(Path(text)) != digest:
            raise ValueError("current28 mathematical input changed during audit")
    report = {
        "schema": "N26-actual-formal-current28-closed-ear-core-capacity-mathematical-audit-v1",
        "verified": False, "input_sha256": digests, "results": results,
        "actual_current_audit_sha256": expected_current,
        "actual_independent_final_sha256": expected_final,
        "actual_current28_frontier_states_scanned_by_two_patch_methods": len(rows),
        "actual_current28_whole_prefix_conditional_geometric_obstructions": len(results),
        "actual_current28_obstruction_boundary_family_counts": dict(
            Counter(str(row["actual_source_state"]["B"]) for row in results)),
        "actual_current28_obstruction_missing_nonowner_counts": dict(
            Counter(str(26-row["actual_source_state"]["next"]) for row in results)),
        "source_current_final_exact_bound_association_checked": True,
        "this_is_NOT_a_new_complete_current_or_independent_final_replay": True,
        "exact_ear_projection_margin_above_U": str(F(4, 5)-2*u),
        "exact_four_core_points_minimum_pair_distance_margin_above_2U": str(1-4*u),
        "simple_embedded_dual_physical_source_and_starring_gate_REQUIRED_NOT_admitted": True,
        "frozen_geometric_reduction_proved": False,
        "actual_current_transport_frontier_STILL": len(rows),
        "actual_current_whole_candidate_roots_STILL": 25,
        "actual_current_nodes_removed": 0, "new_geometric_payments": 0,
        "candidate_whole_roots_removed": 0,
        "source_frozen_executors_histories_strict_ledgers_paid_leaves_UNMODIFIED": True,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
    }
    with output.open("x", encoding="utf-8", newline="\n") as target:
        target.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({key: report[key] for key in (
        "actual_current28_frontier_states_scanned_by_two_patch_methods",
        "actual_current28_whole_prefix_conditional_geometric_obstructions",
        "actual_current28_obstruction_boundary_family_counts",
        "actual_current28_obstruction_missing_nonowner_counts",
        "actual_current_transport_frontier_STILL", "actual_current_whole_candidate_roots_STILL",
        "actual_current_nodes_removed")}), flush=True)


if __name__ == "__main__":
    main()
