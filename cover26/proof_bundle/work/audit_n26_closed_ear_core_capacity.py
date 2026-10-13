"""Actual whole-prefix geometry pilot with EXPLICIT embedded-source hypothesis."""

from collections import Counter
from functools import lru_cache
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_origin import OriginReference, validate_disk
import n26_force as force
import verify_conditional_force_stage as binding


def ear_patch(row):
    b, introduced, faces = row["B"], row["next"], row["faces"]
    if introduced > 26 or 26-introduced > 3 or len(faces) != 2*(introduced-b)+1:
        return None
    used = {i for face in faces for i in range(introduced) if face & (1 << i)}
    owners = used.intersection(range(b))
    if (len(owners) != 3 or used.difference(range(b)) != set(range(b, introduced))):
        return None
    bases = [i for i in range(b) if owners == {i, (i+1) % b, (i+2) % b}]
    if len(bases) != 1:
        return None
    base = bases[0]
    labels = [base, (base+1) % b, (base+2) % b]+list(range(b, introduced))
    inverse = {v: i for i, v in enumerate(labels)}
    mapped = [sum(1 << inverse[i] for i in used if face & (1 << i)) for face in faces]
    adjacency = {v: set() for v in used}
    for face in faces:
        members = {v for v in used if face & (1 << v)}
        for v in members:
            adjacency[v].update(members-{v})
    reached, queue = {base}, [base]
    for v in queue:
        for w in adjacency[v]-reached:
            reached.add(w)
            queue.append(w)
    if reached != used:
        return None
    try:
        edges = validate_disk(len(labels), 3, mapped)
    except ValueError:
        return None
    return {
        "consecutive_boundary_triangle": labels[:3],
        "exact_patch_vertices": len(labels), "exact_patch_edges": edges,
        "exact_patch_faces": len(faces),
        "all_introduced_nonowners_enclosed_by_embedded_patch": list(range(b, introduced)),
        "unintroduced_nonowners_at_most": 26-introduced,
        "four_distinct_outside_ear_core_point_owners_required": 4,
        "exact_missing_outside_ear_owner_count": 4-(26-introduced),
    }


def main():
    output = Path("outputs/n26-closed-ear-core-capacity-actual-state-audit-v1.json")
    if output.exists():
        raise FileExistsError(output)
    stage = Path("outputs/n26-conditional-force-stage-v35-sparse-v1")
    source, accepted = stage/"FRONTIER.json", binding.read(stage/"VERIFIED.json")
    if (binding.sha(source) != accepted["files"]["FRONTIER.json"]
            or binding.sha(force.__file__) != accepted["files"]["n26_force.py"]):
        raise ValueError("actual frozen source/model changed")
    proof = Path("work/n26-closed-ear-core-capacity-proof.md")
    core = Path("outputs/n26-b17-independent-radial-witness-core-coverage-v1.json")
    paths = [source, stage/"VERIFIED.json", proof, core, Path(__file__),
             Path(force.__file__), Path("work/audit_prefix_origin.py"),
             Path("work/audit_prefix_partition.py")]
    digests = {str(path): binding.sha(path) for path in paths}
    refs = {b: OriginReference(26, b, "dfs", caps=force.CAPS, scale=force.D) for b in (14, 15, 16, 17)}
    # Instance-local memoization of the unchanged immutable recurrence.
    for ref in refs.values():
        ref.children = lru_cache(None)(ref.children)
    rows, results = binding.read(source)["pending_states"], []
    for index, row in enumerate(rows):
        patch = ear_patch(row)
        if patch is None:
            continue
        ref, prefix = refs[row["B"]], tuple(row["prefix"])
        state = ref.resolve(prefix)
        if {"B": row["B"], **ref.entry(prefix, state, ref.children(state))} != row:
            raise ValueError("actual closed-ear prefix failed exact reconstruction")
        results.append({
            "actual_stage35_source_index": index, "actual_source_state": row,
            "closed_disk_patch_certificate": patch,
            "entire_geometric_prefix_infeasible_IF_actual_source_is_embedded_triangular_disk": True,
            "actual_source_embedded_physical_dual_and_starring_gate_NOT_admitted": True,
            "complete_angular_domain_and_all_future_continuations_covered_by_argument": True,
            "current_frontier_node_removed": False, "new_geometric_payment": False,
        })
        if len(results) % 100 == 0:
            print(json.dumps({
                "actual_closed_ear_prefixes_individually_reconstructed": len(results),
                "embedded_source_hypothesis_still_required": True,
                "current_nodes_removed": 0, "new_geometric_payments": 0}), flush=True)
    u, h, rcore = F(234701, 1000000), F(565299, 1000000), F(265299, 500000)
    if (not u < F(1, 4) or h != F(4, 5)-u or not h > u
            or not rcore > 2*u or not F(3) < F(7, 4)**2 or not F(3, 4) > F(4, 5)**2):
        raise AssertionError("exact whole-domain ear/core separation constants failed")
    for text, digest in digests.items():
        if binding.sha(Path(text)) != digest:
            raise ValueError("actual source/ear proof changed during audit")
    report = {
        "schema": "N26-actual-closed-ear-core-capacity-conditional-geometric-audit-v1",
        "verified": False, "input_sha256": digests, "results": results,
        "actual_standalone_stage35_source_states_scanned": len(rows),
        "actual_prefixes_individually_reconstructed_with_closed_ear_capacity_obstruction": len(results),
        "conditional_obstruction_by_boundary_family": dict(Counter(str(row["actual_source_state"]["B"]) for row in results)),
        "conditional_obstruction_by_unintroduced_nonowner_count": dict(Counter(
            str(row["closed_disk_patch_certificate"]["unintroduced_nonowners_at_most"]) for row in results)),
        "exact_ear_projection_lower": str(h),
        "exact_ear_projection_margin_above_U": str(h-u),
        "exact_core_target_minimum_pair_distance": str(rcore),
        "exact_core_target_distance_margin_above_2U": str(rcore-2*u),
        "new_whole_prefix_GEOMETRIC_rule_NOT_a_rod_or_sample_only_bound": True,
        "simple_embedded_dual_and_physical_starring_reduction_remains_required": True,
        "frozen_geometric_reduction_proved": False,
        "no_frozen_executor_or_source_changes": True,
        "source_closed_history_and_strict_ledger_UNMODIFIED": True,
        "actual_current_transport_nodes_removed": 0, "new_geometric_payments": 0,
        "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
    }
    with output.open("x", encoding="utf-8", newline="\n") as target:
        target.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({key: report[key] for key in (
        "actual_standalone_stage35_source_states_scanned",
        "actual_prefixes_individually_reconstructed_with_closed_ear_capacity_obstruction",
        "conditional_obstruction_by_boundary_family",
        "conditional_obstruction_by_unintroduced_nonowner_count",
        "actual_current_transport_nodes_removed", "new_geometric_payments")}), flush=True)


if __name__ == "__main__":
    main()
