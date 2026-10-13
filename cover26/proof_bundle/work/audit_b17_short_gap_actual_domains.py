"""Read-only nonredundancy and whole-state criteria on actual B17 domains."""

from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_origin import OriginReference
import n26_force as force
import verify_conditional_force_stage as binding


def closed(matrix):
    result = [row[:] for row in matrix]
    for k in range(len(result)):
        for i in range(len(result)):
            for j in range(len(result)):
                result[i][j] = min(result[i][j], result[i][k]+result[k][j])
    return None if any(result[i][i] < 0 for i in range(len(result))) else result


def all_gaps_at_least(matrix, lower):
    if lower*force.D != int(lower*force.D):
        raise ValueError("gap lower bound not exactly on this matrix scale")
    raw, result = int(lower*force.D), [row[:] for row in matrix]
    for j in range(1, len(result)):
        result[j][j-1] = min(result[j][j-1], -raw)
    result[0][-1] = min(result[0][-1], force.D-raw)
    return closed(result)


def main():
    output = Path("outputs/n26-b17-short-gap-actual-domain-audit-v1.json")
    if output.exists():
        raise FileExistsError(output)
    stage = Path("outputs/n26-conditional-force-stage-v35-sparse-v1")
    accepted = binding.read(stage/"VERIFIED.json")
    source = stage/"FRONTIER.json"
    if (binding.sha(source) != accepted["files"]["FRONTIER.json"]
            or binding.sha(force.__file__) != accepted["files"]["n26_force.py"]):
        raise ValueError("actual accepted state/domain source changed")
    arithmetic_path = Path("outputs/n26-b17-nine-disk-core-short-gap-arithmetic-v1.json")
    arithmetic = binding.read(arithmetic_path)
    alpha = F(arithmetic["necessary_at_least_one_cyclic_ownership_gap_STRICTLY_below_turns"])
    if alpha != F(9, 200) or arithmetic["both_exact_arithmetic_routes_strict"] is not True:
        raise ValueError("new geometric necessary-condition arithmetic changed")
    proof = Path("work/n26-b17-nine-disk-core-short-gap-proof.md")
    if binding.sha(proof) != arithmetic["proof_note_sha256"]:
        raise ValueError("new geometric proof changed")
    digests = {str(path): binding.sha(path) for path in (
        source, stage/"VERIFIED.json", arithmetic_path, proof, Path(__file__),
        Path(force.__file__))}
    states = [row for row in binding.read(source)["pending_states"] if row["B"] == 17]
    selected = [states[k*len(states)//64] for k in range(64)]
    reference = OriginReference(26, 17, "dfs", caps=force.CAPS, scale=force.D)
    results = []
    for row in selected:
        prefix = tuple(row["prefix"])
        state = reference.resolve(prefix)
        if reference.entry(prefix, state, reference.children(state)) != {
                key: value for key, value in row.items() if key != "B"}:
            raise ValueError("actual accepted B17 prefix/state failed reconstruction")
        matrix = force.angular_domain({"N": 26, "B": 17, "next": row["next"], "faces": row["faces"]})
        lower_gaps = [F(-matrix[j][j-1], force.D) for j in range(1, 17)]
        lower_gaps.append(1-F(matrix[0][16], force.D))
        whole_excluded = all(value >= alpha for value in lower_gaps)
        ordinary = all_gaps_at_least(matrix, alpha)
        robust = all_gaps_at_least(matrix, alpha+F(1, 10000))
        witness = None
        if ordinary is not None:
            chosen = robust if robust is not None else ordinary
            point = [F(-chosen[j][0], force.D) for j in range(17)]
            gaps = [point[j]-point[j-1] for j in range(1, 17)]+[1-point[-1]]
            if (point[0] != 0 or any(point[j]-point[i] > F(matrix[i][j], force.D)
                                   for i in range(17) for j in range(17))
                    or min(gaps) < alpha):
                raise AssertionError("exact old-domain/new-condition counterpoint is invalid")
            witness = {"exact_anchor_turns": list(map(str, point)),
                       "exact_cyclic_ownership_gaps": list(map(str, gaps)),
                       "exact_minimum_gap_excess_above_new_threshold": str(min(gaps)-alpha),
                       "old_necessary_angular_model_point_NOT_a_disk_cover": True}
        results.append({"actual_source_prefix": row["prefix"], "introduced_centers": row["next"],
                        "actual_old_domain_minimum_gap_bounds": list(map(str, lower_gaps)),
                        "new_constraint_already_implied_by_old_angular_domain": ordinary is None,
                        "exact_new_constraint_removes_an_old_angular_point": witness is not None,
                        "positive_gap_margin_counterpoint_found": robust is not None,
                        "whole_actual_state_geometrically_excluded_by_gap_bounds": whole_excluded,
                        "counterpoint": witness})
    for text, digest in digests.items():
        if binding.sha(Path(text)) != digest:
            raise ValueError("actual domain audit input changed")
    report = {
        "schema": "N26-B17-short-gap-actual-closed-angular-domain-audit-v1",
        "verified": False, "actual_standalone_B17_source_states": len(states),
        "actual_source_states_individually_reconstructed_and_checked": len(results),
        "states_with_exact_old_angular_points_removed_by_new_condition": sum(
            row["exact_new_constraint_removes_an_old_angular_point"] for row in results),
        "states_with_positive_gap_margin_removed_points": sum(
            row["positive_gap_margin_counterpoint_found"] for row in results),
        "states_whose_old_domain_already_implies_new_condition": sum(
            row["new_constraint_already_implied_by_old_angular_domain"] for row in results),
        "whole_actual_states_excluded_by_gap_bounds": sum(
            row["whole_actual_state_geometrically_excluded_by_gap_bounds"] for row in results),
        "input_sha256": digests, "results": results,
        "subset_test_NOT_an_all_family_exhaustion_or_volume_measure": True,
        "original_frozen_source_executors_and_all_frontiers_UNMODIFIED": True,
        "actual_current_source_frontier_nodes_removed": 0,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
    }
    with output.open("x", encoding="utf-8", newline="\n") as target:
        target.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({key: report[key] for key in (
        "actual_standalone_B17_source_states",
        "actual_source_states_individually_reconstructed_and_checked",
        "states_with_exact_old_angular_points_removed_by_new_condition",
        "states_with_positive_gap_margin_removed_points",
        "states_whose_old_domain_already_implies_new_condition",
        "whole_actual_states_excluded_by_gap_bounds")}, indent=2), flush=True)


if __name__ == "__main__":
    main()
