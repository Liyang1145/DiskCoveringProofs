"""Fresh unaccepted forest discovery on the semantically folded current roots."""

import argparse
from collections import deque
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_candidate_energy_local_forest as forest
import n26_current_candidate_forest_source as source
from n26_sharp_radius_constraints import tighten
from propose_candidate_curvature_energy import stationary
from propose_common_grid_candidate_curvature import refine


def discover(original, kernel, arcs, pending, indices, checks_per_root, branch_depth, try_local):
    chosen = [row for row in pending if row["index"] in indices]
    if len(set(indices)) != len(indices) or {row["index"] for row in chosen} != set(indices):
        raise ValueError("continuation requested a duplicate, already paid or nonexistent current root")
    matrix, radius = original["matrix"], original["radius"]
    root_turns = [(F(a) + F(b)) / 2 for a, b in original["cap"]["known_candidate_tiny_angle_cells"]]
    forests = []
    for row in chosen:
        nodes = [{"kind": "OPEN"}]
        queue = deque([(0, list(map(F, row["sharp_lower"])), list(map(F, row["sharp_upper"])), 0)])
        checks = 0
        while queue and checks < checks_per_root:
            index, lower, upper, depth = queue.popleft()
            checks += 1
            box = tighten(matrix, lower, upper)
            if box is None:
                nodes[index] = {"kind": "EMPTY"}
                continue
            lower, upper = box
            if try_local:
                try:
                    forest.local_proof(original, lower, upper)
                except ValueError:
                    pass
                else:
                    nodes[index] = {"kind": "LOCAL"}
                    continue
            angles, _ = stationary(kernel, matrix, lower, upper, root_turns)
            current_box = {"lower": list(map(str, lower)), "upper": list(map(str, upper))}
            certificate, checked, _ = refine(kernel, matrix, current_box, angles, radius, arcs)
            if checked["radius_at_most_Rstar_whole_box_excluded"]:
                nodes[index] = {"kind": "ENERGY", "certificate": certificate}
            elif depth < branch_depth:
                eta = list(map(F, certificate["eta"]))
                axes = [k for k in range(len(lower)) if lower[k] < upper[k]]
                if axes:
                    axis = max(axes, key=lambda k: (upper[k] - lower[k])**2 * (eta[k] + F(1, 10**12)))
                    middle = (lower[axis] + upper[axis]) / 2
                    children = [len(nodes), len(nodes) + 1]
                    nodes.extend([{"kind": "OPEN"}, {"kind": "OPEN"}])
                    nodes[index] = {"kind": "SPLIT", "axis": axis, "mid": str(middle), "children": children}
                    lu, rl = list(upper), list(lower)
                    lu[axis], rl[axis] = middle, middle
                    queue.extend(((children[0], list(lower), lu, depth + 1),
                                  (children[1], rl, list(upper), depth + 1)))
            if checks % 4 == 0:
                print(json.dumps({
                    "verified": False, "source_index": row["index"], "checks": checks,
                    "counts": {kind: sum(node["kind"] == kind for node in nodes) for kind in forest.KINDS},
                }), flush=True)
        result, _, _ = forest.replay(original, kernel, arcs, row, nodes)
        forests.append({
            "source_OPEN_index": row["index"], "actual_source_closed_box": row,
            "nodes": nodes, "discovery_exact_result": result,
            "all_unvisited_OPEN_and_shared_boundaries_retained": True,
        })
        print(json.dumps({"verified": False, "source_index": row["index"], **result}, indent=2), flush=True)
    return forests


def main():
    parser = argparse.ArgumentParser()
    for name in ("source", "source-replay", "current-audit", "current-digest-recheck", "output"):
        parser.add_argument("--" + name, type=Path, required=True)
    parser.add_argument("--only-indices", type=int, nargs="+", required=True)
    parser.add_argument("--checks-per-root", type=int, default=31)
    parser.add_argument("--branch-depth", type=int, default=4)
    parser.add_argument("--try-local", action="store_true")
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    if args.checks_per_root <= 0 or args.branch_depth < 0:
        raise ValueError("candidate continuation limits must retain a finite explicit forest")
    acceptance, values, pending, inventory, previous_paid = source.gate(
        args.source, args.source_replay, args.current_audit, args.current_digest_recheck
    )
    inventory.extend(Path(__file__).with_name(name) for name in (
        "propose_current_candidate_common_grid_forests.py",
        "propose_common_grid_candidate_curvature.py", "propose_candidate_curvature_energy.py",
        "propose_quadratic_energy_minorant.py", "propose_quadratic_secant_refinement.py",
    ))
    hashes = {linux(path): source.sha(path) for path in inventory}
    forests = discover(values[3], values[5], values[6], pending, args.only_indices,
                       args.checks_per_root, args.branch_depth, args.try_local)
    for text, digest in hashes.items():
        if source.sha(text) != digest:
            raise ValueError("folded current candidate source changed during discovery: " + text)
    report = {
        "schema": "N26-unaccepted-current-candidate-energy-LOCAL-continuation-forests-v1",
        "verified": False, "radius_scope": "same-root-Rstar",
        "source": linux(args.source), "source_replay": linux(args.source_replay),
        "source_acceptance_sha256": source.sha(args.source / "VERIFIED.json"),
        "source_pending_angles_sha256": source.sha(args.source / "PENDING-ANGLES.json"),
        "current_audit": linux(args.current_audit),
        "current_audit_sha256": source.sha(args.current_audit),
        "current_digest_recheck": linux(args.current_digest_recheck),
        "current_digest_recheck_sha256": source.sha(args.current_digest_recheck),
        "already_paid_accepted_forest_root_indices": [row["source_OPEN_index"] for row in previous_paid],
        "source_actual_remaining_candidate_roots": len(pending),
        "discovery_strategy": "outward-common-grid-diagonals-and-fresh-child-stationary-references",
        "forests": forests,
        "proposed_complete_lower_bounded_source_roots": sum(
            item["discovery_exact_result"]["source_candidate_root_fully_lower_bounded"] for item in forests
        ),
        "source_roots_attempted": len(forests),
        "current_candidate_source_roots_removed_by_discovery": 0,
        "original_52_coordinate_local_allowance_unchanged": "7/800000",
        "independent_current_source_and_complete_forest_acceptance_still_required": True,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "files": hashes, "executed_producer_sha256": source.sha(__file__),
    }
    args.output.write_text(json.dumps(report, separators=(",", ":")) + "\n", encoding="utf-8")
    print(json.dumps({key: val for key, val in report.items() if key not in ("forests", "files")}, indent=2),
          flush=True)


if __name__ == "__main__":
    main()
