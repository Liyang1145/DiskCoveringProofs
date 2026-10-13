"""Unaccepted current candidate forests with per-root accepted-history retention."""

import argparse
from collections import deque
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_candidate_energy_local_forest as forest
import n26_candidate_seed_extension as contract
import n26_current_owned_candidate_source as source
from n26_sharp_radius_constraints import tighten
from propose_common_grid_candidate_curvature import refine
from propose_candidate_curvature_energy import stationary
from propose_seeded_current_candidate_forest import open_queue


def main():
    parser = argparse.ArgumentParser()
    for name in ("source", "source-replay", "current-audit", "current-digest-recheck", "output"):
        parser.add_argument("--" + name, type=Path, required=True)
    parser.add_argument("--only-indices", type=int, nargs="+", required=True)
    parser.add_argument("--checks-per-root", type=int, default=31)
    parser.add_argument("--maximum-depth", type=int, default=8)
    parser.add_argument("--try-local", action="store_true")
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    if len(set(args.only_indices)) != len(args.only_indices) or args.checks_per_root <= 0 or args.maximum_depth < 0:
        raise ValueError("owned candidate discovery has duplicate roots or invalid finite limits")
    accepted, values, pending, inventory, _ = source.gate(
        args.source, args.source_replay, args.current_audit, args.current_digest_recheck
    )
    history, paths = source.history(args.source, pending)
    inventory.extend(paths)
    original, kernel, arcs = values[3], values[5], values[6]
    chosen = [row for row in pending if row["index"] in args.only_indices]
    if {row["index"] for row in chosen} != set(args.only_indices):
        raise ValueError("owned discovery selected a nonexistent or already discharged current root")
    inventory.extend((Path(__file__), Path(contract.__file__), Path(forest.__file__)))
    inventory.extend(Path(__file__).with_name(name) for name in (
        "propose_common_grid_candidate_curvature.py", "propose_candidate_curvature_energy.py",
        "propose_quadratic_energy_minorant.py", "propose_quadratic_secant_refinement.py",
        "propose_seeded_current_candidate_forest.py",
    ))
    hashes = {linux(path): source.sha(path) for path in inventory}
    turns = [(F(a) + F(b)) / 2 for a, b in original["cap"]["known_candidate_tiny_angle_cells"]]
    proposed = []
    for row in chosen:
        index = row["index"]
        seed = history.get(index)
        mode = "SEEDED" if seed is not None else "FRESH"
        if seed is None:
            nodes = [{"kind": "OPEN"}]
            queue = deque([(0, list(map(F, row["sharp_lower"])), list(map(F, row["sharp_upper"])), 0)])
        else:
            nodes = deepcopy(seed["nodes"])
            initial, old_pending, _ = forest.replay(original, kernel, arcs, row, nodes)
            if {"source_OPEN_index": index, "actual_source_closed_box": row, **initial} != seed[
                "accepted_source_classification"
            ]:
                raise ValueError("newest owned candidate seed did not replay its actual accepted classification")
            queue = open_queue(original, row, nodes)
            if len(queue) != len(old_pending) or initial["source_candidate_root_fully_lower_bounded"]:
                raise ValueError("owned candidate discovery lost a seed OPEN leaf or reopened a paid root")
        checks = 0
        while queue and checks < args.checks_per_root:
            node_index, lower, upper, depth = queue.popleft()
            checks += 1
            box = tighten(original["matrix"], lower, upper)
            if box is None:
                nodes[node_index] = {"kind": "EMPTY"}
                continue
            lower, upper = box
            if args.try_local:
                try:
                    forest.local_proof(original, lower, upper)
                except ValueError:
                    pass
                else:
                    nodes[node_index] = {"kind": "LOCAL"}
                    continue
            angles, _ = stationary(kernel, original["matrix"], lower, upper, turns)
            certificate, checked, _ = refine(
                kernel, original["matrix"],
                {"lower": list(map(str, lower)), "upper": list(map(str, upper))},
                angles, original["radius"], arcs
            )
            if checked["radius_at_most_Rstar_whole_box_excluded"]:
                nodes[node_index] = {"kind": "ENERGY", "certificate": certificate}
            elif depth < args.maximum_depth:
                eta = list(map(F, certificate["eta"]))
                axes = [k for k in range(len(lower)) if lower[k] < upper[k]]
                if axes:
                    axis = max(axes, key=lambda k: (upper[k] - lower[k])**2 * (eta[k] + F(1, 10**12)))
                    mid = (lower[axis] + upper[axis]) / 2
                    children = [len(nodes), len(nodes) + 1]
                    nodes.extend([{"kind": "OPEN"}, {"kind": "OPEN"}])
                    nodes[node_index] = {"kind": "SPLIT", "axis": axis, "mid": str(mid), "children": children}
                    left, right = list(upper), list(lower)
                    left[axis], right[axis] = mid, mid
                    queue.extend(((children[0], list(lower), left, depth + 1),
                                  (children[1], right, list(upper), depth + 1)))
            if checks % 4 == 0:
                print(json.dumps({
                    "verified": False, "source_index": index, "history_mode": mode, "new_checks": checks,
                    "counts": {kind: sum(node["kind"] == kind for node in nodes) for kind in forest.KINDS},
                }), flush=True)
        extension = {"source_OPEN_index": index, "actual_source_closed_box": row, "nodes": nodes}
        if seed is not None:
            contract.gate(row, seed, extension)
        result, _, _ = forest.replay(original, kernel, arcs, row, nodes)
        proposed.append({
            **extension, "history_mode": mode,
            "accepted_history_source": seed["history_source"] if seed is not None else None,
            "discovery_exact_result": result,
            "all_unvisited_OPEN_and_shared_boundaries_retained": True,
        })
        print(json.dumps({"verified": False, "source_index": index, "history_mode": mode, **result}, indent=2),
              flush=True)
    for text, digest in hashes.items():
        if source.sha(text) != digest:
            raise ValueError("owned candidate discovery source changed during execution: " + text)
    report = {
        "schema": "N26-unaccepted-current-owned-candidate-energy-LOCAL-forests-v1",
        "verified": False, "radius_scope": "same-root-Rstar",
        "source": linux(args.source), "source_replay": linux(args.source_replay),
        "source_acceptance_sha256": source.sha(args.source / "VERIFIED.json"),
        "source_pending_angles_sha256": source.sha(args.source / "PENDING-ANGLES.json"),
        "current_audit": linux(args.current_audit), "current_audit_sha256": source.sha(args.current_audit),
        "current_digest_recheck": linux(args.current_digest_recheck),
        "current_digest_recheck_sha256": source.sha(args.current_digest_recheck),
        "source_actual_remaining_candidate_roots": len(pending),
        "forests": proposed, "source_roots_attempted": len(proposed),
        "proposed_complete_lower_bounded_source_roots": sum(
            item["discovery_exact_result"]["source_candidate_root_fully_lower_bounded"] for item in proposed
        ),
        "all_newest_accepted_per_root_forests_and_unattempted_whole_roots_preserved": True,
        "current_candidate_source_roots_removed_by_discovery": 0,
        "original_52_coordinate_local_allowance_unchanged": "7/800000",
        "independent_source_and_closed_forest_acceptance_still_required": True,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "files": hashes, "executed_producer_sha256": source.sha(__file__),
    }
    args.output.write_text(json.dumps(report, separators=(",", ":")) + "\n", encoding="utf-8")
    print(json.dumps({key: val for key, val in report.items() if key not in ("forests", "files")}, indent=2),
          flush=True)


if __name__ == "__main__":
    main()
