"""Discovery-only refinement of explicit accepted-seed current forest schemas."""

import argparse
from collections import deque
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_candidate_energy_local_forest as forest
import n26_candidate_seed_extension as contract
import n26_current_seeded_candidate_source as source
from n26_sharp_radius_constraints import tighten
from propose_common_grid_candidate_curvature import refine
from propose_candidate_curvature_energy import stationary
from propose_seeded_current_candidate_forest import open_queue


def main():
    parser = argparse.ArgumentParser()
    for name in ("source", "source-replay", "current-audit", "current-digest-recheck", "output"):
        parser.add_argument("--" + name, type=Path, required=True)
    parser.add_argument("--source-index", type=int, required=True)
    parser.add_argument("--checks", type=int, default=255)
    parser.add_argument("--maximum-depth", type=int, default=12)
    parser.add_argument("--try-local", action="store_true")
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    if args.checks <= 0 or args.maximum_depth < 0:
        raise ValueError("accepted-seed discovery requires finite explicit limits")
    accepted, values, pending, inventory, paid = source.gate(
        args.source, args.source_replay, args.current_audit, args.current_digest_recheck
    )
    original, kernel, arcs = values[3], values[5], values[6]
    row = next((row for row in pending if row["index"] == args.source_index), None)
    if row is None:
        raise ValueError("accepted-seed discovery requested a previously paid or nonexistent current root")
    seed_path = args.source / "PROPOSAL.json"
    seed = next((item for item in source.read(seed_path)["forests"]
                 if item["source_OPEN_index"] == args.source_index), None)
    if seed is None:
        raise ValueError("selected current root has no explicit actual accepted forest seed")
    nodes = deepcopy(seed["nodes"])
    contract.gate(row, seed, {**seed, "nodes": nodes})
    initial, retained, _ = forest.replay(original, kernel, arcs, row, nodes)
    queue = open_queue(original, row, nodes)
    if initial["source_candidate_root_fully_lower_bounded"] or len(queue) != len(retained):
        raise ValueError("accepted-seed discovery reopened a paid root or lost an OPEN leaf")
    classification = next(item for item in source.read(args.source / "ROOT-CLASSIFICATION.json")
                          if item["source_OPEN_index"] == args.source_index)
    if classification != {"source_OPEN_index": row["index"], "actual_source_closed_box": row, **initial}:
        raise ValueError("actual accepted seed did not reconstruct its published classification")
    inventory.extend((seed_path, Path(__file__), Path(contract.__file__), Path(forest.__file__)))
    inventory.extend(Path(__file__).with_name(name) for name in (
        "propose_seeded_current_candidate_forest.py", "propose_common_grid_candidate_curvature.py",
        "propose_candidate_curvature_energy.py", "propose_quadratic_energy_minorant.py",
        "propose_quadratic_secant_refinement.py",
    ))
    hashes = {linux(path): source.sha(path) for path in inventory}
    turns = [(F(a) + F(b)) / 2 for a, b in original["cap"]["known_candidate_tiny_angle_cells"]]
    checks = 0
    while queue and checks < args.checks:
        index, lower, upper, depth = queue.popleft()
        checks += 1
        box = tighten(original["matrix"], lower, upper)
        if box is None:
            nodes[index] = {"kind": "EMPTY"}
            continue
        lower, upper = box
        if args.try_local:
            try:
                forest.local_proof(original, lower, upper)
            except ValueError:
                pass
            else:
                nodes[index] = {"kind": "LOCAL"}
                continue
        angles, _ = stationary(kernel, original["matrix"], lower, upper, turns)
        certificate, checked, _ = refine(
            kernel, original["matrix"],
            {"lower": list(map(str, lower)), "upper": list(map(str, upper))},
            angles, original["radius"], arcs
        )
        if checked["radius_at_most_Rstar_whole_box_excluded"]:
            nodes[index] = {"kind": "ENERGY", "certificate": certificate}
        elif depth < args.maximum_depth:
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
            print(json.dumps({"verified": False, "source_index": row["index"], "new_checks": checks,
                              "counts": {kind: sum(node["kind"] == kind for node in nodes)
                                         for kind in forest.KINDS}}), flush=True)
    extension = {"source_OPEN_index": row["index"], "actual_source_closed_box": row, "nodes": nodes}
    preserved = contract.gate(row, seed, extension)
    exact, retained, _ = forest.replay(original, kernel, arcs, row, nodes)
    for text, digest in hashes.items():
        if source.sha(text) != digest:
            raise ValueError("accepted-seed discovery source changed during execution: " + text)
    report = {
        "schema": "N26-unaccepted-current-candidate-seeded-ENERGY-LOCAL-forest-v1",
        "verified": False, "radius_scope": "same-root-Rstar",
        "source": linux(args.source), "source_replay": linux(args.source_replay),
        "source_acceptance_sha256": source.sha(args.source / "VERIFIED.json"),
        "source_pending_angles_sha256": source.sha(args.source / "PENDING-ANGLES.json"),
        "current_audit": linux(args.current_audit),
        "current_audit_sha256": source.sha(args.current_audit),
        "current_digest_recheck": linux(args.current_digest_recheck),
        "current_digest_recheck_sha256": source.sha(args.current_digest_recheck),
        "source_actual_remaining_candidate_roots": len(pending),
        "already_paid_current_source_whole_root_indices": [row["source_OPEN_index"] for row in paid],
        "accepted_seed_proposal_sha256": source.sha(seed_path),
        "accepted_seed_exact_result": initial,
        "old_paid_leaves_and_closed_splits_retained_identically": True,
        "seed_extension_contract": preserved,
        "forests": [{**extension, "discovery_exact_result": exact,
                     "all_unvisited_OPEN_and_shared_boundaries_retained": True}],
        "source_roots_attempted": 1,
        "proposed_complete_lower_bounded_source_roots": int(exact["source_candidate_root_fully_lower_bounded"]),
        "new_leaf_checks": checks, "remaining_explicit_closed_OPEN_leaves": len(retained),
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
