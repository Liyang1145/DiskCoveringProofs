"""Refine only OPEN leaves of an actually accepted current candidate forest.

All old paid leaves and the complete original closed partition are retained.
This writes an unaccepted proposal; it changes no current root count.
"""

import argparse
from collections import deque
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_candidate_energy_local_forest as forest
import n26_current_candidate_continuation_source as source
from n26_sharp_radius_constraints import tighten
from propose_candidate_curvature_energy import stationary
from propose_common_grid_candidate_curvature import refine


def open_queue(original, row, nodes):
    stack = [(0, list(map(F, row["sharp_lower"])), list(map(F, row["sharp_upper"])), 0)]
    seen, pending = set(), []
    while stack:
        index, lower, upper, depth = stack.pop()
        if index in seen or not 0 <= index < len(nodes):
            raise ValueError("accepted seed repeats or hides a partition node")
        seen.add(index)
        node = nodes[index]
        box = tighten(original["matrix"], lower, upper)
        if box is None:
            if node != {"kind": "EMPTY"}:
                raise ValueError("accepted seed altered an exact empty leaf")
            continue
        lower, upper = box
        if node["kind"] == "SPLIT":
            stack.extend((*child, depth + 1) for child in reversed(
                forest.split(node, index, lower, upper, len(nodes))
            ))
        elif node["kind"] == "OPEN":
            pending.append((index, lower, upper, depth))
    if len(seen) != len(nodes):
        raise ValueError("accepted seed has unreachable nodes")
    return deque(sorted(pending, key=lambda row: row[0]))


def main():
    parser = argparse.ArgumentParser()
    for name in ("source", "source-replay", "current-audit", "current-digest-recheck", "output"):
        parser.add_argument("--" + name, type=Path, required=True)
    parser.add_argument("--source-index", type=int, required=True)
    parser.add_argument("--checks", type=int, default=255)
    parser.add_argument("--maximum-depth", type=int, default=8)
    parser.add_argument("--try-local", action="store_true")
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    if args.checks <= 0 or args.maximum_depth < 0:
        raise ValueError("seeded continuation needs finite explicit refinement limits")
    acceptance, values, pending, inventory, paid = source.gate(
        args.source, args.source_replay, args.current_audit, args.current_digest_recheck
    )
    original, kernel, arcs = values[3], values[5], values[6]
    row = next((row for row in pending if row["index"] == args.source_index), None)
    if row is None:
        raise ValueError("seeded continuation requested an already paid or nonexistent current root")
    seed_path = args.source / "PROPOSAL.json"
    proposal = source.read(seed_path)
    seed = next((item for item in proposal["forests"] if item["source_OPEN_index"] == args.source_index), None)
    if seed is None or seed["actual_source_closed_box"] != row:
        raise ValueError("accepted seed is not the full exact current retained source root")
    nodes = deepcopy(seed["nodes"])
    initial, retained, _ = forest.replay(original, kernel, arcs, row, nodes)
    if initial["source_candidate_root_fully_lower_bounded"]:
        raise ValueError("seeded continuation would pay a previously completed whole root")
    queue = open_queue(original, row, nodes)
    if len(queue) != len(retained):
        raise ValueError("seeded continuation lost an actual accepted OPEN leaf")
    inventory.extend((seed_path, Path(__file__), Path(forest.__file__)))
    inventory.extend(Path(__file__).with_name(name) for name in (
        "propose_common_grid_candidate_curvature.py", "propose_candidate_curvature_energy.py",
        "propose_quadratic_energy_minorant.py", "propose_quadratic_secant_refinement.py",
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
        certificate, result, _ = refine(
            kernel, original["matrix"],
            {"lower": list(map(str, lower)), "upper": list(map(str, upper))},
            angles, original["radius"], arcs
        )
        if result["radius_at_most_Rstar_whole_box_excluded"]:
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
    for index, old_node in enumerate(seed["nodes"]):
        if old_node["kind"] != "OPEN" and nodes[index] != old_node:
            raise ValueError("seeded continuation changed a prior paid leaf or accepted closed split")
    exact, remaining, _ = forest.replay(original, kernel, arcs, row, nodes)
    for text, digest in hashes.items():
        if source.sha(text) != digest:
            raise ValueError("seeded continuation source changed during discovery: " + text)
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
        "already_paid_current_continuation_indices": [row["source_OPEN_index"] for row in paid],
        "accepted_seed_proposal_sha256": source.sha(seed_path),
        "accepted_seed_exact_result": initial,
        "old_paid_leaves_and_closed_splits_retained_identically": True,
        "forests": [{
            "source_OPEN_index": row["index"], "actual_source_closed_box": row,
            "nodes": nodes, "discovery_exact_result": exact,
            "all_unvisited_OPEN_and_shared_boundaries_retained": True,
        }],
        "source_roots_attempted": 1,
        "proposed_complete_lower_bounded_source_roots": int(exact["source_candidate_root_fully_lower_bounded"]),
        "new_leaf_checks": checks, "remaining_explicit_closed_OPEN_leaves": len(remaining),
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
