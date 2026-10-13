"""Unaccepted closed-half ENERGY/LOCAL forests on actual current candidate roots."""

import argparse
from collections import deque
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_candidate_energy_local_forest as forest
from n26_sharp_radius_constraints import tighten
from propose_quadratic_energy_minorant import rational_reference
from propose_quadratic_secant_refinement import refine
import verify_candidate_curvature_overlay as source


def main():
    parser = argparse.ArgumentParser()
    for name in ("source", "source-replay", "output"):
        parser.add_argument("--" + name, type=Path, required=True)
    parser.add_argument("--only-indices", type=int, nargs="+")
    parser.add_argument("--checks-per-root", type=int, default=63)
    parser.add_argument("--branch-depth", type=int, default=6)
    parser.add_argument("--try-local", action="store_true")
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    accepted, inventory = source.bound(args.source)
    if (source.read(args.source_replay) != accepted
            or accepted["schema"] != "N26-accepted-original-candidate-curvature-energy-overlay-v1"
            or source.sha(source.__file__) != accepted["files"]["verify_candidate_curvature_overlay.py"]):
        raise ValueError("candidate forest discovery lacks its actual current curvature source")
    print("Reconstructing the actual current candidate roots, prior payments and original frame.", flush=True)
    values = source.input_gate(args.source)
    paid, pending = source.derive(values)
    if (paid != source.read(args.source / "LOWER-LEDGER.json")
            or pending != source.read(args.source / "PENDING-ANGLES.json")
            or len(pending) != accepted["unresolved_closed_angle_boxes"]):
        raise ValueError("candidate forest discovery substituted the actual remaining root list")
    original, kernel, arcs = values[3], values[5], values[6]
    matrix, radius = original["matrix"], original["radius"]
    inventory.extend(values[-1])
    hashes = {linux(path): source.sha(path) for path in inventory}
    records = {row["source_OPEN_index"]: row for row in values[7]["proposals"]}
    chosen = [row for row in pending if args.only_indices is None or row["index"] in args.only_indices]
    if args.only_indices is not None and {row["index"] for row in chosen} != set(args.only_indices):
        raise ValueError("candidate forest requested an already paid or nonexistent source root")
    forests = []
    for row in chosen:
        seed = records[row["index"]]["certificate"]
        nodes = [{"kind": "OPEN"}]
        queue = deque([(0, list(map(F, row["sharp_lower"])), list(map(F, row["sharp_upper"])), 0)])
        checks, energies, locals_paid, empty, splits = 0, 0, 0, 0, 0
        while queue and checks < args.checks_per_root:
            index, lower, upper, depth = queue.popleft()
            checks += 1
            box = tighten(matrix, lower, upper)
            if box is None:
                nodes[index] = {"kind": "EMPTY"}
                empty += 1
                continue
            lower, upper = box
            if args.try_local:
                try:
                    forest.local_proof(original, lower, upper)
                except ValueError:
                    pass
                else:
                    nodes[index] = {"kind": "LOCAL"}
                    locals_paid += 1
                    continue
            previous = deepcopy(seed)
            previous["reference_turns"] = rational_reference(list(map(F, seed["reference_turns"])),
                                                             lower, upper, matrix)
            current_box = {"lower": list(map(str, lower)), "upper": list(map(str, upper))}
            certificate, check, _ = refine(kernel, matrix, current_box, previous, radius, arcs)
            if check["radius_at_most_Rstar_whole_box_excluded"]:
                nodes[index] = {"kind": "ENERGY", "certificate": certificate}
                energies += 1
            elif depth < args.branch_depth:
                eta = list(map(F, certificate["eta"])) if isinstance(certificate["eta"], list) else [
                    F(certificate["eta"])] * len(lower)
                axes = [axis for axis in range(len(lower)) if lower[axis] < upper[axis]]
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
                    splits += 1
            if checks % 8 == 0:
                print(json.dumps({"verified": False, "source_index": row["index"], "checks": checks,
                                  "ENERGY": energies, "LOCAL": locals_paid, "EMPTY": empty, "SPLIT": splits,
                                  "OPEN": sum(node["kind"] == "OPEN" for node in nodes)}), flush=True)
        result, boxes, ledger = forest.replay(original, kernel, arcs, row, nodes)
        forests.append({"source_OPEN_index": row["index"], "actual_source_closed_box": row,
                        "nodes": nodes, "discovery_exact_result": result,
                        "all_unvisited_OPEN_and_shared_boundaries_retained": True})
        print(json.dumps({"verified": False, "source_index": row["index"], **result}, indent=2), flush=True)
    for text, digest in hashes.items():
        if source.sha(source.local_path(text)) != digest:
            raise ValueError("candidate forest source bytes changed during discovery")
    report = {"schema": "N26-unaccepted-original-candidate-energy-LOCAL-closed-forests-v1",
              "verified": False, "radius_scope": "same-root-Rstar",
              "source": linux(args.source), "source_acceptance_sha256": source.sha(args.source / "VERIFIED.json"),
              "source_pending_angles_sha256": source.sha(args.source / "PENDING-ANGLES.json"),
              "forests": forests,
              "proposed_complete_lower_bounded_source_roots": sum(
                  item["discovery_exact_result"]["source_candidate_root_fully_lower_bounded"] for item in forests),
              "source_roots_attempted": len(forests),
              "current_candidate_source_roots_removed_by_discovery": 0,
              "original_52_coordinate_local_allowance_unchanged": "7/800000",
              "independent_current_source_and_complete_forest_acceptance_still_required": True,
              "global_lower_bound_proved": False, "global_optimality_proved": False}
    args.output.write_text(json.dumps(report, separators=(",", ":")) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in report.items() if key != "forests"}, indent=2), flush=True)


if __name__ == "__main__":
    main()
