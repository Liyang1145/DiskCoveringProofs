"""Unaccepted closed-half forests on the two retained hard-type energy boxes."""

import argparse
from collections import deque
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from n26_force import load_trig
from n26_sharp_radius_constraints import tighten
import n26_quadratic_energy_minorant as energy
from propose_quadratic_energy_minorant import rational_reference
from propose_quadratic_secant_refinement import refine
from verify_selected_type_trees import bound, read
from verify_terminal_catalog import sha


def main():
    parser = argparse.ArgumentParser()
    for key in ("overlay", "overlay-replay", "registry", "output"):
        parser.add_argument("--" + key, type=Path, required=True)
    parser.add_argument("--checks-per-box", type=int, default=80)
    parser.add_argument("--branch-depth", type=int, default=8)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    accepted, _ = bound(args.overlay)
    source, _ = bound(args.registry)
    if (read(args.overlay_replay) != accepted
            or accepted["source_acceptance_sha256"] != sha(args.registry / "VERIFIED.json")
            or sha(energy.__file__) != accepted["files"]["n26_quadratic_energy_minorant.py"]):
        raise ValueError("residual energy discovery changed its actually replayed source")
    proposal = read(args.overlay / "PROPOSAL.json")
    kernels = read(args.overlay / "KERNELS.json")
    paid = {tuple(row) for row in read(args.overlay / "CERTIFICATE.json")["paid_source_OPEN_keys"]}
    pending = {row["group_index"]: {box["index"]: box for box in row["closed_OPEN_boxes"]}
               for row in read(args.overlay / "PENDING-TYPES.json")}
    domains = {row["group_index"]: row["matrix"] for row in read(args.registry / "DOMAINS.json")}
    radius, arcs = F(accepted["radius_upper"]), load_trig(args.registry)[0]
    cache, forests = {}, []
    for item in proposal["proposals"]:
        group, root_index = item["group_index"], item["source_OPEN_index"]
        if (group, root_index) in paid:
            continue
        box = pending[group][root_index]
        ki = item["kernel_index"]
        if ki not in cache:
            cache[ki] = energy.kernel_gate(kernels[ki]["certificate"]["spec"], kernels[ki]["certificate"])
        kernel, matrix = cache[ki], domains[group]
        nodes = [{"kind": "OPEN"}]
        queue = deque([(0, list(map(F, box["lower"])), list(map(F, box["upper"])), 0)])
        checks, count_paid, splits = 0, 0, 0
        while queue and checks < args.checks_per_box:
            index, lower, upper, depth = queue.popleft()
            checks += 1
            contracted = tighten(matrix, lower, upper)
            if contracted is None:
                nodes[index] = {"kind": "EMPTY"}
                continue
            lower, upper = contracted
            reference = rational_reference(list(map(F, item["certificate"]["reference_turns"])),
                                           lower, upper, matrix)
            previous = {**deepcopy(item["certificate"]), "reference_turns": reference}
            current_box = {"lower": list(map(str, lower)), "upper": list(map(str, upper))}
            cert, check, strategy = refine(kernel, matrix, current_box, previous, radius, arcs)
            if check["radius_at_most_Rstar_whole_box_excluded"]:
                nodes[index] = {"kind": "QUADRATIC_ENERGY", "kernel_index": ki, "certificate": cert}
                count_paid += 1
            elif depth < args.branch_depth:
                diagonal = list(map(F, cert["eta"])) if isinstance(cert["eta"], list) else [
                    F(cert["eta"])] * len(lower)
                axis = max(range(len(lower)),
                           key=lambda i: (upper[i] - lower[i])**2 * (diagonal[i] + F(1, 10**12)))
                middle = (lower[axis] + upper[axis]) / 2
                if lower[axis] < middle < upper[axis]:
                    children = [len(nodes), len(nodes) + 1]
                    nodes.extend(({"kind": "OPEN"}, {"kind": "OPEN"}))
                    nodes[index] = {"kind": "SPLIT", "axis": axis, "mid": str(middle), "children": children}
                    lu, rl = list(upper), list(lower)
                    lu[axis], rl[axis] = middle, middle
                    queue.extend(((children[0], list(lower), lu, depth + 1),
                                  (children[1], rl, list(upper), depth + 1)))
                    splits += 1
            if checks % 10 == 0:
                print(json.dumps({"verified": False, "group_index": group, "source_OPEN_index": root_index,
                                  "checks": checks, "strict_energy_leaves_proposed": count_paid,
                                  "complete_closed_splits": splits,
                                  "OPEN": sum(node["kind"] == "OPEN" for node in nodes)}), flush=True)
        forests.append({"group_index": group, "spec": kernel["spec"], "source_OPEN_index": root_index,
                        "source_closed_OPEN_box": box, "nodes": nodes,
                        "checks": checks, "all_unvisited_OPEN_retained": True})
        print(json.dumps({"verified": False, "group_index": group, "source_OPEN_index": root_index,
                          "nodes": len(nodes), "proposed_closed": not any(node["kind"] == "OPEN" for node in nodes)}),
              flush=True)
    args.output.write_text(json.dumps({
        "schema": "N26-unaccepted-current-quadratic-residual-closed-half-forests-v1",
        "verified": False, "radius_scope": accepted["radius_scope"],
        "source_overlay_acceptance_sha256": sha(args.overlay / "VERIFIED.json"),
        "source_registry_acceptance_sha256": sha(args.registry / "VERIFIED.json"),
        "source_kernels_sha256": sha(args.overlay / "KERNELS.json"),
        "forests": forests, "all_source_nodes_paid_boxes_and_closed_halves_preserved": True,
        "independent_forest_BFS_replay_and_acceptance_still_required": True,
        "global_optimality_proved": False}, separators=(",", ":")) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
