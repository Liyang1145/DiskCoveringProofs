"""Unaccepted fresh-flow/energy closed forests for the last hard canonical type."""

import argparse
from collections import deque
from fractions import Fraction as F
import json
from pathlib import Path

import numpy as np

import probe_free_angle_candidate_rods as joint_module
from probe_retained_joint_force import RetainingJointSolver
from propose_quadratic_energy_minorant import make_kernel, payment
from propose_quadratic_secant_refinement import refine
from n26_force import load_trig
from n26_sharp_radius_constraints import tighten
import n26_correlated_arc_force as force
from verify_selected_type_trees import bound, read
from verify_terminal_catalog import sha


def main():
    parser = argparse.ArgumentParser()
    for key in ("source", "source-replay", "registry", "output", "kernels-output"):
        parser.add_argument("--" + key, type=Path, required=True)
    parser.add_argument("--group", type=int, default=38)
    parser.add_argument("--source-OPEN", type=int, default=139)
    parser.add_argument("--checks", type=int, default=80)
    parser.add_argument("--branch-depth", type=int, default=10)
    args = parser.parse_args()
    if args.output.exists() or args.kernels_output.exists():
        raise FileExistsError("fresh hybrid residual paths required")
    accepted, _ = bound(args.source)
    registry, _ = bound(args.registry)
    if (read(args.source_replay) != accepted
            or accepted["source_acceptance_sha256"] != sha(args.registry / "VERIFIED.json")):
        raise ValueError("hybrid residual source is not the actual matched current overlay")
    row = next(row for row in read(args.source / "PENDING-TYPES.json") if row["group_index"] == args.group)
    box = next(box for box in row["closed_OPEN_boxes"] if box["index"] == args.source_OPEN)
    matrix = next(row["matrix"] for row in read(args.registry / "DOMAINS.json") if row["group_index"] == args.group)
    spec, radius, arcs = row["spec"], F(accepted["radius_upper"]), load_trig(args.registry)[0]
    solver, nodes, kernels, diagnostics = RetainingJointSolver(spec), [{"kind": "OPEN"}], [], []
    queue = deque([(0, list(map(F, box["lower"])), list(map(F, box["upper"])), 0)])
    checks, force_paid, energy_paid, splits = 0, 0, 0, 0
    while queue and checks < args.checks:
        index, lower, upper, depth = queue.popleft()
        checks += 1
        contracted = tighten(matrix, lower, upper)
        if contracted is None:
            nodes[index] = {"kind": "EMPTY"}
            continue
        lower, upper = contracted
        captured, original = [], joint_module.minimize

        def capture(*call_args, **kwargs):
            result = original(*call_args, **kwargs)
            captured.append(result)
            return result

        joint_module.minimize = capture
        try:
            value = solver.solve_retained(lower, upper, matrix, radius)
        finally:
            joint_module.minimize = original
        cert = value["stationary_flow_candidate_retained_even_if_unpaid"]
        if cert is not None:
            check = force.force_check(spec, lower, upper, matrix, cert, arcs)
            if F(check["required_radius_lower"]) > radius:
                nodes[index] = {"kind": "CORRELATED_FORCE", "certificate": cert}
                force_paid += 1
                continue
        optimized = captured[-1]
        turns = np.r_[0., value["joint_angles"]]
        points = np.vstack((np.c_[np.cos(2 * np.pi * turns), np.sin(2 * np.pi * turns)],
                            value["joint_center_coordinates"], value["joint_internal_witness_coordinates"]))
        ds = points[solver.E[:, 0]] - points[solver.E[:, 1]]
        lengths = np.linalg.norm(ds, axis=1)
        weights = np.maximum(optimized.multipliers[:len(solver.edges)] / np.maximum(lengths, 1e-15), 1e-8)
        kernel_certificate, kernel = make_kernel(spec, weights)
        ki = len(kernels)
        kernels.append({"group_index": args.group, "certificate": kernel_certificate})
        current_box = {"lower": list(map(str, lower)), "upper": list(map(str, upper))}
        scalar, scalar_check = payment(kernel, matrix, current_box, value["joint_angles"], radius, arcs)
        improved, improved_check, strategy = refine(kernel, matrix, current_box, scalar, radius, arcs)
        if F(improved_check["minimum_strict_energy_margin"]) < F(scalar_check["minimum_strict_energy_margin"]):
            improved, improved_check, strategy = scalar, scalar_check, "scalar"
        if improved_check["radius_at_most_Rstar_whole_box_excluded"]:
            nodes[index] = {"kind": "QUADRATIC_ENERGY", "kernel_index": ki, "certificate": improved}
            energy_paid += 1
        elif depth < args.branch_depth:
            diagonal = list(map(F, improved["eta"])) if isinstance(improved["eta"], list) else [
                F(improved["eta"])] * len(lower)
            axis = max(range(len(lower)), key=lambda i:
                       (upper[i] - lower[i])**2 * (diagonal[i] + F(1, 10**12)))
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
        diagnostics.append({"node_index": index, "floating_joint_radius_not_a_lower_bound": value["floating_joint_radius"],
                            "exact_whole_box_energy_margin_for_discovery":
                                improved_check["minimum_strict_energy_margin"], "strategy": strategy})
        if checks % 5 == 0:
            print(json.dumps({"verified": False, "checks": checks, "nodes": len(nodes),
                              "force_proposals": force_paid, "energy_proposals": energy_paid,
                              "complete_closed_splits": splits,
                              "OPEN": sum(node["kind"] == "OPEN" for node in nodes)}), flush=True)
    args.kernels_output.write_text(json.dumps(kernels, separators=(",", ":")) + "\n", encoding="utf-8")
    args.output.write_text(json.dumps({
        "schema": "N26-unaccepted-hybrid-force-quadratic-residual-forest-v1",
        "verified": False, "radius_scope": accepted["radius_scope"], "group_index": args.group,
        "spec": spec, "source_OPEN_index": args.source_OPEN, "source_closed_OPEN_box": box,
        "source_acceptance_sha256": sha(args.source / "VERIFIED.json"),
        "source_registry_acceptance_sha256": sha(args.registry / "VERIFIED.json"),
        "kernels_sha256": sha(args.kernels_output), "nodes": nodes, "diagnostics": diagnostics,
        "all_unvisited_OPEN_and_complete_closed_halves_retained": True,
        "independent_hybrid_forest_checker_and_full_source_acceptance_still_required": True,
        "global_optimality_proved": False}, separators=(",", ":")) + "\n", encoding="utf-8")
    print(json.dumps({"verified": False, "checks": checks, "nodes": len(nodes),
                      "proposed_closed": not any(node["kind"] == "OPEN" for node in nodes)}), flush=True)


if __name__ == "__main__":
    main()
