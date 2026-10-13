"""Unaccepted box-specific quadratic kernels, retaining every earlier proposal."""

import argparse
import json
from pathlib import Path
from fractions import Fraction as F

import numpy as np

import probe_free_angle_candidate_rods as joint_module
from probe_retained_joint_force import RetainingJointSolver
from propose_quadratic_energy_minorant import make_kernel, payment
from n26_force import load_trig
from verify_selected_type_trees import bound, read
from verify_terminal_catalog import sha


def main():
    parser = argparse.ArgumentParser()
    for key in ("registry", "registry-replay", "seed", "kernels", "output", "kernels-output"):
        parser.add_argument("--" + key, type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists() or args.kernels_output.exists():
        raise FileExistsError("fresh box-specific quadratic paths required")
    accepted, _ = bound(args.registry)
    if read(args.registry_replay) != accepted:
        raise ValueError("fresh quadratic source has no matching actual replay")
    seed, kernels = read(args.seed), read(args.kernels)
    if (seed["registry_acceptance_sha256"] != sha(args.registry / "VERIFIED.json")
            or seed["kernels_sha256"] != sha(args.kernels)):
        raise ValueError("fresh quadratic box source changed")
    domains = {row["group_index"]: row["matrix"] for row in read(args.registry / "DOMAINS.json")}
    pending = {group["group_index"]: {row["index"]: row for row in group["closed_OPEN_boxes"]}
               for group in read(args.registry / "PENDING-TYPES.json")}
    specs = {row["group_index"]: row["spec"] for row in read(args.registry / "PENDING-TYPES.json")}
    radius, arcs = F(accepted["radius_upper"]), load_trig(args.registry)[0]
    proposals, numerical, solvers, paid = [], [], {}, 0
    for previous in seed["proposals"]:
        if previous["discovery_exact_result"]["radius_at_most_Rstar_whole_box_excluded"]:
            proposals.append(previous)
            paid += 1
            continue
        index, source_index = previous["group_index"], previous["source_OPEN_index"]
        box, matrix = pending[index][source_index], domains[index]
        solver = solvers.setdefault(index, RetainingJointSolver(specs[index]))
        captured, original = [], joint_module.minimize

        def capture(*call_args, **kwargs):
            result = original(*call_args, **kwargs)
            captured.append(result)
            return result

        joint_module.minimize = capture
        try:
            value = solver.solve_retained(list(map(F, box["lower"])), list(map(F, box["upper"])), matrix, radius)
        finally:
            joint_module.minimize = original
        result = captured[-1]
        points = np.vstack((np.c_[np.cos(2 * np.pi * np.r_[0., value["joint_angles"]]),
                                       np.sin(2 * np.pi * np.r_[0., value["joint_angles"]])],
                            value["joint_center_coordinates"], value["joint_internal_witness_coordinates"]))
        ds = points[solver.E[:, 0]] - points[solver.E[:, 1]]
        lengths = np.linalg.norm(ds, axis=1)
        weights = np.maximum(result.multipliers[:len(solver.edges)] / np.maximum(lengths, 1e-15), 1e-8)
        certificate, kernel = make_kernel(specs[index], weights)
        kernel_index = len(kernels)
        kernels.append({"group_index": index, "certificate": certificate})
        cert, check = payment(kernel, matrix, box, value["joint_angles"], radius, arcs)
        item = {"group_index": index, "source_OPEN_index": source_index, "kernel_index": kernel_index,
                "certificate": cert, "discovery_exact_result": check}
        if F(check["minimum_strict_energy_margin"]) > F(previous["discovery_exact_result"]["minimum_strict_energy_margin"]):
            proposals.append(item)
        else:
            proposals.append(previous)
        best = proposals[-1]["discovery_exact_result"]
        if best["radius_at_most_Rstar_whole_box_excluded"]:
            paid += 1
        numerical.append({"group_index": index, "source_OPEN_index": source_index,
                          "floating_joint_radius": value["floating_joint_radius"],
                          "floating_success": value["floating_success"],
                          "all_numerical_objectives_are_not_lower_bounds": True})
        print(json.dumps({"verified": False, "group_index": index, "OPEN_index": source_index,
                          "strict_whole_box_energy_proposed": best["radius_at_most_Rstar_whole_box_excluded"],
                          "best_exact_energy_margin_for_discovery": float(F(best["minimum_strict_energy_margin"]))}),
              flush=True)
    args.kernels_output.write_text(json.dumps(kernels, separators=(",", ":")) + "\n", encoding="utf-8")
    args.output.write_text(json.dumps({
        **{key: value for key, value in seed.items() if key not in
           ("proposals", "strict_whole_box_proposals", "kernels_sha256")},
        "proposals": proposals, "kernels_sha256": sha(args.kernels_output),
        "strict_whole_box_proposals": paid, "numerical_discovery": numerical,
        "seed_sha256": sha(args.seed), "all_previous_valid_proposals_retained": True,
        "independent_standalone_acceptance_still_required": True},
        separators=(",", ":")) + "\n", encoding="utf-8")
    print(json.dumps({"verified": False, "boxes": len(proposals), "strict_whole_box_proposals": paid}), flush=True)


if __name__ == "__main__":
    main()
