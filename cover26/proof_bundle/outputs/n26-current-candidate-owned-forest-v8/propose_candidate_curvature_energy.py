"""Unaccepted curvature/dual energy discovery on actual retained candidate boxes."""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

import numpy as np
from scipy.optimize import minimize

from audit_prefix_partition import linux
import n26_candidate_curvature_energy as candidate
from n26_sharp_radius_constraints import SCALE
from propose_quadratic_energy_minorant import payment, rational_reference
from propose_quadratic_secant_refinement import refine
import verify_dirichlet_candidate_overlay as source


def stationary(kernel, matrix, lower, upper, root_turns):
    lo, hi = list(map(F, lower)), list(map(F, upper))
    reference = rational_reference(root_turns, lo, hi, matrix)
    x0 = np.array([float(F(x)) for x in reference])
    weights = np.array([float(F(w, kernel["energy_denominator"])) for _, _, w in kernel["pairs"]])
    left, right = np.array([(i, j) for i, j, _ in kernel["pairs"]]).T
    rows, rhs = [], []
    for i in range(16):
        for j in range(16):
            if i == j:
                continue
            row = np.zeros(15)
            if i:
                row[i - 1] -= 1
            if j:
                row[j - 1] += 1
            rows.append(row)
            rhs.append(float(F(matrix[i][j], SCALE)))
    rows, rhs = np.array(rows), np.array(rhs)

    def energy_gradient(x):
        turns = np.r_[0., x]
        delta = 2 * np.pi * (turns[right] - turns[left])
        energy = 2 * np.dot(weights, 1 - np.cos(delta))
        gradient = np.zeros(16)
        np.add.at(gradient, left, -4 * np.pi * weights * np.sin(delta))
        np.add.at(gradient, right, 4 * np.pi * weights * np.sin(delta))
        return float(energy), gradient[1:]

    optimized = minimize(lambda x: energy_gradient(x)[0], x0, jac=lambda x: energy_gradient(x)[1],
                         bounds=[(float(a), float(b)) for a, b in zip(lo, hi)],
                         constraints={"type": "ineq", "fun": lambda x: rhs - rows @ x,
                                      "jac": lambda x: -rows},
                         method="SLSQP", options={"ftol": 1e-13, "maxiter": 160, "disp": False})
    return optimized.x, {"floating_stationary_success": bool(optimized.success),
                         "floating_stationary_energy": float(optimized.fun)}


def main():
    parser = argparse.ArgumentParser()
    for name in ("source", "source-replay", "output"):
        parser.add_argument("--" + name, type=Path, required=True)
    parser.add_argument("--limit", type=int, default=76)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    accepted, inventory = source.leaf.bound(args.source)
    if (source.read(args.source_replay) != accepted or accepted["radius_scope"] != "same-root-Rstar"
            or source.sha(source.__file__) != accepted["files"]["verify_dirichlet_candidate_overlay.py"]):
        raise ValueError("candidate energy discovery lacks the actual current Dirichlet published replay")
    print("Reconstructing the actual candidate tree and all prior Dirichlet payments.", flush=True)
    values = source.source_gate(args.source)
    _, _, original, _, old_pending, _, old_discovery, old_kernel, arcs, paths = values
    prior_payments, pending = source.derive(old_pending, old_discovery["proposed_paid_OPEN_indices"],
                                            old_kernel, original["radius"], arcs)
    if (pending != source.read(args.source / "PENDING-ANGLES.json")
            or prior_payments != source.read(args.source / "LOWER-LEDGER.json")
            or len(pending) != accepted["unresolved_closed_angle_boxes"]):
        raise ValueError("candidate energy discovery changed the actual remaining closed boxes")
    inventory.extend(paths)
    kernel = candidate.kernel_gate(original["reference"], source.read(args.source / "DIRICHLET-KERNEL.json"))
    identity = source.identity_control(kernel)
    radius, matrix = original["radius"], original["matrix"]
    root_turns = [float((F(a) + F(b)) / 2) for a, b in original["cap"]["known_candidate_tiny_angle_cells"]]
    pending.sort(key=lambda row: max(F(b) - F(a) for a, b in zip(row["sharp_lower"], row["sharp_upper"])))
    proposals = []
    for row in pending[:args.limit]:
        box = {"lower": row["sharp_lower"], "upper": row["sharp_upper"]}
        angles, numerical = stationary(kernel, matrix, box["lower"], box["upper"], root_turns)
        try:
            certificate, check = payment(kernel, matrix, box, angles, radius, arcs)
            improved, improved_check, strategy = refine(kernel, matrix, box, certificate, radius, arcs)
            if F(improved_check["minimum_strict_energy_margin"]) > F(check["minimum_strict_energy_margin"]):
                certificate, check = improved, improved_check
            checked = candidate.bound(kernel, matrix, box["lower"], box["upper"], certificate, radius, arcs)
            record = {"source_OPEN_index": row["index"], "source_closed_box": row,
                      "certificate": certificate, "discovery_exact_result": checked,
                      "proposed_strict_candidate_energy_payment": checked[
                          "candidate_same_root_whole_closed_box_excluded"], **numerical}
        except ValueError as error:
            record = {"source_OPEN_index": row["index"], "source_closed_box": row,
                      "proposed_strict_candidate_energy_payment": False,
                      "exact_proposal_failure": str(error), **numerical}
        proposals.append(record)
        print(json.dumps({"verified": False, "checked": len(proposals), "index": row["index"],
                          "strict_candidate_box_proposed": record["proposed_strict_candidate_energy_payment"],
                          "exact_energy_margin_for_discovery": float(F(record["discovery_exact_result"][
                              "minimum_strict_energy_margin"])) if "discovery_exact_result" in record else None}),
              flush=True)
    hashes = {linux(path): source.sha(path) for path in inventory}
    for text, digest in hashes.items():
        if source.sha(source.leaf.local_path(text)) != digest:
            raise ValueError("candidate energy source changed during discovery")
    report = {"schema": "N26-unaccepted-original-candidate-curvature-energy-overlay-v1",
              "verified": False, "radius_scope": "same-root-Rstar",
              "source": linux(args.source), "source_acceptance_sha256": source.sha(args.source / "VERIFIED.json"),
              "source_pending_angles_sha256": source.sha(args.source / "PENDING-ANGLES.json"),
              "original_Dirichlet_kernel_sha256": source.sha(args.source / "DIRICHLET-KERNEL.json"),
              "original_92_rod_identity_control": identity,
              "source_actual_remaining_closed_boxes": len(pending),
              "proposals": proposals,
              "proposed_strict_whole_candidate_boxes": sum(
                  row["proposed_strict_candidate_energy_payment"] for row in proposals),
              "current_candidate_boxes_removed_by_discovery": 0,
              "original_52_coordinate_local_allowance_unchanged": "7/800000",
              "independent_current_semantic_acceptance_still_required": True,
              "global_lower_bound_proved": False, "global_optimality_proved": False}
    args.output.write_text(json.dumps(report, separators=(",", ":")) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in report.items() if key != "proposals"}, indent=2), flush=True)


if __name__ == "__main__":
    main()
