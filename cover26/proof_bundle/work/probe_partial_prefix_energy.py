"""Unaccepted partial-prefix stress/energy discovery on the actual frontier.

No numerical objective, eigenvalue, solver success or discovery boolean
removes a transport subtree. Exact current acceptance is a separate step.
"""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

import numpy as np
from sympy import Matrix

from audit_prefix_origin import OriginReference
from audit_prefix_partition import linux
from n26_force import CAPS, D, load_trig
import n26_partial_prefix_quadratic_kernel as partial
import n26_sharp_partial_domains as independent
import n26_sharp_radius_constraints as constraints
import probe_free_angle_candidate_rods as joint
from probe_retained_joint_force import RetainingJointSolver
from propose_quadratic_energy_minorant import payment
from propose_quadratic_secant_refinement import refine
from verify_conditional_force_stage import bound, read, sha


def make_kernel(spec, raw_weights):
    vertices, edges = partial.graph(spec)
    b, scale = spec["B"], 10**10
    weights = [max(1, round(float(w) * scale)) for w in raw_weights]
    if len(weights) != len(edges):
        raise ValueError("partial discovery weights belong to a different rod graph")
    lap = [[0] * vertices for _ in range(vertices)]
    for (u, v), w in zip(edges, weights):
        lap[u][u] += w
        lap[v][v] += w
        lap[u][v] -= w
        lap[v][u] -= w
    inverse, denominator = Matrix([row[b:] for row in lap[b:]]).to_DM().inv_den()
    nums, den = inverse.to_Matrix().tolist(), int(denominator)
    nums = [[int(x) for x in row] for row in nums]
    if den < 0:
        nums, den = [[-x for x in row] for row in nums], -den
    certificate = {"schema": partial.SCHEMA, "spec": spec, "weight_scale": scale,
                   "weight_numerators": weights, "inverse_denominator": str(den),
                   "inverse_numerators": [[str(x) for x in row] for row in nums]}
    return certificate, partial.kernel_gate(spec, certificate)


def main():
    parser = argparse.ArgumentParser()
    for name in ("stage", "caps", "output", "kernels-output"):
        parser.add_argument("--" + name, type=Path, required=True)
    parser.add_argument("--checks", type=int, default=12)
    args = parser.parse_args()
    if args.output.exists() or args.kernels_output.exists():
        raise FileExistsError("fresh partial energy discovery paths required")
    accepted, _ = bound(args.stage)
    cap_report, _ = bound(args.caps)
    cap, frontier = read(args.caps / "CERTIFICATE.json"), read(args.stage / "FRONTIER.json")
    radius, arcs = F(accepted["radius_upper"]), load_trig(args.stage)[0]
    caps, _ = constraints.cap_gate(radius, cap, arcs)
    if cap_report["verified"] is not True:
        raise ValueError("partial discovery has no accepted sharp cap source")
    refs = {b: OriginReference(26, b, "dfs", caps=CAPS, scale=D) for b in (14, 15, 16, 17)}
    rows = [(index, row) for index, row in enumerate(frontier["pending_states"]) if not row["terminal"]]
    rows.sort(key=lambda item: (-len(item[1]["faces"]), -item[1]["next"],
                               item[1]["child_count"], item[1]["B"], item[1]["prefix"]))
    selected, seen = [], set()
    for index, row in rows:
        key = row["B"], row["next"], tuple(row["faces"])
        if key not in seen:
            seen.add(key)
            selected.append((index, row))
        if len(selected) >= args.checks:
            break
    results, kernels = [], []
    for source_index, row in selected:
        b, prefix = row["B"], tuple(row["prefix"])
        ref = refs[b]
        state = ref.resolve(prefix)
        if {"B": b, **ref.entry(prefix, state, ref.children(state))} != row:
            raise ValueError("partial discovery source does not reconstruct from its actual prefix")
        spec = {"N": 26, "B": b, "next": row["next"], "faces": row["faces"]}
        matrix, derivation = constraints.constraint_matrix(spec, caps)
        alternative, _ = independent.matrix(spec, caps)
        if matrix != alternative:
            raise ValueError("partial necessary angular-domain constructions disagree")
        record = {"source_index": source_index, "B": b, "prefix": list(prefix), "spec": spec,
                  "sharp_domain_empty": matrix is None, "partial_energy_whole_root_proposed": False}
        if matrix is None:
            record["empty_derivation"] = derivation
            results.append(record)
            continue
        lower = [F(-matrix[i][0], constraints.SCALE) for i in range(1, b)]
        upper = [F(matrix[0][i], constraints.SCALE) for i in range(1, b)]
        captured, original = [], joint.minimize

        def capture(*call_args, **kwargs):
            optimized = original(*call_args, **kwargs)
            captured.append(optimized)
            return optimized

        joint.minimize = capture
        try:
            numerical = RetainingJointSolver(spec).solve_retained(lower, upper, matrix, radius)
        finally:
            joint.minimize = original
        record["numerical"] = numerical
        record["floating_joint_radius"] = numerical["floating_joint_radius"]
        optimized = captured[-1]
        if not hasattr(optimized, "multipliers"):
            record["no_stress_multipliers_available"] = True
            results.append(record)
            continue
        points = np.vstack((np.c_[np.cos(2 * np.pi * np.r_[0., numerical["joint_angles"]]),
                                  np.sin(2 * np.pi * np.r_[0., numerical["joint_angles"]])],
                            numerical["joint_center_coordinates"],
                            numerical["joint_internal_witness_coordinates"]))
        vertices, edges = partial.graph(spec)
        distances = np.linalg.norm(points[np.array(edges)[:, 0]] - points[np.array(edges)[:, 1]], axis=1)
        weights = np.maximum(optimized.multipliers[:len(edges)] / np.maximum(distances, 1e-15), 1e-7)
        kernel_certificate, kernel = make_kernel(spec, weights)
        record["kernel_index"] = len(kernels)
        kernels.append({"source_index": source_index, "certificate": kernel_certificate})
        record["partial_identity_controls"] = partial.identity_control(kernel)
        box = {"lower": list(map(str, lower)), "upper": list(map(str, upper))}
        try:
            certificate, exact_result = payment(kernel, matrix, box, numerical["joint_angles"], radius, arcs)
            refined, refined_result, strategy = refine(kernel, matrix, box, certificate, radius, arcs)
            if F(refined_result["minimum_strict_energy_margin"]) > F(exact_result["minimum_strict_energy_margin"]):
                certificate, exact_result = refined, refined_result
                record["curvature_strategy"] = strategy
            checked = partial.bound(kernel, matrix, lower, upper, certificate, radius, arcs)
            record.update({"certificate": certificate, "discovery_exact_result": checked,
                           "partial_energy_whole_root_proposed": checked[
                               "radius_at_most_Rstar_partial_whole_box_excluded"],
                           "exact_energy_margin_for_discovery": float(F(checked["minimum_strict_energy_margin"]))})
        except ValueError as error:
            record["exact_energy_proposal_failure"] = str(error)
        results.append(record)
        print(json.dumps({key: value for key, value in record.items() if key in
                          ("source_index", "B", "floating_joint_radius", "partial_energy_whole_root_proposed",
                           "exact_energy_margin_for_discovery", "exact_energy_proposal_failure")}), flush=True)
    args.kernels_output.write_text(json.dumps(kernels, separators=(",", ":")) + "\n", encoding="utf-8")
    report = {"schema": "N26-unaccepted-current-partial-prefix-energy-discovery-v1",
              "verified": False, "radius_scope": accepted["radius_scope"],
              "source_stage": linux(args.stage), "source_acceptance_sha256": sha(args.stage / "VERIFIED.json"),
              "source_frontier_sha256": sha(args.stage / "FRONTIER.json"),
              "caps": linux(args.caps), "cap_acceptance_sha256": sha(args.caps / "VERIFIED.json"),
              "kernels_sha256": sha(args.kernels_output), "results": results,
              "proposed_strict_whole_root_exclusions": sum(
                  row["partial_energy_whole_root_proposed"] for row in results),
              "proposed_empty_sharp_domains": sum(row["sharp_domain_empty"] for row in results),
              "current_transport_subtrees_removed": 0,
              "standalone_current_source_semantic_transfer_acceptance_still_required": True,
              "global_optimality_proved": False}
    args.output.write_text(json.dumps(report, separators=(",", ":")) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in report.items() if key != "results"}, indent=2), flush=True)


if __name__ == "__main__":
    main()
