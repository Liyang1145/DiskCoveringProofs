"""Standalone-stage DATA-only B17 present-prefix stress/whole-box exploration.

Reconstruct actual source rows and present rods, not complete-type padding.
No source frontier, native record, accepted history or current proof is edited.
"""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

import numpy as np

from audit_prefix_origin import OriginReference
from audit_prefix_partition import linux
import audit_conditional_stage_acceptance_contract as contract
from n26_force import CAPS, D, load_trig
import n26_partial_prefix_quadratic_kernel as partial
import n26_sharp_partial_domains as independent
import n26_sharp_radius_constraints as constraints
import probe_free_angle_candidate_rods as joint
import probe_partial_prefix_energy as kernel_producer
from probe_retained_joint_force import RetainingJointSolver
import propose_partial_stationary_energy as stationary
from propose_quadratic_energy_minorant import payment
from propose_quadratic_secant_refinement import refine
import verify_conditional_force_stage as binding


SCHEMA = "N26-unaccepted-current-standalone-stage-B17-present-rod-energy-diagnosis-v1"


def main():
    parser = argparse.ArgumentParser()
    for name in ("stage", "stage-replay", "caps", "report"):
        parser.add_argument("--"+name, type=Path, required=True)
    parser.add_argument("--checks", type=int, default=2)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    if not 1 <= args.checks <= 4:
        raise ValueError("B17 small present-prefix DATA probe limit is invalid")
    accepted = binding.read(args.stage / "VERIFIED.json")
    manifest = binding.read(args.stage / "MANIFEST.json")
    checker = contract.gate(accepted, manifest)
    source_digest = binding.sha(args.stage / "VERIFIED.json")
    if (binding.sha(args.stage / checker) != accepted["executed_checker_sha256"]
            or binding.read(args.stage_replay) != accepted
            or binding.sha(args.stage_replay) != source_digest
            or accepted["files"]["FRONTIER.json"] != binding.sha(args.stage / "FRONTIER.json")):
        raise ValueError("B17 DATA probe changed actual standalone acceptance/replay or source root table")
    cap_acceptance = binding.read(args.caps / "VERIFIED.json")
    cap_certificate = binding.read(args.caps / "CERTIFICATE.json")
    cap_digest, frontier_digest = binding.sha(args.caps / "VERIFIED.json"), binding.sha(args.stage / "FRONTIER.json")
    if (cap_acceptance["verified"] is not True
            or cap_acceptance["files"]["CERTIFICATE.json"] != binding.sha(args.caps / "CERTIFICATE.json")):
        raise ValueError("B17 DATA probe changed accepted sharp-radius chord-cap DATA")
    frontier = binding.read(args.stage / "FRONTIER.json")
    radius, arcs = F(accepted["radius_upper"]), load_trig(args.stage)[0]
    caps, _ = constraints.cap_gate(radius, cap_certificate, arcs)
    ref = OriginReference(26, 17, "dfs", caps=CAPS, scale=D)
    rows = sorted(
        ((index, row) for index, row in enumerate(frontier["pending_states"])
         if row["B"] == 17 and not row["terminal"] and row["child_count"] > 0),
        key=lambda item: (-len(item[1]["faces"]), -item[1]["next"],
                          item[1]["child_count"], item[1]["prefix"]),
    )
    selected, seen = [], set()
    for index, row in rows:
        key = row["next"], tuple(row["faces"])
        if key in seen:
            continue
        seen.add(key)
        selected.append((index, row))
        if len(selected) >= args.checks:
            break
    results = []
    for index, row in selected:
        prefix = tuple(row["prefix"])
        state = ref.resolve(prefix)
        if {"B": 17, **ref.entry(prefix, state, ref.children(state))} != row:
            raise ValueError("actual B17 DATA row failed complete independent prefix reconstruction")
        spec = {"N": 26, "B": 17, "next": row["next"], "faces": row["faces"]}
        matrix, derivation = constraints.constraint_matrix(spec, caps)
        other, _ = independent.matrix(spec, caps)
        if matrix != other:
            raise ValueError("B17 present-prefix independent necessary angular domains disagree")
        record = {
            "actual_source_index_DATA": index, "actual_source_row": row, "spec": spec,
            "sharp_domain_empty": matrix is None, "partial_energy_whole_root_proposed": False,
        }
        if matrix is None:
            record["empty_domain_derivation"] = derivation
            results.append(record)
            continue
        lower = [F(-matrix[i][0], constraints.SCALE) for i in range(1, 17)]
        upper = [F(matrix[0][i], constraints.SCALE) for i in range(1, 17)]
        captured, old_minimize = [], joint.minimize

        def capture(*call_args, **kwargs):
            result = old_minimize(*call_args, **kwargs)
            captured.append(result)
            return result

        joint.minimize = capture
        try:
            numerical = RetainingJointSolver(spec).solve_retained(lower, upper, matrix, radius)
        finally:
            joint.minimize = old_minimize
        record["numerical_suggestion_NOT_proof"] = numerical
        if not captured or not hasattr(captured[-1], "multipliers"):
            record["no_stress_multipliers_available_NOT_a_geometric_result"] = True
            results.append(record)
            continue
        vertices, edges = partial.graph(spec)
        points = np.vstack((
            np.c_[np.cos(2*np.pi*np.r_[0., numerical["joint_angles"]]),
                  np.sin(2*np.pi*np.r_[0., numerical["joint_angles"]])],
            numerical["joint_center_coordinates"], numerical["joint_internal_witness_coordinates"],
        ))
        distances = np.linalg.norm(points[np.array(edges)[:, 0]]-points[np.array(edges)[:, 1]], axis=1)
        weights = np.maximum(captured[-1].multipliers[:len(edges)]/np.maximum(distances, 1e-15), 1e-7)
        kernel_certificate, kernel = kernel_producer.make_kernel(spec, weights)
        record.update(
            actual_present_rod_vertices=vertices, actual_present_rod_edges=len(edges),
            exact_partial_positive_kernel=kernel_certificate,
            exact_partial_identity_controls=partial.identity_control(kernel),
            exact_necessary_difference_matrix=matrix,
            actual_closed_lower=list(map(str, lower)), actual_closed_upper=list(map(str, upper)),
        )
        box = {"lower": list(map(str, lower)), "upper": list(map(str, upper))}
        trials = []
        for label, angles in (
            ("retained-joint-angle-reference", numerical["joint_angles"]),
            ("fresh-Schur-stationary-reference", stationary.stationary(
                kernel, matrix, lower, upper, numerical["joint_angles"])[0]),
        ):
            try:
                certificate, exact = payment(kernel, matrix, box, angles, radius, arcs)
                improved, improved_result, strategy = refine(
                    kernel, matrix, box, certificate, radius, arcs)
                if F(improved_result["minimum_strict_energy_margin"]) > F(exact["minimum_strict_energy_margin"]):
                    certificate = improved
                result = partial.bound(kernel, matrix, lower, upper, certificate, radius, arcs)
            except ValueError as error:
                trials.append({"strategy": label, "exact_proposal_failure": str(error),
                               "strict_actual_whole_present_prefix_bound": False})
            else:
                strict = result["radius_at_most_Rstar_partial_whole_box_excluded"]
                record["partial_energy_whole_root_proposed"] |= strict
                trials.append({"strategy": label, "certificate": certificate,
                               "exact_arithmetic_result": result,
                               "strict_actual_whole_present_prefix_bound": strict})
        record["whole_closed_domain_trials"] = trials
        results.append(record)
        print(json.dumps({
            "actual_B17_source_index": index, "present_faces": len(row["faces"]),
            "introduced_centers": row["next"], "actual_present_rods": len(edges),
            "floating_joint_radius_NOT_proof": numerical["floating_joint_radius"],
            "strict_whole_prefix_arithmetic_proposed": record["partial_energy_whole_root_proposed"],
            "verified": False, "current_transport_subtrees_removed": 0}), flush=True)
    for path, digest in ((args.stage / "VERIFIED.json", source_digest),
                         (args.stage / "FRONTIER.json", frontier_digest),
                         (args.caps / "VERIFIED.json", cap_digest)):
        if binding.sha(path) != digest:
            raise ValueError("actual standalone-stage or cap DATA changed during B17 probing")
    report = {
        "schema": SCHEMA, "verified": False, "N": 26, "boundary_family_B": 17,
        "source_stage_standalone_DATA_NOT_complete_current_frontier": linux(args.stage),
        "source_standalone_acceptance_sha256": source_digest,
        "source_standalone_actual_replay_sha256": binding.sha(args.stage_replay),
        "source_frontier_DATA_sha256": frontier_digest,
        "sharp_cap_acceptance_DATA_sha256": cap_digest,
        "radius_scope": accepted["radius_scope"], "radius_upper": str(radius),
        "results": results,
        "actual_present_prefix_rows_and_only_present_rods_reconstructed": True,
        "no_unintroduced_centers_future_face_witnesses_or_complete_type_padding": True,
        "new_stress_weights_and_numerical_optimizer_NOT_proofs": True,
        "proposed_strict_whole_prefix_arithmetic_trials": sum(
            item["partial_energy_whole_root_proposed"] for item in results),
        "source_frontier_and_old_proofs_UNMODIFIED": True,
        "complete_latest_current_model_source_history_and_geometry_transfer_NOT_performed": True,
        "new_geometric_payments": 0, "current_transport_subtrees_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
        "executed_probe_sha256": binding.sha(__file__),
        "modules": {linux(Path(module.__file__)): binding.sha(module.__file__)
                    for module in (partial, constraints, independent, kernel_producer, stationary, joint)},
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({"actual_B17_present_prefix_probe_completed": True, "actual_prefixes": len(results),
                      "strict_whole_prefix_proposals": report["proposed_strict_whole_prefix_arithmetic_trials"],
                      "verified": False, "current_transport_subtrees_removed": 0}), flush=True)


if __name__ == "__main__":
    main()
