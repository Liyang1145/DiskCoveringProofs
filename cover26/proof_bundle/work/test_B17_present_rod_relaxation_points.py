"""Exact point witnesses for the limits of selected PRESENT-rod relaxations.

This is NOT a disk covering, global lower bound, geometric payment or
counterexample to n26 optimality. Missing future faces are not invented.
"""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_origin import OriginReference
from n26_force import CAPS, D, load_trig
import n26_partial_prefix_quadratic_kernel as partial
import n26_sharp_partial_domains as independent
import n26_sharp_radius_constraints as constraints
from propose_quadratic_energy_minorant import rational_reference
import probe_current_B17_present_rod_energy as producer
import verify_conditional_force_stage as binding


SCHEMA = "N26-exact-B17-present-rod-relaxation-point-controls-v1"


def point_check(spec, matrix, lower, upper, certificate, candidate_lower, arcs):
    if (set(certificate) != {"anchor_turns", "free_points", "rod_radius_upper"}
            or type(certificate["rod_radius_upper"]) is not str):
        raise ValueError("partial rod point has unknown or missing exact fields")
    radius = F(certificate["rod_radius_upper"])
    if not 0 < radius < candidate_lower:
        raise ValueError("partial rod witness radius is not strictly below the candidate radius lower endpoint")
    vertices, edges = partial.graph(spec)
    ref = partial.quadratic.reference_gate(certificate["anchor_turns"], lower, upper, matrix)[0]
    free = certificate["free_points"]
    if (not isinstance(free, list) or len(free) != vertices-spec["B"]
            or any(not isinstance(point, list) or len(point) != 2
                   or any(type(value) is not str for value in point) for point in free)):
        raise ValueError("partial rod point changed actual introduced-center/present-witness dimensions")
    free = [[F(value) for value in point] for point in free]
    # Optional stronger control: the actually introduced disk centers are in
    # the unit disk too. This still does not assert any disk covering.
    if any(sum(value**2 for value in point) > 1 for point in free[:spec["next"]]):
        raise ValueError("a proposed introduced-center point lies outside the unit disk")
    anchors = []
    for turn in ref:
        cosine, sine = arcs.sincos_turn(turn)
        anchors.append([
            [F(value, arcs.SCALE) for value in cosine],
            [F(value, arcs.SCALE) for value in sine],
        ])
    points = anchors+[[[value, value] for value in point] for point in free]
    squared, margins = [], []
    for u, v in edges:
        upper_bound = F(0)
        for left, right in zip(points[u], points[v]):
            a, b = left[0]-right[1], left[1]-right[0]
            upper_bound += max(a*a, b*b)
        if upper_bound >= radius**2:
            raise ValueError("an actual present rod does not satisfy the strict exact point radius bound")
        squared.append(str(upper_bound))
        margins.append(radius**2-upper_bound)
    return {
        "actual_present_vertices": vertices, "actual_present_rods": len(edges),
        "all_unit_circle_anchors_and_exact_necessary_difference_constraints_checked": True,
        "all_introduced_centers_checked_inside_unit_disk": spec["next"],
        "all_present_rods_strictly_below_exact_rational_radius": str(radius),
        "candidate_radius_strict_lower_endpoint": str(candidate_lower),
        "actual_present_rod_squared_length_upper_bounds": squared,
        "minimum_strict_present_rod_squared_margin": str(min(margins)),
        "no_future_face_witnesses_or_rods_added": True,
        "is_NOT_a_disk_cover_or_counterexample_to_global_optimality": True,
    }


def main():
    parser = argparse.ArgumentParser()
    for name in ("stage", "caps", "diagnosis", "report"):
        parser.add_argument("--"+name, type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    diagnosis = binding.read(args.diagnosis)
    digest = binding.sha(args.diagnosis)
    accepted = binding.read(args.stage / "VERIFIED.json")
    frontier = binding.read(args.stage / "FRONTIER.json")
    if (diagnosis["schema"] != producer.SCHEMA
            or diagnosis["executed_probe_sha256"] != binding.sha(producer.__file__)
            or diagnosis["source_standalone_acceptance_sha256"] != binding.sha(args.stage / "VERIFIED.json")
            or diagnosis["source_frontier_DATA_sha256"] != binding.sha(args.stage / "FRONTIER.json")
            or diagnosis["sharp_cap_acceptance_DATA_sha256"] != binding.sha(args.caps / "VERIFIED.json")
            or diagnosis["verified"] is not False or diagnosis["current_transport_subtrees_removed"] != 0
            or diagnosis["new_geometric_payments"] != 0
            or accepted["files"]["FRONTIER.json"] != binding.sha(args.stage / "FRONTIER.json")):
        raise ValueError("B17 exact point controls changed actual DATA source, producer or zero-payment scope")
    radius, candidate_lower = F(accepted["radius_upper"]), F(accepted["r_strict_interval"][0])
    arcs = load_trig(args.stage)[0]
    caps, _ = constraints.cap_gate(radius, binding.read(args.caps / "CERTIFICATE.json"), arcs)
    reference = OriginReference(26, 17, "dfs", caps=CAPS, scale=D)
    checked = []
    for item in diagnosis["results"]:
        row = frontier["pending_states"][item["actual_source_index_DATA"]]
        state = reference.resolve(tuple(row["prefix"]))
        if (row != item["actual_source_row"]
                or {"B": 17, **reference.entry(tuple(row["prefix"]), state, reference.children(state))} != row):
            raise ValueError("B17 exact point controls changed the entire actual present-prefix source row")
        spec = {"N": 26, "B": 17, "next": row["next"], "faces": row["faces"]}
        matrix, _ = constraints.constraint_matrix(spec, caps)
        other, _ = independent.matrix(spec, caps)
        if (spec != item["spec"] or matrix is None or matrix != other
                or matrix != item["exact_necessary_difference_matrix"]):
            raise ValueError("B17 exact point controls changed actual present rods or necessary angular domain")
        lower = [F(-matrix[i][0], constraints.SCALE) for i in range(1, 17)]
        upper = [F(matrix[0][i], constraints.SCALE) for i in range(1, 17)]
        numerical = item["numerical_suggestion_NOT_proof"]
        angles = rational_reference(numerical["joint_angles"], lower, upper, matrix)
        raw = numerical["joint_center_coordinates"]+numerical["joint_internal_witness_coordinates"]
        certificate = {
            "anchor_turns": angles,
            "free_points": [[str(F(round(float(value)*10**12), 10**12)) for value in point] for point in raw],
            "rod_radius_upper": "21/100",
        }
        result = point_check(spec, matrix, lower, upper, certificate, candidate_lower, arcs)
        checked.append({
            "actual_source_index_DATA": item["actual_source_index_DATA"],
            "actual_source_row": row, "exact_point_certificate": certificate,
            "exact_partial_rod_point_result": result,
        })
    if not checked:
        raise ValueError("B17 exact point controls have no actual partial-rod witness")
    first, item = checked[0], diagnosis["results"][0]
    spec, matrix = item["spec"], item["exact_necessary_difference_matrix"]
    lower, upper = list(map(F, item["actual_closed_lower"])), list(map(F, item["actual_closed_upper"]))
    rejected = []

    def reject(label, mutation):
        bad = deepcopy(first["exact_point_certificate"])
        mutation(bad)
        try:
            point_check(spec, matrix, lower, upper, bad, candidate_lower, arcs)
        except (ValueError, KeyError, TypeError, IndexError):
            rejected.append(label)
        else:
            raise AssertionError("invalid actual B17 partial-point witness accepted: "+label)

    for label, mutation in (
        ("partial-point-false-small-radius", lambda bad: bad.update(rod_radius_upper="1/100")),
        ("partial-point-radius-not-below-candidate", lambda bad: bad.update(rod_radius_upper="1/4")),
        ("partial-point-negative-radius", lambda bad: bad.update(rod_radius_upper="-1")),
        ("partial-point-missing-present-witness", lambda bad: bad["free_points"].pop()),
        ("partial-point-unpresent-extra-witness", lambda bad: bad["free_points"].append(["0", "0"])),
        ("partial-point-wrong-anchor-dimension", lambda bad: bad["anchor_turns"].pop()),
        ("partial-point-infeasible-anchor-angle", lambda bad: bad["anchor_turns"].__setitem__(0, "100")),
        ("partial-point-center-outside-unit-disk", lambda bad: bad["free_points"].__setitem__(0, ["100", "100"])),
        ("partial-point-future-rod-field-added", lambda bad: bad.update(future_rods=[])),
        ("partial-point-numerical-coordinate-used-as-proof", lambda bad: bad["free_points"][0].__setitem__(0, 0.0)),
    ):
        reject(label, mutation)
    if binding.sha(args.diagnosis) != digest:
        raise ValueError("B17 actual diagnosis changed during exact partial-point controls")
    report = {
        "schema": SCHEMA, "verified": False, "N": 26, "boundary_family_B": 17,
        "diagnosis_sha256": digest, "exact_actual_partial_present_rod_witnesses": checked,
        "all_actual_present_prefix_rows_rods_and_angular_constraints_reconstructed": True,
        "strict_partial_rod_relaxation_radius_below_candidate": "21/100",
        "impossibility_of_a_strict_whole_domain_lower_bound_using_ONLY_these_present_rods_at_Rstar": True,
        "missing_future_face_and_complete_embedding_cover_obligations_remain": True,
        "is_NOT_a_disk_cover_or_counterexample_to_global_optimality": True,
        "actual_partial_point_rejection_controls_passed": rejected,
        "source_frontier_and_all_prior_proofs_UNMODIFIED": True,
        "complete_latest_current_source_history_geometry_transfer_NOT_performed": True,
        "new_geometric_payments": 0, "current_transport_subtrees_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
        "executed_test_sha256": binding.sha(__file__),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({"B17_exact_present_rod_relaxation_controls_completed": True,
                      "actual_partial_point_witnesses": len(checked), "strict_radius": "21/100",
                      "actual_rejections": len(rejected), "NOT_a_disk_cover": True,
                      "verified": False, "current_transport_subtrees_removed": 0}), flush=True)


if __name__ == "__main__":
    main()
