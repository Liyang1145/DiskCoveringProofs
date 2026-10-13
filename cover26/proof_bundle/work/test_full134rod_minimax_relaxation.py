"""Independent full134rod exact realization and fresh positive-stress checks."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import probe_full134rod_minimax_relaxation as producer
import verify_conditional_force_stage as binding


SCHEMA = "N26-independent-actual-full134rod-minimax-point-and-stress-controls-v1"
full = producer.full


def point_controls(original, model, leaf, item, radius_lower, arcs):
    turns = list(map(F, item["actual_fixed_feasible_anchor_turns"]))
    free = [list(map(F, point)) for point in item["rational60_free_points_NEW134rod_model"]]
    if len(free) != 60 or any(len(point) != 2 for point in free):
        raise ValueError("independent full134rod point has a wrong60free dimension")
    full.hull.quadratic.reference_gate(turns, leaf["lower"], leaf["upper"], original["matrix"])
    # Independently construct exact interval coordinates without the producer
    # helper or any harmonic model/optimization value.
    x, y = [], []
    for turn in [F(0), *turns]:
        cosine, sine = arcs.sincos_turn(turn)
        x.append([F(value, arcs.SCALE) for value in cosine])
        y.append([F(value, arcs.SCALE) for value in sine])
    for px, py in free:
        x.append([px, px])
        y.append([py, py])
    bounds = []
    for u, v in model["edges"]:
        dx = [left-right for left in x[u] for right in x[v]]
        dy = [left-right for left in y[u] for right in y[v]]
        bounds.append(max(value*value for value in dx)+max(value*value for value in dy))
    result = item["exact_necessary_model_realization_result"]
    radius = F(result["exact_outward_realization_radius"])
    margins = [radius*radius-bound for bound in bounds]
    unit_margins = [F(1)-px*px-py*py for px, py in free]
    below = radius < F(radius_lower) and min(unit_margins) >= 0
    if (radius <= 0 or min(margins) <= 0
            or list(map(str, bounds)) != result["exact_all134rod_distance_upper_bounds"]
            or str(min(margins)) != result["exact_minimum_all134rod_squared_distance_margin"]
            or str(min(unit_margins)) != result["exact_minimum_all60_free_unit_disk_margin"]
            or result["all60_free_centers_and_face_witnesses_inside_unit_disk"] != (min(unit_margins) >= 0)
            or result["exact_radius_margin_below_candidate_Rstar_LOWER"] != str(F(radius_lower)-radius)
            or result["exact_below_Rstar_complete134rod_NECESSARY_model_realization"] != below
            or result["continuous_unit_disk_cover_NOT_proved"] is not True
            or result["embedding_and_topological_cover_constraints_NOT_accepted"] is not True
            or result["not_a_global_optimality_counterexample"] is not True):
        raise ValueError("full134rod independent point/radius/unit-disk/scope reconstruction failed")
    return below


def trial_controls(original, model, item, radius_lower, arcs):
    leaf = item["actual_checked_v7_OPEN_leaf"]
    below = point_controls(original, model, leaf, item, radius_lower, arcs)
    kernel, identity = producer.prior_producer.previous.arithmetic.kernel_controls(
        model, item["NEW_full134rod_stress_kernel_certificate"])
    if identity != item["NEW_full134rod_stress_exact_identity_controls"]:
        raise ValueError("fresh minimax NEW60ground nonharmonic identity failed")
    old_certificate, old_result = item["NEW_stress_old_diagonal_certificate"], item["NEW_stress_old_diagonal_result"]
    if old_certificate is not None:
        trial = {"NEW_full134rod_energy_certificate": old_certificate,
                 "NEW_full134rod_exact_closed_leaf_result": old_result}
        producer.prior_producer.previous.arithmetic.bound_controls(original, kernel, leaf, trial, arcs)
    elif old_result is not None:
        raise ValueError("uncertified old diagonal stress suggestion declared a proof")
    certificate, result = item["NEW_stress_correlated_certificate"], item["NEW_stress_correlated_result"]
    if certificate is not None:
        trial = {"NEW_correlated_quadratic_certificate": certificate,
                 "NEW_correlated_exact_closed_leaf_result": result}
        producer.prior_controls.arithmetic_control(original, kernel, leaf, trial, arcs)
    elif result is not None:
        raise ValueError("uncertified new correlated stress suggestion declared a proof")
    if below and ((result is not None and result["arithmetic_strict_target_test_passed"])
                  or (old_result is not None and old_result["arithmetic_strict_target_test_passed"])):
        raise AssertionError("below-Rstar exact primal realization contradicts a strict whole-leaf energy bound")
    tiny = original["cap"]["known_candidate_tiny_angle_cells"]
    actual = full.direct.bound(
        [a for a, _ in tiny], [b for _, b in tiny], kernel, F(original["radius"])**2, arcs)
    if actual != item["known_feasible_tiny_stress_positive_control"] or actual["radius_conditional_whole_angle_box_excluded"]:
        raise ValueError("fresh full134rod minimax stress tiny positive control failed")
    return below, kernel


def rejections(original, model, item, radius_lower, arcs):
    rejected = []

    def reject(label, mutation):
        bad = deepcopy(item)
        mutation(bad)
        try:
            trial_controls(original, model, bad, radius_lower, arcs)
        except (ValueError, KeyError, TypeError, IndexError):
            rejected.append(label)
        else:
            raise AssertionError("invalid actual full134rod minimax point/stress accepted: "+label)

    for label, mutation in (
        ("minimax-full134rod-old46free-points-substituted", lambda bad: bad.update(
            rational60_free_points_NEW134rod_model=bad["rational60_free_points_NEW134rod_model"][:46])),
        ("minimax-full134rod-free-coordinate-omitted", lambda bad: bad["rational60_free_points_NEW134rod_model"][0].pop()),
        ("minimax-full134rod-anchor-frame-dimension", lambda bad: bad["actual_fixed_feasible_anchor_turns"].pop()),
        ("minimax-full134rod-infeasible-anchor-turn", lambda bad: bad["actual_fixed_feasible_anchor_turns"].__setitem__(0, "100")),
        ("minimax-full134rod-nonrational-free-coordinate", lambda bad:
            bad["rational60_free_points_NEW134rod_model"][0].__setitem__(0, "not-a-rational")),
        ("minimax-full134rod-realization-radius-forged", lambda bad:
            bad["exact_necessary_model_realization_result"].update(exact_outward_realization_radius="1/100")),
        ("minimax-full134rod-exact-edge-bound-forged", lambda bad:
            bad["exact_necessary_model_realization_result"]["exact_all134rod_distance_upper_bounds"].__setitem__(0, "-1")),
        ("minimax-full134rod-unit-disk-margin-forged", lambda bad:
            bad["exact_necessary_model_realization_result"].update(exact_minimum_all60_free_unit_disk_margin="-100")),
        ("minimax-full134rod-below-radius-claim-flipped", lambda bad:
            bad["exact_necessary_model_realization_result"].update(
                exact_below_Rstar_complete134rod_NECESSARY_model_realization=
                not bad["exact_necessary_model_realization_result"]["exact_below_Rstar_complete134rod_NECESSARY_model_realization"])),
        ("minimax-full134rod-relaxation-promoted-to-cover", lambda bad:
            bad["exact_necessary_model_realization_result"].update(continuous_unit_disk_cover_NOT_proved=False)),
        ("minimax-full134rod-embedding-acceptance-invented", lambda bad:
            bad["exact_necessary_model_realization_result"].update(embedding_and_topological_cover_constraints_NOT_accepted=False)),
        ("minimax-full134rod-optimality-counterexample-invented", lambda bad:
            bad["exact_necessary_model_realization_result"].update(not_a_global_optimality_counterexample=False)),
        ("minimax-stress-old92weights-substituted", lambda bad:
            bad["NEW_full134rod_stress_kernel_certificate"].update(
                weight_numerators=bad["NEW_full134rod_stress_kernel_certificate"]["weight_numerators"][:92])),
        ("minimax-stress-nonpositive-rod-weight", lambda bad:
            bad["NEW_full134rod_stress_kernel_certificate"]["weight_numerators"].__setitem__(0, 0)),
        ("minimax-stress-false-NEW60inverse", lambda bad:
            bad["NEW_full134rod_stress_kernel_certificate"]["inverse_numerators"][0].__setitem__(
                0, str(int(bad["NEW_full134rod_stress_kernel_certificate"]["inverse_numerators"][0][0])+1))),
        ("minimax-stress-old92mode-laundered", lambda bad:
            bad["NEW_full134rod_stress_kernel_certificate"].update(mode="NEW-POSITIVE-SUPPORT")),
    ):
        reject(label, mutation)
    return rejected


def main():
    parser = argparse.ArgumentParser()
    for name in ("resource", "resource-replay", "current-audit", "source", "seed", "seed-controls",
                 "ancestor-seed", "old-full-diagnosis", "old-full-controls", "prior-diagnosis",
                 "prior-controls", "correlated-diagnosis", "correlated-controls", "diagnosis", "report"):
        parser.add_argument("--"+name, type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    original, model, seed, ancestor, prior, row, arcs, digests, layer = producer.prior_producer.input_gate(args)
    digests[args.correlated_diagnosis] = binding.sha(args.correlated_diagnosis)
    digests[args.correlated_controls] = binding.sha(args.correlated_controls)
    correlated_controls = binding.read(args.correlated_controls)
    if (correlated_controls["schema"] != producer.prior_controls.SCHEMA
            or correlated_controls["executed_test_sha256"] != binding.sha(producer.prior_controls.__file__)
            or correlated_controls["diagnosis_sha256"] != digests[args.correlated_diagnosis]
            or correlated_controls["tested_correlated_module_sha256"] != binding.sha(
                producer.prior_producer.correlated.__file__)
            or correlated_controls["verified"] is not False
            or correlated_controls["new_geometric_payments"] != 0
            or len(correlated_controls["actual_correlated_mode_rejection_controls_passed"]) != 24):
        raise ValueError("minimax independent test changed actual correlated prerequisite controls")
    record, digest = binding.read(args.diagnosis), binding.sha(args.diagnosis)
    if (record["schema"] != producer.SCHEMA
            or record["executed_probe_sha256"] != binding.sha(producer.__file__)
            or record["checked_v7_forest_sha256"] != digests[args.seed]
            or record["checked_v7_forest_controls_sha256"] != digests[args.seed_controls]
            or record["actual_current_audit_sha256"] != digests[args.current_audit]
            or record["actual_latest_candidate_layer_identity_only"] != layer
            or record["source_OPEN_index"] != row["index"] or record["actual_source_closed_box"] != row
            or record["source_file_sha256"] != seed["source_file_sha256"]
            or record["NEW_distinct_full134rod_edges"] != model["edges"]
            or record["correlated_diagnosis_sha256"] != digests[args.correlated_diagnosis]
            or record["correlated_actual_independent_controls_sha256"] != digests[args.correlated_controls]
            or record["verified"] is not False or record["new_geometric_payments"] != 0
            or record["candidate_whole_roots_removed"] != 0
            or record["continuous_disk_cover_and_global_optimality_counterexample_NOT_proved"] is not True
            or record["checked_v7_and_NEWEST_running_v8_forests_NONOPEN_proofs_and_supports_UNMODIFIED"] is not True
            or record["successful_v7_stress_supplement_NEEDS_fresh_actual_v8_OPEN_descendant_reconstruction"] is not True):
        raise ValueError("actual minimax point/stress diagnostic changed source, history or zero-payment scope")
    for module in (full, producer.prior_producer, producer.prior_producer.correlated, producer.prior_controls):
        if record["modules"][linux(Path(module.__file__))] != binding.sha(module.__file__):
            raise ValueError("actual minimax point/stress module changed during independent testing")
    current = binding.read(args.current_audit)
    radius_lower = current["r_strict_interval"][0]
    actual_leaves = {item["actual_newest_OPEN_leaf"]["index"]: item["actual_newest_OPEN_leaf"]
                     for item in prior["results"]}
    seen, checked = set(), []
    for item in record["results"]:
        leaf = item["actual_checked_v7_OPEN_leaf"]
        if leaf["index"] in seen or actual_leaves[leaf["index"]] != leaf:
            raise ValueError("actual minimax point/stress changed or repeated an old whole OPEN leaf")
        seen.add(leaf["index"])
        below, kernel = trial_controls(original, model, item, radius_lower, arcs)
        checked.append({"checked_v7_OPEN_leaf": leaf["index"],
                        "exact_radius": item["exact_necessary_model_realization_result"]["exact_outward_realization_radius"],
                        "exact_below_Rstar_full134rod_NECESSARY_model_realization": below,
                        "fresh_stress_correlated_whole_leaf_strict":
                            item["NEW_stress_correlated_result"] is not None and
                            item["NEW_stress_correlated_result"]["arithmetic_strict_target_test_passed"]})
    if seen != set(actual_leaves):
        raise ValueError("actual minimax diagnostic omitted an entire checked old leaf")
    negative = rejections(original, model, record["results"][0], radius_lower, arcs)
    if len(negative) != 16:
        raise AssertionError("actual minimax point/stress omitted a required mode guard")
    producer.prior_producer.previous.producer.unchanged_inputs(args, digests, seed)
    if binding.sha(args.diagnosis) != digest:
        raise ValueError("actual minimax diagnostic changed during independent arithmetic")
    report = {
        "schema": SCHEMA, "verified": False, "diagnosis_sha256": digest,
        "actual_full134rod_points_and_fresh_stress_results_independently_reconstructed": checked,
        "independent_interval_anchor_plus_exact_free_point_rod_checks": len(checked)*134,
        "independent_all60_free_unit_disk_checks": len(checked)*60,
        "actual_point_dimension_radius_scope_and_fresh_stress_rejection_controls_passed": negative,
        "fresh_NEW60ground_inverse_harmonic_Schur_and_nonharmonic_identities_checked": len(checked),
        "old_diagonal_and_NEW_correlated_whole_leaf_results_independently_reconstructed": True,
        "continuous_disk_cover_and_global_optimality_counterexample_NOT_proved": True,
        "successful_v7_stress_supplement_NEEDS_fresh_actual_v8_OPEN_descendant_reconstruction": True,
        "old_proofs_supports_and_NEWEST_running_histories_UNMODIFIED": True,
        "arithmetic_only_NOT_complete_latest_model_source_history_or_geometry_acceptance": True,
        "source_file_sha256": seed["source_file_sha256"],
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
        "executed_test_sha256": binding.sha(__file__),
        "tested_minimax_probe_sha256": binding.sha(producer.__file__),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({"full134rod_actual_point_and_stress_independent_controls_completed": True,
                      "actual_checked_v7_leaves": len(checked), "actual_rejections": len(negative),
                      "below_Rstar_full134rod_relaxation_points": sum(
                          item["exact_below_Rstar_full134rod_NECESSARY_model_realization"] for item in checked),
                      "fresh_strict_stress_whole_leaf_results": sum(
                          item["fresh_stress_correlated_whole_leaf_strict"] for item in checked),
                      "verified": False, "new_geometric_payments": 0}), flush=True)


if __name__ == "__main__":
    main()
