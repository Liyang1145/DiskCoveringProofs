"""Independent NEW60ground/134rod identities and actual leaf-energy controls."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

import n26_full_candidate_face_energy as full
import n26_typed_arithmetic_context as codec
import probe_candidate_positive_curvature_hull as fixed
import probe_full_candidate_face_energy as producer
import verify_conditional_force_stage as binding


SCHEMA = "N26-independent-actual-distinct-full134rod-candidate-energy-controls-v1"


def kernel_controls(model, certificate):
    kernel = full.kernel_gate(model, certificate)
    # Independent weighted incidence accumulation, rather than the shared
    # Laplacian helper used by the producer.
    matrix = [[0]*76 for _ in range(76)]
    adjacency = [set() for _ in range(76)]
    for (u, v), weight in zip(model["edges"], certificate["weight_numerators"]):
        incidence = {u: 1, v: -1}
        for i, a in incidence.items():
            for j, b in incidence.items():
                matrix[i][j] += weight*a*b
        adjacency[u].add(v)
        adjacency[v].add(u)
    seen, queue = set(range(16)), list(range(16))
    for u in queue:
        for v in adjacency[u]:
            if v not in seen:
                seen.add(v)
                queue.append(v)
    if len(seen) != 76 or matrix != kernel["matrix"]:
        raise ValueError("NEW134rod independent incidence or actual grounding disagreed")
    inverse, denominator = kernel["inverse"], kernel["inverse_denominator"]
    for column in range(60):
        for row in range(60):
            if sum(inverse[row][k]*matrix[16+k][16+column] for k in range(60)) != (
                    denominator if row == column else 0):
                raise ValueError("NEW60ground independent inverse-times-ground product failed")
    if (kernel.get("original_candidate_92_rod_46_free_vertex_kernel") is not None
            or kernel.get("alternative_positive_support_of_original_92_rods_NOT_original_fixed_weights") is not None
            or kernel["vertices"] != 76 or len(kernel["weights"]) != 134):
        raise ValueError("NEW134rod independent kernel was relabelled as an old92rod model")
    identity = full.native_graph.identity_control(kernel)
    return kernel, identity


def bound_controls(original, kernel, leaf, trial, arcs):
    certificate = trial["NEW_full134rod_energy_certificate"]
    result = full.bound(
        kernel, original["matrix"], leaf["lower"], leaf["upper"],
        certificate, original["radius"], arcs)
    if result != trial["NEW_full134rod_exact_closed_leaf_result"]:
        raise ValueError("actual NEW134rod whole closed leaf result failed exact reconstruction")
    ref, lo, hi, _, _ = full.hull.hull_gate(
        certificate["reference_turns"], leaf["lower"], leaf["upper"], original["matrix"])
    parts = certificate["parts"]
    total, combined = F(0), [[F(0)]*15 for _ in range(15)]
    for index in range(parts):
        a, b = F(index, parts), F(index+1, parts)
        # Independent integral expression, distinct from integer/parts^2
        # normalized weights used by the new pure arithmetic module.
        weight = 2*(b-a)-(b*b-a*a)
        lower, upper = [], []
        for r, x, y in zip(ref[1:], lo[1:], hi[1:]):
            values = (r+a*(x-r), r+a*(y-r), r+b*(x-r), r+b*(y-r))
            lower.append(min(values))
            upper.append(max(values))
        minorant = full.hull.quadratic.hessian_minorant(kernel, original["matrix"], lower, upper, arcs)
        for i in range(15):
            for j in range(15):
                combined[i][j] += weight*minorant[i][j]
        total += weight
    if total != 1:
        raise ValueError("NEW134rod independent exact Taylor integral weights did not sum1")
    eta = list(map(F, certificate["signed_eta"]))
    allowance = F(15, full.hull.quadratic.ROUND_GRID)
    pivots = full.hull.quadratic.positive_ldl([
        [value+(eta[i]-allowance if i == j else 0) for j, value in enumerate(row)]
        for i, row in enumerate(combined)])
    if (result["weighted_symmetric_rounding_operator_error_charged"] != str(allowance)
            or result["exact_positive_LDL_minimum_pivot"] != str(min(pivots))):
        raise ValueError("NEW134rod independent integrated LDL/rounding identity failed")
    lower, upper = list(map(F, leaf["lower"])), list(map(F, leaf["upper"]))
    for point in (lower, upper, [(a+b)/2 for a, b in zip(lower, upper)]):
        full_ref = full.hull.quadratic.reference_gate(point, lower, upper, original["matrix"])[0]
        numerator = 0
        for i, j, weight in kernel["pairs"]:
            _, sine = arcs.sincos_turn((full_ref[j]-full_ref[i])/2)
            numerator += 4*weight*max(sine[0]**2, sine[1]**2)
        upper_energy = F(numerator, kernel["energy_denominator"]*arcs.SCALE**2)
        if F(result["boundary_full134rod_energy_lower"]) > upper_energy:
            raise AssertionError("NEW134rod global closed-leaf bound exceeds independent feasible point energy")
    return result


def rejection_controls(original, model, leaf, trial, arcs):
    rejected = []

    def reject(label, call):
        try:
            call()
        except (ValueError, KeyError, TypeError, IndexError):
            rejected.append(label)
        else:
            raise AssertionError("invalid actual NEW134rod mode accepted: "+label)

    def changed_kernel(mutation):
        bad = deepcopy(trial["NEW_full134rod_kernel_certificate"])
        mutation(bad)
        full.kernel_gate(model, bad)

    for label, mutation in (
        ("full134-old46inverse-schema-laundered", lambda bad: bad.update(schema="N26-exact-integer-ground-Dirichlet-inverse-v1")),
        ("full134-old92positive-mode-laundered", lambda bad: bad.update(mode="NEW-POSITIVE-SUPPORT")),
        ("full134-unknown-kernel-proof-field", lambda bad: bad.update(original_fixed_kernel=True)),
        ("full134-old92weight-table-substituted", lambda bad: bad.update(weight_numerators=bad["weight_numerators"][:92])),
        ("full134-nonpositive-rod-weight", lambda bad: bad["weight_numerators"].__setitem__(0, 0)),
        ("full134-boolean-weight-not-an-integer", lambda bad: bad["weight_numerators"].__setitem__(0, True)),
        ("full134-old46ground-dimension-substituted", lambda bad: bad.update(
            inverse_numerators=[row[:46] for row in bad["inverse_numerators"][:46]])),
        ("full134-false-NEW60inverse-entry", lambda bad: bad["inverse_numerators"][0].__setitem__(
            0, str(int(bad["inverse_numerators"][0][0])+1))),
        ("full134-negative-inverse-denominator", lambda bad: bad.update(inverse_denominator="-1")),
        ("full134-zero-NEWweight-scale", lambda bad: bad.update(weight_scale=0)),
    ):
        reject(label, lambda mutation=mutation: changed_kernel(mutation))
    kernel = full.kernel_gate(model, trial["NEW_full134rod_kernel_certificate"])

    def changed_bound(mutation):
        bad = deepcopy(trial)
        mutation(bad)
        bound_controls(original, kernel, leaf, bad, arcs)

    for label, mutation in (
        ("full134-zero-Taylor-strips", lambda bad: bad["NEW_full134rod_energy_certificate"].update(parts=0)),
        ("full134-boolean-Taylor-strips", lambda bad: bad["NEW_full134rod_energy_certificate"].update(parts=True)),
        ("full134-old-constant-certificate-mode", lambda bad: bad["NEW_full134rod_energy_certificate"].pop("parts")),
        ("full134-unknown-leaf-proof-field", lambda bad: bad["NEW_full134rod_energy_certificate"].update(fake_acceptance=True)),
        ("full134-nonpositive-corrected-LDL", lambda bad: bad["NEW_full134rod_energy_certificate"].update(
            signed_eta=["-1000000000000000"]*15)),
        ("full134-infeasible-reference", lambda bad: bad["NEW_full134rod_energy_certificate"]["reference_turns"].__setitem__(0, "100")),
        ("full134-negative-difference-dual", lambda bad: bad["NEW_full134rod_energy_certificate"].update(
            difference_dual={"q": 1, "terms": [[0, 1, "-1"]]})),
        ("full134-duplicate-difference-dual", lambda bad: bad["NEW_full134rod_energy_certificate"].update(
            difference_dual={"q": 1, "terms": [[0, 1, "1"], [0, 1, "1"]]})),
        ("full134-forged-exact-radius-margin", lambda bad: bad["NEW_full134rod_exact_closed_leaf_result"].update(strict_radius_margin="1")),
        ("full134-rounding-allowance-omitted", lambda bad: bad["NEW_full134rod_exact_closed_leaf_result"].update(
            weighted_symmetric_rounding_operator_error_charged="0")),
    ):
        reject(label, lambda mutation=mutation: changed_bound(mutation))
    return rejected


def main():
    parser = argparse.ArgumentParser()
    for name in ("resource", "resource-replay", "source", "seed", "diagnosis", "report"):
        parser.add_argument("--"+name, type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    resource = binding.read(args.resource / "VERIFIED.json")
    if (binding.sha(args.resource / "VERIFIED.json") != fixed.RESOURCE_SHA
            or binding.sha(args.resource_replay) != fixed.RESOURCE_SHA
            or binding.read(args.resource_replay) != resource
            or resource["resource_acceptance_is_not_a_faster_current_source_interface"] is not True
            or resource["context_is_not_a_current_candidate_source_or_a_seed_history_substitute"] is not True
            or binding.sha(args.resource / "CONTEXT.json") != resource["files"]["CONTEXT.json"]
            or binding.sha(codec.__file__) != resource["files"]["n26_typed_arithmetic_context.py"]):
        raise ValueError("NEW134rod controls changed fixed arithmetic model DATA identity")
    original = codec.gate(binding.read(args.resource / "CONTEXT.json")["typed_context"])["original"]
    model = full.model_gate(original["data"][0], original["reference"], original["data"][3])
    diagnosis, seed = binding.read(args.diagnosis), binding.read(args.seed)
    digest, seed_digest = binding.sha(args.diagnosis), binding.sha(args.seed)
    if (diagnosis["schema"] != producer.SCHEMA
            or diagnosis["executed_probe_sha256"] != binding.sha(producer.__file__)
            or diagnosis["checked_old_leaf_forest_sha256"] != seed_digest
            or diagnosis["NEW_distinct_full134rod_edges"] != model["edges"]
            or diagnosis["verified"] is not False or diagnosis["new_geometric_payments"] != 0
            or diagnosis["candidate_whole_roots_removed"] != 0
            or diagnosis["old92rod_original_kernel_weights_inverse_and_LOCAL_model_UNMODIFIED"] is not True
            or diagnosis["old_and_latest_running_forests_NOT_reset_or_relabelled"] is not True):
        raise ValueError("NEW134rod actual diagnostic changed exact model, old forest or zero-payment scope")
    from audit_prefix_partition import linux
    if diagnosis["modules"][linux(Path(full.__file__))] != binding.sha(full.__file__):
        raise ValueError("NEW134rod pure arithmetic changed after actual probing")
    if diagnosis["source_file_sha256"] != seed["source_file_sha256"]:
        raise ValueError("NEW134rod actual diagnostic changed old source/history DATA bindings")
    accepted = binding.read(args.source / "VERIFIED.json")
    for name, expected in seed["source_file_sha256"].items():
        if binding.sha(args.source / name) != expected or accepted["files"][name] != expected:
            raise ValueError("NEW134rod controls changed actual source/root/history DATA")
    arcs = binding.force.load_trig(args.resource)[0]
    old_leaves = {leaf["index"]: leaf for leaf in seed["pending_closed_leaf_boxes"]}
    checked, kernels = [], []
    for item in diagnosis["results"]:
        leaf = item["actual_old_OPEN_leaf"]
        if old_leaves[leaf["index"]] != leaf:
            raise ValueError("NEW134rod actual diagnostic changed an old whole closed OPEN domain")
        for trial in item["trials"]:
            kernel, identity = kernel_controls(model, trial["NEW_full134rod_kernel_certificate"])
            if identity != trial["NEW_full134rod_exact_identity_controls"]:
                raise ValueError("NEW134rod actual nonharmonic square-completion controls changed")
            point = [F(0), *map(F, trial["actual_midpoint_turns"])]
            point_energy = full.hull.quadratic.point_energy_gradient(kernel, point, arcs)[0]
            cap = F(original["radius"])**2*F(sum(kernel["weights"]), kernel["scale"])
            if (str(point_energy) != trial["exact_midpoint_energy_lower"]
                    or str(cap) != trial["NEW_full134rod_same_root_energy_upper"]
                    or str(point_energy-cap) != trial["exact_midpoint_strict_energy_margin"]):
                raise ValueError("NEW134rod actual point bound or NEWweight sum failed reconstruction")
            if trial["NEW_full134rod_energy_certificate"] is not None:
                result = bound_controls(original, kernel, leaf, trial, arcs)
                if trial["strict_actual_old_closed_leaf_exclusion"] != result["arithmetic_strict_target_test_passed"]:
                    raise ValueError("NEW134rod actual closed-leaf strictness claim changed")
                checked.append({"old_OPEN_leaf_index": leaf["index"], "strategy": trial["strategy"],
                                "strict_actual_old_closed_leaf_bound": result["arithmetic_strict_target_test_passed"],
                                "strict_radius_margin": result["strict_radius_margin"]})
            kernels.append(kernel)
    first = next((item, trial) for item in diagnosis["results"] for trial in item["trials"]
                 if trial["NEW_full134rod_energy_certificate"] is not None)
    negative = rejection_controls(original, model, first[0]["actual_old_OPEN_leaf"], first[1], arcs)
    if len(negative) != 20:
        raise AssertionError("NEW134rod controls omitted a required actual mode/arithmetic rejection")
    tiny = original["cap"]["known_candidate_tiny_angle_cells"]
    for kernel in kernels:
        if full.direct.bound([a for a, _ in tiny], [b for _, b in tiny], kernel,
                             F(original["radius"])**2, arcs)["radius_conditional_whole_angle_box_excluded"]:
            raise AssertionError("NEW134rod checked support excludes the known feasible tiny candidate")
    for path, expected in ((args.diagnosis, digest), (args.seed, seed_digest)):
        if binding.sha(path) != expected:
            raise ValueError("NEW134rod actual input changed during independent testing")
    for name, expected in seed["source_file_sha256"].items():
        if binding.sha(args.source / name) != expected:
            raise ValueError("actual source/history DATA changed during NEW134rod controls")
    report = {
        "schema": SCHEMA, "verified": False,
        "diagnosis_sha256": digest, "checked_old_leaf_forest_sha256": seed_digest,
        "actual_NEW60ground_inverse_incidence_harmonic_Schur_identities_checked": len(kernels),
        "actual_NEW134rod_closed_leaf_results_independently_reconstructed": checked,
        "independent_sine_square_feasible_corner_midpoint_checks": 3*len(checked),
        "known_feasible_tiny_NEW134rod_positive_controls_passed": len(kernels),
        "actual_NEW134rod_mode_rejection_controls_passed": negative,
        "old92rod_flags_inverse_weights_and_LOCAL_model_NOT_forged_or_modified": True,
        "old_forest_and_latest_running_histories_NOT_reset": True,
        "successful_old_leaf_NEEDS_fresh_actual_newest_OPEN_descendant_reconstruction_before_reuse": True,
        "whole_actual_root_cover_NOT_proved": True,
        "arithmetic_only_NOT_complete_latest_model_source_history_or_geometry_acceptance": True,
        "source_file_sha256": seed["source_file_sha256"],
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
        "tested_NEW_full134rod_module_sha256": binding.sha(full.__file__),
        "executed_test_sha256": binding.sha(__file__),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({"NEW134rod_actual_independent_arithmetic_controls_completed": True,
                      "actual_NEW60inverse_kernels": len(kernels), "actual_closed_leaf_trials": len(checked),
                      "actual_strict_closed_leaf_trials": sum(item["strict_actual_old_closed_leaf_bound"] for item in checked),
                      "actual_rejections": len(negative), "verified": False, "new_geometric_payments": 0}), flush=True)


if __name__ == "__main__":
    main()
