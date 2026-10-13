"""Independent exact correlated support, closed secants and NEW mode guards."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
from n26_sharp_radius_constraints import SCALE
import probe_full134rod_correlated_support as producer
import verify_conditional_force_stage as binding


SCHEMA = "N26-independent-actual-full134rod-correlated-supplement-controls-v1"
correlated = producer.correlated
full = correlated.full


def arithmetic_control(original, kernel, leaf, trial, arcs):
    certificate = trial["NEW_correlated_quadratic_certificate"]
    actual = correlated.bound(
        kernel, original["matrix"], leaf["lower"], leaf["upper"], certificate, original["radius"], arcs)
    if actual != trial["NEW_correlated_exact_closed_leaf_result"]:
        raise ValueError("actual correlated closed-leaf result failed exact reconstruction")
    ref, lo, hi, _, _ = full.hull.hull_gate(
        certificate["reference_turns"], leaf["lower"], leaf["upper"], original["matrix"])
    parts, correction = certificate["parts"], list(map(F, certificate["curvature_correction"]))
    combined, total = [[F(0)]*15 for _ in range(15)], F(0)
    # Independent integral form of the normalized weights.
    for index in range(parts):
        a, b = F(index, parts), F(index+1, parts)
        weight = 2*(b-a)-(b*b-a*a)
        lower, upper = [], []
        for r, x, y in zip(ref[1:], lo[1:], hi[1:]):
            endpoints = (r+a*(x-r), r+a*(y-r), r+b*(x-r), r+b*(y-r))
            lower.append(min(endpoints))
            upper.append(max(endpoints))
        minorant = full.hull.quadratic.hessian_minorant(kernel, original["matrix"], lower, upper, arcs)
        for i in range(15):
            for j in range(15):
                combined[i][j] += weight*minorant[i][j]
        total += weight
    if total != 1:
        raise ValueError("correlated independent closed Taylor weights did not sum1")
    error_allowance = F(15, full.hull.quadratic.ROUND_GRID)
    quadratic = [[value+(correction[i]-error_allowance if i == j else 0)
                  for j, value in enumerate(row)] for i, row in enumerate(combined)]
    pivots = full.hull.quadratic.positive_ldl(quadratic)
    a, b = [x-r for x, r in zip(lo[1:], ref[1:])], [y-r for y, r in zip(hi[1:], ref[1:])]
    energy, gradient = full.hull.outward_point_values(kernel, ref, arcs)
    error = sum((y-x)*max(abs(c), abs(d))/2 for (x, y), c, d in zip(gradient[1:], a, b))
    p = [(x+y)/2-eta*(left+right)/2 for (x, y), eta, left, right in zip(
        gradient[1:], correction, a, b)]
    constant = sum(eta*left*right/2 for eta, left, right in zip(correction, a, b))-error
    z = list(map(F, certificate["quadratic_support_point"]))
    qz = [sum(row[j]*z[j] for j in range(15)) for row in quadratic]
    at_z = sum(x*y for x, y in zip(z, qz))/2
    # Independent multiplier divergence and exact endpoint support formula,
    # not the existing shared signed-hull support helper.
    divergence, dual_constant, seen = [F(0)]*16, F(0), set()
    denominator = certificate["difference_dual"]["q"]
    for i, j, raw in certificate["difference_dual"]["terms"]:
        if (i, j) in seen or int(raw) < 0:
            raise ValueError("independent correlated difference dual is invalid")
        seen.add((i, j))
        mu = F(int(raw), denominator)
        divergence[i] -= mu
        divergence[j] += mu
        dual_constant += mu*(ref[j]-ref[i]-F(original["matrix"][i][j], SCALE))
    linear = dual_constant+sum(min((linear+value+div)*left, (linear+value+div)*right)
                               for linear, value, div, left, right in zip(p, qz, divergence[1:], a, b))
    independent_lower = energy+constant+linear-at_z
    if (str(independent_lower) != actual["boundary_full134rod_correlated_energy_lower"]
            or str(error) != actual["outward_gradient_midpoint_error_explicitly_charged"]
            or str(error_allowance) != actual["weighted_symmetric_rounding_operator_error_charged"]
            or str(min(pivots)) != actual["exact_positive_LDL_minimum_pivot"]
            or str(at_z) != actual["exact_correlated_quadratic_at_support_point"]):
        raise ValueError("independent correlated quadratic/gradient/secant/dual identity failed")
    for point in (lo[1:], hi[1:], [(x+y)/2 for x, y in zip(lo[1:], hi[1:])]):
        delta = [value-r for value, r in zip(point, ref[1:])]
        for d, eta, left, right in zip(delta, correction, a, b):
            secant_gap = -eta*d*d/2-(-eta*(left+right)*d/2+eta*left*right/2)
            if secant_gap != eta*(d-left)*(right-d)/2 or secant_gap < 0:
                raise AssertionError("closed concave correction secant identity failed")
        qd = [sum(row[j]*delta[j] for j in range(15)) for row in quadratic]
        tangent_gap = sum(x*y for x, y in zip(delta, qd))/2-sum(
            x*y for x, y in zip(delta, qz))+at_z
        displaced = [d-x for d, x in zip(delta, z)]
        exact_gap = sum(displaced[i]*quadratic[i][j]*displaced[j]
                        for i in range(15) for j in range(15))/2
        if tangent_gap != exact_gap or exact_gap < 0:
            raise AssertionError("independent correlated positive square completion failed")
        full_point = full.hull.quadratic.reference_gate(
            point, lo[1:], hi[1:], original["matrix"])[0]
        numerator = 0
        for i, j, weight in kernel["pairs"]:
            _, sine = arcs.sincos_turn((full_point[j]-full_point[i])/2)
            numerator += 4*weight*max(sine[0]**2, sine[1]**2)
        energy_upper = F(numerator, kernel["energy_denominator"]*arcs.SCALE**2)
        if independent_lower > energy_upper:
            raise AssertionError("correlated bound exceeds independent feasible sine-square point energy")
    return actual


def rejections(original, kernel, leaf, trial, arcs):
    rejected = []

    def changed_certificate(mutation):
        bad = deepcopy(trial)
        mutation(bad["NEW_correlated_quadratic_certificate"])
        arithmetic_control(original, kernel, leaf, bad, arcs)

    def reject(label, call):
        try:
            call()
        except (ValueError, KeyError, TypeError, IndexError):
            rejected.append(label)
        else:
            raise AssertionError("invalid actual correlated arithmetic accepted: "+label)

    for label, mutation in (
        ("correlated-old-diagonal-certificate-schema", lambda bad: bad.update(schema=full.SCHEMA)),
        ("correlated-unknown-proof-field", lambda bad: bad.update(fake_geometry_payment=True)),
        ("correlated-zero-Taylor-strips", lambda bad: bad.update(parts=0)),
        ("correlated-boolean-Taylor-strips", lambda bad: bad.update(parts=True)),
        ("correlated-too-many-Taylor-strips", lambda bad: bad.update(parts=257)),
        ("correlated-correction-dimension", lambda bad: bad.update(curvature_correction=["0"]*14)),
        ("correlated-negative-concave-correction", lambda bad: bad["curvature_correction"].__setitem__(0, "-1")),
        ("correlated-boolean-correction", lambda bad: bad["curvature_correction"].__setitem__(0, True)),
        ("correlated-unbounded-correction", lambda bad: bad["curvature_correction"].__setitem__(0, str(10**61))),
        ("correlated-support-point-dimension", lambda bad: bad.update(quadratic_support_point=["0"]*14)),
        ("correlated-boolean-support-point", lambda bad: bad["quadratic_support_point"].__setitem__(0, True)),
        ("correlated-unbounded-support-point", lambda bad: bad["quadratic_support_point"].__setitem__(0, str(10**61))),
        ("correlated-support-point-omitted", lambda bad: bad.pop("quadratic_support_point")),
        ("correlated-old-signed-eta-field-substituted", lambda bad: bad.update(
            signed_eta=bad.pop("curvature_correction"))),
        ("correlated-negative-difference-dual", lambda bad: bad.update(
            difference_dual={"q": 1, "terms": [[0, 1, "-1"]]})),
        ("correlated-duplicate-difference-dual", lambda bad: bad.update(
            difference_dual={"q": 1, "terms": [[0, 1, "1"], [0, 1, "1"]]})),
        ("correlated-floating-dual-numerator", lambda bad: bad.update(
            difference_dual={"q": 1, "terms": [[0, 1, 0.5]]})),
        ("correlated-zero-dual-denominator", lambda bad: bad.update(difference_dual={"q": 0, "terms": []})),
        ("correlated-boolean-dual-denominator", lambda bad: bad.update(difference_dual={"q": True, "terms": []})),
        ("correlated-unknown-dual-proof-field", lambda bad: bad["difference_dual"].update(fake_acceptance=True)),
    ):
        reject(label, lambda mutation=mutation: changed_certificate(mutation))
    for label, field, value in (
        ("correlated-forged-energy-bound", "boundary_full134rod_correlated_energy_lower", "1"),
        ("correlated-operator-rounding-charge-omitted", "weighted_symmetric_rounding_operator_error_charged", "0"),
    ):
        bad = deepcopy(trial)
        bad["NEW_correlated_exact_closed_leaf_result"][field] = value
        reject(label, lambda bad=bad: arithmetic_control(original, kernel, leaf, bad, arcs))
    reject("correlated-old92kernel-label-forged", lambda: correlated.bound(
        {**kernel, "original_candidate_92_rod_46_free_vertex_kernel": True},
        original["matrix"], leaf["lower"], leaf["upper"],
        trial["NEW_correlated_quadratic_certificate"], original["radius"], arcs))
    reject("correlated-old62vertex-dimension-substituted", lambda: correlated.bound(
        {**kernel, "vertices": 62}, original["matrix"], leaf["lower"], leaf["upper"],
        trial["NEW_correlated_quadratic_certificate"], original["radius"], arcs))
    return rejected


def main():
    parser = argparse.ArgumentParser()
    for name in ("resource", "resource-replay", "current-audit", "source", "seed", "seed-controls",
                 "ancestor-seed", "old-full-diagnosis", "old-full-controls", "prior-diagnosis",
                 "prior-controls", "diagnosis", "report"):
        parser.add_argument("--"+name, type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    original, model, seed, ancestor, prior, row, arcs, digests, layer = producer.input_gate(args)
    record, digest = binding.read(args.diagnosis), binding.sha(args.diagnosis)
    if (record["schema"] != producer.SCHEMA
            or record["executed_probe_sha256"] != binding.sha(producer.__file__)
            or record["checked_v7_forest_sha256"] != digests[args.seed]
            or record["checked_v7_forest_controls_sha256"] != digests[args.seed_controls]
            or record["prior_full134rod_leaf_diagnosis_sha256"] != digests[args.prior_diagnosis]
            or record["prior_full134rod_actual_independent_controls_sha256"] != digests[args.prior_controls]
            or record["actual_latest_candidate_layer_identity_only"] != layer
            or record["actual_current_audit_sha256"] != digests[args.current_audit]
            or record["source_OPEN_index"] != row["index"] or record["actual_source_closed_box"] != row
            or record["source_file_sha256"] != seed["source_file_sha256"]
            or record["NEW_distinct_full134rod_edges"] != model["edges"]
            or record["verified"] is not False or record["new_geometric_payments"] != 0
            or record["candidate_whole_roots_removed"] != 0
            or record["checked_v7_and_NEWEST_running_v8_forests_nonOPEN_proofs_supports_and_ledgers_UNMODIFIED"] is not True
            or record["successful_v7_supplement_NEEDS_fresh_actual_v8_OPEN_descendant_reconstruction_before_reuse"] is not True):
        raise ValueError("correlated actual supplement changed source, history, scope or executor")
    for module in (correlated, full, producer.previous, producer.previous.producer):
        if record["modules"][linux(Path(module.__file__))] != binding.sha(module.__file__):
            raise ValueError("correlated arithmetic changed after actual probing")
    if record["arithmetic_lemma_sha256"] != binding.sha(Path(producer.__file__).with_name(
            "n26-full134rod-correlated-quadratic-proof.md")):
        raise ValueError("correlated arithmetic lemma changed after actual probing")
    old_leaves = {item["actual_newest_OPEN_leaf"]["index"]: item for item in prior["results"]}
    checked, kernels, seen = [], [], set()
    for item in record["results"]:
        leaf = item["actual_checked_v7_OPEN_leaf"]
        old_item = old_leaves[leaf["index"]]
        if (leaf != old_item["actual_newest_OPEN_leaf"] or leaf["index"] in seen
                or item["retained_v6_OPEN_ancestor"] != old_item["retained_old_OPEN_ancestor"]):
            raise ValueError("correlated supplement changed an actual checked closed OPEN leaf")
        seen.add(leaf["index"])
        old_trials = {trial["strategy"]: trial for trial in old_item["trials"]
                      if trial["NEW_full134rod_energy_certificate"] is not None}
        if {trial["original_checked_strategy"] for trial in item["trials"]} != set(old_trials):
            raise ValueError("correlated supplement omitted an actual checked kernel trial")
        for trial in item["trials"]:
            old_trial = old_trials[trial["original_checked_strategy"]]
            if (trial["NEW_full134rod_kernel_certificate"] != old_trial["NEW_full134rod_kernel_certificate"]
                    or trial["old_diagonal_exact_closed_leaf_result"] != old_trial["NEW_full134rod_exact_closed_leaf_result"]):
                raise ValueError("correlated supplement changed a checked positive kernel or old bound")
            kernel, identity = producer.previous.arithmetic.kernel_controls(
                model, trial["NEW_full134rod_kernel_certificate"])
            if identity != trial["NEW_full134rod_exact_identity_controls"]:
                raise ValueError("correlated NEW60ground nonharmonic identities changed")
            result = arithmetic_control(original, kernel, leaf, trial, arcs)
            improvement = F(result["boundary_full134rod_correlated_energy_lower"])-F(
                old_trial["NEW_full134rod_exact_closed_leaf_result"]["boundary_full134rod_energy_lower"])
            if (str(improvement) != trial["exact_energy_lower_improvement_over_old_diagonal"]
                    or trial["strict_actual_checked_v7_closed_leaf_supplement"] != result["arithmetic_strict_target_test_passed"]):
                raise ValueError("correlated supplement changed exact improvement or whole-leaf strictness")
            checked.append({"checked_v7_OPEN_leaf": leaf["index"],
                            "original_strategy": trial["original_checked_strategy"],
                            "strict_whole_closed_leaf": result["arithmetic_strict_target_test_passed"],
                            "strict_radius_margin": result["strict_radius_margin"],
                            "exact_energy_lower_improvement": str(improvement)})
            kernels.append(kernel)
    if seen != set(old_leaves):
        raise ValueError("correlated supplement omitted an entire actual checked leaf")
    first = (record["results"][0]["actual_checked_v7_OPEN_leaf"], record["results"][0]["trials"][0])
    rejected = rejections(original, kernels[0], *first, arcs)
    if len(rejected) != 24:
        raise AssertionError("correlated mode omitted a required actual arithmetic rejection")
    # Positive control: z need not be a feasible point or a minimizer.
    outside = deepcopy(first[1]["NEW_correlated_quadratic_certificate"])
    outside["quadratic_support_point"][0] = "2"
    outside_result = correlated.bound(
        kernels[0], original["matrix"], first[0]["lower"], first[0]["upper"],
        outside, original["radius"], arcs)
    midpoint = [(F(a)+F(b))/2 for a, b in zip(first[0]["lower"], first[0]["upper"])]
    full_midpoint = full.hull.quadratic.reference_gate(
        midpoint, first[0]["lower"], first[0]["upper"], original["matrix"])[0]
    numerator = 0
    for i, j, weight in kernels[0]["pairs"]:
        _, sine = arcs.sincos_turn((full_midpoint[j]-full_midpoint[i])/2)
        numerator += 4*weight*max(sine[0]**2, sine[1]**2)
    midpoint_upper = F(numerator, kernels[0]["energy_denominator"]*arcs.SCALE**2)
    if F(outside_result["boundary_full134rod_correlated_energy_lower"]) > midpoint_upper:
        raise AssertionError("arbitrary outside-box tangent exceeds an actual feasible point energy")
    tiny = original["cap"]["known_candidate_tiny_angle_cells"]
    tiny_box = producer.previous.producer.latest_controls.producer.BASE.tighten(
        original["matrix"], [a for a, _ in tiny], [b for _, b in tiny])
    for kernel in kernels:
        certificate = {"schema": correlated.SCHEMA, "reference_turns": list(map(str, tiny_box[0])),
                       "parts": 16, "curvature_correction": ["1000000"]*15,
                       "quadratic_support_point": ["0"]*15, "difference_dual": {"q": 1, "terms": []}}
        if correlated.bound(kernel, original["matrix"], *tiny_box, certificate,
                            original["radius"], arcs)["arithmetic_strict_target_test_passed"]:
            raise AssertionError("correlated positive control excludes known feasible tiny candidate")
    producer.previous.producer.unchanged_inputs(args, digests, seed)
    if binding.sha(args.diagnosis) != digest:
        raise ValueError("actual correlated supplement changed during independent testing")
    report = {
        "schema": SCHEMA, "verified": False, "diagnosis_sha256": digest,
        "checked_v7_forest_sha256": digests[args.seed],
        "prior_full134rod_actual_independent_controls_sha256": digests[args.prior_controls],
        "independent_normalized_Taylor_matrix_gradient_error_closed_secants_and_dual_formula_checked": True,
        "actual_correlated_closed_leaf_results_independently_reconstructed": checked,
        "independent_correlated_square_completion_and_sine_square_controls": 3*len(checked),
        "known_feasible_tiny_correlated_positive_controls_passed": len(kernels),
        "arbitrary_rational_tangent_outside_box_correctly_NOT_required_to_be_feasible": True,
        "actual_correlated_mode_rejection_controls_passed": rejected,
        "old_diagonal_backend_original92rod_LOCAL_and_NEWEST_v8_histories_UNMODIFIED": True,
        "successful_v7_supplement_NEEDS_fresh_actual_v8_OPEN_descendant_reconstruction_before_reuse": True,
        "arithmetic_only_NOT_complete_latest_model_source_history_or_geometry_acceptance": True,
        "whole_actual_root_cover_NOT_proved": True, "source_file_sha256": seed["source_file_sha256"],
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
        "executed_test_sha256": binding.sha(__file__),
        "tested_correlated_module_sha256": binding.sha(correlated.__file__),
        "tested_correlated_probe_sha256": binding.sha(producer.__file__),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({"actual_correlated_full134rod_independent_controls_completed": True,
                      "actual_correlated_trials": len(checked),
                      "strict_correlated_whole_leaf_trials": sum(item["strict_whole_closed_leaf"] for item in checked),
                      "actual_mode_rejections": len(rejected),
                      "verified": False, "new_geometric_payments": 0}), flush=True)


if __name__ == "__main__":
    main()
