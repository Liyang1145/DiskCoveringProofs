"""Independent normalized-strip reconstruction and real NEW-mode controls."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

import n26_NEW_positive_integrated_hull_energy as integrated
import n26_typed_arithmetic_context as codec
import probe_candidate_positive_curvature_hull as fixed
import probe_NEW_positive_integrated_leaf_bounds as producer
import verify_conditional_force_stage as binding


SCHEMA = "N26-independent-actual-NEW-positive-integrated-leaf-arithmetic-controls-v1"


def check(original, arcs, leaf, trial):
    support = trial["NEW_positive_support"]
    certificate = trial["NEW_integrated_certificate"]
    result = integrated.bound(
        original["reference"], support, original["matrix"], leaf["lower"], leaf["upper"],
        certificate, original["radius"], arcs)
    if result != trial["NEW_integrated_exact_arithmetic_result"]:
        raise ValueError("actual NEW integrated arithmetic result failed exact reconstruction")
    kernel = integrated.kernel_gate(original["reference"], support)
    ref, lo, hi, _, _ = integrated.hull.hull_gate(
        certificate["reference_turns"], leaf["lower"], leaf["upper"], original["matrix"])
    parts, n = certificate["parts"], 15
    # Independently derive each normalized weight directly as an integer
    # numerator over parts^2, instead of 2(b-a)-(b^2-a^2).
    total, combined, strips = F(0), [[F(0)]*n for _ in range(n)], []
    for index in range(parts):
        weight = F(2*parts-2*index-1, parts**2)
        left, right = F(index, parts), F(index+1, parts)
        lower, upper = [], []
        for r, a, b in zip(ref[1:], lo[1:], hi[1:]):
            values = (r+left*(a-r), r+left*(b-r), r+right*(a-r), r+right*(b-r))
            lower.append(min(values))
            upper.append(max(values))
        matrix = integrated.hull.quadratic.hessian_minorant(kernel, original["matrix"], lower, upper, arcs)
        for i in range(n):
            for j in range(n):
                combined[i][j] += weight*matrix[i][j]
        total += weight
        strips.append({
            "t_closed_lower": str(left), "t_closed_upper": str(right),
            "normalized_Taylor_weight": str(weight),
            "closed_coordinate_lower": list(map(str, lower)),
            "closed_coordinate_upper": list(map(str, upper)),
        })
    if total != 1 or strips != result["closed_Taylor_strips"]:
        raise ValueError("NEW integrated exact normalized strips failed independent reconstruction")
    eta = list(map(F, certificate["signed_eta"]))
    allowance = F(n, integrated.hull.quadratic.ROUND_GRID)
    tested = [[value+(eta[i]-allowance if i == j else 0)
               for j, value in enumerate(row)] for i, row in enumerate(combined)]
    pivots = integrated.hull.quadratic.positive_ldl(tested)
    if (result["weighted_symmetric_rounding_operator_error_charged"] != str(allowance)
            or result["exact_LDL_minimum_pivot"] != str(min(pivots))
            or kernel.get("original_candidate_92_rod_46_free_vertex_kernel") is not None):
        raise ValueError("NEW integrated rounding, exact LDL or distinct kernel label changed")
    lower, upper = list(map(F, leaf["lower"])), list(map(F, leaf["upper"]))
    for point in (lower, upper, [(a+b)/2 for a, b in zip(lower, upper)]):
        full = integrated.hull.quadratic.reference_gate(point, lower, upper, original["matrix"])[0]
        numerator = 0
        for i, j, weight in kernel["pairs"]:
            _, sine = arcs.sincos_turn((full[j]-full[i])/2)
            numerator += 4*weight*max(sine[0]**2, sine[1]**2)
        energy_upper = F(numerator, kernel["energy_denominator"]*arcs.SCALE**2)
        if F(result["boundary_NEW_support_energy_lower"]) > energy_upper:
            raise AssertionError("NEW integrated whole-domain bound exceeds independent feasible point energy")
    return result


def negatives(original, arcs, leaf, trial):
    rejected = []

    def reject(label, mutation):
        bad = deepcopy(trial)
        mutation(bad)
        try:
            check(original, arcs, leaf, bad)
        except (ValueError, KeyError, TypeError, IndexError):
            rejected.append(label)
        else:
            raise AssertionError("invalid actual NEW integrated support arithmetic accepted: "+label)

    for label, mutation in (
        ("NEW-integrated-unknown-mode-field", lambda bad: bad["NEW_positive_support"].update(fake_acceptance=True)),
        ("NEW-integrated-forged-original-fixed-mode", lambda bad: bad["NEW_positive_support"].update(mode="ORIGINAL-FIXED")),
        ("NEW-integrated-original-rod-edge-omitted", lambda bad: bad["NEW_positive_support"]["reference"]["edges"].pop()),
        ("NEW-integrated-nonpositive-rod-weight", lambda bad:
         bad["NEW_positive_support"]["reference"]["weight_numerators"].__setitem__(0, "0")),
        ("NEW-integrated-false-integer-ground-inverse", lambda bad:
         bad["NEW_positive_support"]["inverse"]["inverse_numerators"][0].__setitem__(
             0, str(int(bad["NEW_positive_support"]["inverse"]["inverse_numerators"][0][0])+1))),
        ("NEW-integrated-alternative-weight-label-removed", lambda bad:
         bad["NEW_positive_support"]["reference"].update(
             alternative_weights_are_DIAGNOSTIC_not_original_accepted_support=False)),
        ("NEW-integrated-original-fixed-weights-substituted", lambda bad:
         bad["NEW_positive_support"]["reference"].update(
             weight_numerators=deepcopy(original["reference"]["weight_numerators"]))),
        ("NEW-integrated-boolean-strip-count", lambda bad: bad["NEW_integrated_certificate"].update(parts=True)),
        ("NEW-integrated-zero-strip-count", lambda bad: bad["NEW_integrated_certificate"].update(parts=0)),
        ("NEW-integrated-excessive-strip-count", lambda bad: bad["NEW_integrated_certificate"].update(parts=257)),
        ("NEW-integrated-constant-mode-certificate-substituted", lambda bad: bad["NEW_integrated_certificate"].pop("parts")),
        ("NEW-integrated-unknown-proof-field", lambda bad: bad["NEW_integrated_certificate"].update(fake_acceptance=True)),
        ("NEW-integrated-invalid-positive-LDL", lambda bad:
         bad["NEW_integrated_certificate"].update(signed_eta=["-1000000000000000"]*15)),
        ("NEW-integrated-infeasible-reference", lambda bad:
         bad["NEW_integrated_certificate"]["reference_turns"].__setitem__(0, "100")),
        ("NEW-integrated-negative-difference-dual", lambda bad:
         bad["NEW_integrated_certificate"].update(difference_dual={"q": 1, "terms": [[0, 1, "-1"]]})),
        ("NEW-integrated-duplicate-difference-dual", lambda bad:
         bad["NEW_integrated_certificate"].update(difference_dual={"q": 1, "terms": [[0, 1, "1"], [0, 1, "1"]]})),
        ("NEW-integrated-forged-radius-margin", lambda bad:
         bad["NEW_integrated_exact_arithmetic_result"].update(strict_radius_margin="1")),
        ("NEW-integrated-missing-closed-strip-boundary", lambda bad:
         bad["NEW_integrated_exact_arithmetic_result"]["closed_Taylor_strips"][0].update(t_closed_lower="1/2")),
    ):
        reject(label, mutation)
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
        raise ValueError("NEW integrated controls changed fixed arithmetic DATA identity")
    original = codec.gate(binding.read(args.resource / "CONTEXT.json")["typed_context"])["original"]
    seed, diagnosis = binding.read(args.seed), binding.read(args.diagnosis)
    seed_digest, digest = binding.sha(args.seed), binding.sha(args.diagnosis)
    if (diagnosis["schema"] != producer.SCHEMA
            or diagnosis["executed_probe_sha256"] != binding.sha(producer.__file__)
            or diagnosis["checked_ancestor_forest_sha256"] != seed_digest
            or diagnosis["verified"] is not False or diagnosis["new_geometric_payments"] != 0
            or diagnosis["candidate_whole_roots_removed"] != 0
            or diagnosis["old_forest_nodes_supports_and_all_proofs_UNMODIFIED"] is not True
            or diagnosis["latest_running_forest_NOT_reset_or_relabelled"] is not True
            or diagnosis["successful_old_leaf_NEEDS_fresh_actual_newest_OPEN_descendant_reconstruction_before_reuse"] is not True):
        raise ValueError("NEW integrated controls changed actual ancestor/supplement scope or executor")
    if diagnosis["source_file_sha256"] != seed["source_file_sha256"]:
        raise ValueError("NEW integrated supplement changed actual source/history DATA bindings")
    accepted = binding.read(args.source / "VERIFIED.json")
    for name, source_digest in seed["source_file_sha256"].items():
        if binding.sha(args.source / name) != source_digest or accepted["files"][name] != source_digest:
            raise ValueError("NEW integrated controls changed actual source/root/history DATA")
    by_index = {leaf["index"]: leaf for leaf in seed["pending_closed_leaf_boxes"]}
    arcs = binding.force.load_trig(args.resource)[0]
    checked, strict, supports = [], 0, []
    for item in diagnosis["results"]:
        leaf = item["actual_old_closed_leaf"]
        if by_index[item["old_OPEN_leaf_index"]] != leaf:
            raise ValueError("NEW integrated supplement changed actual old closed OPEN domain")
        for trial in item["trials"]:
            if trial["NEW_integrated_certificate"] is None:
                continue
            if seed["alternative_supports"][trial["support_index_DATA"]] != trial["NEW_positive_support"]:
                raise ValueError("NEW integrated supplement changed its checked same-rod support DATA")
            result = check(original, arcs, leaf, trial)
            if trial["strict_actual_old_closed_leaf_exclusion"] != result["arithmetic_strict_target_test_passed"]:
                raise ValueError("NEW integrated supplement relabelled an unsuccessful trial as strict")
            strict += int(result["arithmetic_strict_target_test_passed"])
            checked.append({"old_OPEN_leaf_index": leaf["index"],
                            "support_index_DATA": trial["support_index_DATA"],
                            "strict_actual_closed_leaf_bound": result["arithmetic_strict_target_test_passed"],
                            "strict_radius_margin": result["strict_radius_margin"],
                            "independent_exact_normalized_strips_and_LDL_reconstructed": True})
            supports.append(trial["NEW_positive_support"])
    if not checked:
        raise ValueError("NEW integrated controls have no actual constructed arithmetic trial")
    first = next((item, trial) for item in diagnosis["results"] for trial in item["trials"]
                 if trial["NEW_integrated_certificate"] is not None)
    negative = negatives(original, arcs, first[0]["actual_old_closed_leaf"], first[1])
    if len(negative) != 18:
        raise AssertionError("NEW integrated controls omitted a required actual mode rejection")
    tiny = original["cap"]["known_candidate_tiny_angle_cells"]
    for support in supports:
        kernel = integrated.kernel_gate(original["reference"], support)
        result = integrated.alternative.dirichlet.bound(
            [a for a, _ in tiny], [b for _, b in tiny], kernel, F(original["radius"])**2, arcs)
        if result["radius_conditional_whole_angle_box_excluded"]:
            raise AssertionError("NEW integrated positive-weight kernel excludes known feasible tiny candidate")
    for path, expected in ((args.seed, seed_digest), (args.diagnosis, digest)):
        if binding.sha(path) != expected:
            raise ValueError("actual NEW integrated supplement input changed during independent testing")
    for name, source_digest in seed["source_file_sha256"].items():
        if binding.sha(args.source / name) != source_digest:
            raise ValueError("actual source/history DATA changed during NEW integrated controls")
    report = {
        "schema": SCHEMA, "verified": False,
        "diagnosis_sha256": digest, "checked_ancestor_forest_sha256": seed_digest,
        "actual_constructed_NEW_integrated_trials_independently_reconstructed": checked,
        "actual_strict_old_closed_leaf_trials": strict,
        "independent_normalized_weight_formula_and_all_closed_strips_checked": True,
        "independent_sine_square_feasible_corner_midpoint_checks": 3*len(checked),
        "known_feasible_tiny_positive_weight_kernel_controls_passed": len(supports),
        "actual_NEW_mode_rejection_controls_passed": negative,
        "same_original_rods_NEW_weights_NOT_original_fixed_kernel_relabelling": True,
        "old_forest_and_latest_running_forest_not_changed": True,
        "successful_old_leaf_NEEDS_fresh_actual_newest_OPEN_descendant_reconstruction_before_reuse": True,
        "entire_root_cover_NOT_proved": True,
        "arithmetic_only_NOT_complete_latest_model_source_history_or_geometry_acceptance": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "source_file_sha256": seed["source_file_sha256"],
        "tested_NEW_integrated_module_sha256": binding.sha(integrated.__file__),
        "executed_test_sha256": binding.sha(__file__),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({"NEW_integrated_independent_actual_arithmetic_controls_completed": True,
                      "actual_trials": len(checked), "actual_strict_trials": strict,
                      "actual_rejections": len(negative), "verified": False,
                      "new_geometric_payments": 0}), flush=True)


if __name__ == "__main__":
    main()
