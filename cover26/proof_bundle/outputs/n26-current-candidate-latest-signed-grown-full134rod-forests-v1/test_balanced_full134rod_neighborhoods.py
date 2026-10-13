"""Reconstruct actual proper closed neighborhoods and all NEW energy bounds."""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import probe_balanced_full134rod_neighborhoods as producer
import verify_conditional_force_stage as binding


SCHEMA = "N26-independent-actual-balanced-full134rod-neighborhood-controls-v1"
full = producer.full


def payment_scope_gate(record):
    if (record["verified"] is not False or record["new_geometric_payments"] != 0
            or record["candidate_whole_roots_removed"] != 0
            or record["only_proper_closed_neighborhoods_NOT_whole_old_leaf_or_root"] is not True
            or record["successful_v7_neighborhood_NEEDS_fresh_actual_v8_OPEN_intersections_and_remaining_cover"] is not True
            or record["complete_latest_source_model_history_geometry_admission_NOT_performed"] is not True):
        raise ValueError("proper closed subset was promoted to a current root or geometry payment")


def neighborhood_gate(original, old_item, trial):
    leaf, turns = old_item["actual_checked_v7_OPEN_leaf"], list(map(F, old_item["actual_fixed_feasible_anchor_turns"]))
    width = F(trial["requested_closed_half_width"])
    if width not in (F(1, 1000), F(1, 100000), F(1, 10000000)):
        raise ValueError("unknown actual proper closed neighborhood width")
    base = producer.stress_producer.old.prior_producer.previous.producer.latest_controls.producer.BASE
    expected = base.tighten(
        original["matrix"], [max(F(a), t-width) for a, t in zip(leaf["lower"], turns)],
        [min(F(b), t+width) for b, t in zip(leaf["upper"], turns)])
    lower, upper = list(map(F, trial["actual_proper_closed_lower"])), list(map(F, trial["actual_proper_closed_upper"]))
    if (expected is None or lower != expected[0] or upper != expected[1]
            or (lower == list(map(F, leaf["lower"])) and upper == list(map(F, leaf["upper"])))
            or any(not F(a) <= x <= t <= y <= F(b) for a, b, x, y, t in zip(
                leaf["lower"], leaf["upper"], lower, upper, turns))):
        raise ValueError("proper neighborhood changed whole-leaf ownership, reference or exact containment")
    full.hull.quadratic.reference_gate(turns, lower, upper, original["matrix"])
    return {"lower": list(map(str, lower)), "upper": list(map(str, upper))}


def main():
    parser = argparse.ArgumentParser()
    for name in ("resource", "resource-replay", "current-audit", "source", "seed", "seed-controls",
                 "ancestor-seed", "old-full-diagnosis", "old-full-controls", "prior-diagnosis",
                 "prior-controls", "correlated-diagnosis", "correlated-controls",
                 "old-minimax-diagnosis", "old-minimax-controls",
                 "balanced-diagnosis", "balanced-controls", "diagnosis", "report"):
        parser.add_argument("--"+name, type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    original, model, seed, row, arcs, digests, layer, stresses = producer.data_gate(args)
    record, digest = binding.read(args.diagnosis), binding.sha(args.diagnosis)
    payment_scope_gate(record)
    if (record["schema"] != producer.SCHEMA
            or record["executed_probe_sha256"] != binding.sha(producer.__file__)
            or record["checked_v7_forest_sha256"] != digests[args.seed]
            or record["actual_current_audit_sha256"] != digests[args.current_audit]
            or record["actual_latest_candidate_layer_identity_only"] != layer
            or record["source_OPEN_index"] != row["index"] or record["actual_source_closed_box"] != row
            or record["source_file_sha256"] != seed["source_file_sha256"]
            or record["balanced_stress_diagnosis_sha256"] != digests[args.balanced_diagnosis]
            or record["balanced_stress_actual_independent_controls_sha256"] != digests[args.balanced_controls]
            or record["NEW_distinct_full134rod_edges"] != model["edges"]
            or record["verified"] is not False or record["new_geometric_payments"] != 0
            or record["candidate_whole_roots_removed"] != 0
            or record["only_proper_closed_neighborhoods_NOT_whole_old_leaf_or_root"] is not True
            or record["old_and_NEWEST_running_forests_supports_NONOPEN_proofs_and_ledgers_UNMODIFIED"] is not True
            or record["successful_v7_neighborhood_NEEDS_fresh_actual_v8_OPEN_intersections_and_remaining_cover"] is not True):
        raise ValueError("proper neighborhood diagnostic changed actual source/history/zero-payment scope")
    for module in (full, producer.stress_producer, producer.stress_controls,
                   producer.stress_producer.old.prior_producer):
        if record["modules"][linux(Path(module.__file__))] != binding.sha(module.__file__):
            raise ValueError("proper neighborhood arithmetic changed after actual probing")
    old = {item["actual_checked_v7_OPEN_leaf"]["index"]: item for item in stresses["results"]}
    checked, seen = [], set()
    for item in record["results"]:
        leaf = item["actual_checked_v7_OPEN_leaf"]
        old_item = old[leaf["index"]]
        if (leaf["index"] in seen or leaf != old_item["actual_checked_v7_OPEN_leaf"]
                or item["NEW_full134rod_stress_kernel_certificate"] != old_item["NEW_full134rod_stress_kernel_certificate"]):
            raise ValueError("proper neighborhoods changed or repeated an actual old case/kernel")
        seen.add(leaf["index"])
        kernel, identity = producer.stress_producer.old.prior_producer.previous.arithmetic.kernel_controls(
            model, item["NEW_full134rod_stress_kernel_certificate"])
        if identity != item["NEW_full134rod_stress_exact_identity_controls"]:
            raise ValueError("proper neighborhood NEW60inverse identity changed")
        point = [F(0), *map(F, item["actual_fixed_feasible_anchor_turns"])]
        energy = full.hull.quadratic.point_energy_gradient(kernel, point, arcs)[0]
        cap = F(original["radius"])**2*F(sum(kernel["weights"]), kernel["scale"])
        if (str(energy) != item["exact_fixed_point_energy_lower"]
                or str(cap) != item["exact_NEWweight_same_root_energy_cap"]
                or str(energy-cap) != item["exact_fixed_point_strict_energy_margin"]):
            raise ValueError("actual proper-neighborhood fixed-point energy identity failed")
        widths = set()
        for trial in item["trials"]:
            target = neighborhood_gate(original, old_item, trial)
            width = trial["requested_closed_half_width"]
            if width in widths:
                raise ValueError("proper closed neighborhood repeated a width")
            widths.add(width)
            diagonal, result = trial["NEW_stress_diagonal_certificate"], trial["NEW_stress_diagonal_result"]
            if diagonal is not None:
                producer.stress_producer.old.prior_producer.previous.arithmetic.bound_controls(
                    original, kernel, target, {"NEW_full134rod_energy_certificate": diagonal,
                                              "NEW_full134rod_exact_closed_leaf_result": result}, arcs)
            correlated, corr_result = trial["NEW_stress_correlated_certificate"], trial["NEW_stress_correlated_result"]
            if correlated is not None:
                producer.stress_producer.old.prior_controls.arithmetic_control(
                    original, kernel, target, {"NEW_correlated_quadratic_certificate": correlated,
                                              "NEW_correlated_exact_closed_leaf_result": corr_result}, arcs)
                if trial["strict_actual_proper_closed_neighborhood"] != corr_result["arithmetic_strict_target_test_passed"]:
                    raise ValueError("proper neighborhood strictness claim changed")
                checked.append({"checked_v7_leaf": leaf["index"], "proper_half_width": width,
                                "strict_actual_closed_neighborhood": corr_result["arithmetic_strict_target_test_passed"],
                                "strict_radius_margin": corr_result["strict_radius_margin"]})
            elif corr_result is not None or trial["strict_actual_proper_closed_neighborhood"] is not False:
                raise ValueError("uncertified proper neighborhood was promoted to an energy proof")
        if widths != {"1/1000", "1/100000", "1/10000000"}:
            raise ValueError("proper-neighborhood proof omitted an actual target")
    if seen != set(old):
        raise ValueError("proper neighborhood diagnostic omitted an entire old leaf case")
    negative = []
    first_item, first_trial = record["results"][0], record["results"][0]["trials"][0]
    old_item = old[first_item["actual_checked_v7_OPEN_leaf"]["index"]]
    from copy import deepcopy
    for label, mutation in (
        ("neighborhood-unknown-width", lambda bad: bad.update(requested_closed_half_width="0")),
        ("neighborhood-source-lower-bound-changed", lambda bad: bad["actual_proper_closed_lower"].__setitem__(0, "-100")),
        ("neighborhood-source-upper-bound-changed", lambda bad: bad["actual_proper_closed_upper"].__setitem__(0, "100")),
        ("neighborhood-closed-coordinate-omitted", lambda bad: bad["actual_proper_closed_lower"].pop()),
        ("neighborhood-subset-laundered-as-whole-old-leaf", lambda bad: bad.update(
            actual_proper_closed_lower=old_item["actual_checked_v7_OPEN_leaf"]["lower"],
            actual_proper_closed_upper=old_item["actual_checked_v7_OPEN_leaf"]["upper"])),
    ):
        bad = deepcopy(first_trial)
        mutation(bad)
        try:
            neighborhood_gate(original, old_item, bad)
        except (ValueError, KeyError, TypeError, IndexError):
            negative.append(label)
        else:
            raise AssertionError("invalid actual proper subset accepted: "+label)
    for label, mutation in (
        ("neighborhood-prospective-proof-paid-as-geometry", lambda bad: bad.update(verified=True, new_geometric_payments=1)),
        ("neighborhood-subset-paid-as-whole-root", lambda bad: bad.update(candidate_whole_roots_removed=1)),
        ("neighborhood-latest-v8-intersection-obligation-omitted", lambda bad: bad.update(
            successful_v7_neighborhood_NEEDS_fresh_actual_v8_OPEN_intersections_and_remaining_cover=False)),
    ):
        bad = deepcopy(record)
        mutation(bad)
        try:
            payment_scope_gate(bad)
        except (ValueError, KeyError, TypeError, IndexError):
            negative.append(label)
        else:
            raise AssertionError("invalid actual proper-neighborhood payment accepted: "+label)
    if len(negative) != 8:
        raise AssertionError("proper-neighborhood tester omitted an actual subset/payment guard")
    producer.stress_producer.old.prior_producer.previous.producer.unchanged_inputs(args, digests, seed)
    if binding.sha(args.diagnosis) != digest:
        raise ValueError("proper neighborhood input changed during independent controls")
    report = {
        "schema": SCHEMA, "verified": False, "diagnosis_sha256": digest,
        "actual_proper_closed_neighborhood_results_independently_reconstructed": checked,
        "actual_reference_containment_and_necessary_domain_reconstruction_checked": len(checked),
        "independent_sine_square_and_correlated_square_completion_controls": len(checked)*3,
        "actual_closed_subset_and_no_payment_rejection_controls_passed": negative,
        "proper_neighborhoods_NOT_whole_old_leaf_or_current_root_payments": True,
        "old_proofs_supports_and_NEWEST_running_histories_UNMODIFIED": True,
        "successful_v7_neighborhood_NEEDS_fresh_actual_v8_OPEN_intersections_and_remaining_cover": True,
        "arithmetic_only_NOT_complete_latest_model_source_history_or_geometry_acceptance": True,
        "source_file_sha256": seed["source_file_sha256"],
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
        "executed_test_sha256": binding.sha(__file__),
        "tested_neighborhood_probe_sha256": binding.sha(producer.__file__),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({"actual_full134rod_proper_neighborhood_independent_controls_completed": True,
                      "actual_neighborhoods": len(checked),
                      "strict_proper_neighborhoods": sum(item["strict_actual_closed_neighborhood"] for item in checked),
                      "NOT_whole_old_leaf_or_current_root": True,
                      "verified": False, "new_geometric_payments": 0}), flush=True)


if __name__ == "__main__":
    main()
