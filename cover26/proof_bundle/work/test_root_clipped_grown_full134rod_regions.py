"""Independent exact source-root regions; no old-leaf/current payment reuse."""

from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import probe_root_clipped_grown_full134rod_regions as producer
import test_full_candidate_face_energy as diagonal_controls
import test_full134rod_correlated_support as correlated_controls
import verify_conditional_force_stage as binding


SCHEMA = "N26-independent-source-root-clipped-grown-full134rod-region-controls-v1"


def scope_gate(record, seed, row, model, layer, args, digests):
    if (record["schema"] != producer.SCHEMA
            or record["executed_probe_sha256"] != binding.sha(producer.__file__)
            or record["source_OPEN_index"] != row["index"] or record["actual_source_closed_box"] != row
            or record["source_file_sha256"] != seed["source_file_sha256"]
            or record["actual_supplied_current_audit_sha256"] != digests[args.current_audit]
            or record["actual_latest_candidate_layer_identity_only"] != layer
            or record["explicit_OLD_v7_stress_origin_forest_sha256"] != digests[args.seed]
            or record["balanced_stress_diagnosis_sha256"] != digests[args.balanced_diagnosis]
            or record["balanced_stress_controls_sha256"] != digests[args.balanced_controls]
            or record["NEW_distinct_full134rod_edges"] != model["edges"]
            or record["checked_root_half_widths"] != list(map(str, producer.WIDTHS))
            or record["nested_regions_are_NOT_disjoint_paid_leaves_or_a_latest_forest_cover"] is not True
            or record["all_original_and_NEWEST_running_forests_supports_and_ledgers_UNMODIFIED"] is not True
            or record["successful_regions_NEED_fresh_latest_OPEN_intersections_and_all_remainders"] is not True
            or record["complete_latest_source_model_history_geometry_admission_NOT_performed"] is not True
            or record["verified"] is not False or record["new_geometric_payments"] != 0
            or record["candidate_whole_roots_removed"] != 0
            or record["global_lower_bound_proved"] is not False
            or record["global_optimality_proved"] is not False or record["n27_started"] is not False):
        raise ValueError("grown source-root regions changed actual current/source or unpaid scope")
    for module in producer.modules():
        if record["modules"][linux(Path(module.__file__))] != binding.sha(module.__file__):
            raise ValueError("grown root region arithmetic module changed")


def region_control(original, row, item, trial):
    width = F(trial["requested_root_closed_half_width"])
    turns = list(map(F, item["actual_feasible_reference_turns"]))
    if width not in producer.WIDTHS:
        raise ValueError("grown root region changed an actual requested closed width")
    # Separate interval intersection and independent difference contraction;
    # do not call the producer's root-region gate for this reconstruction.
    lower = [max(F(a), t-width) for a, t in zip(row["sharp_lower"], turns)]
    upper = [min(F(b), t+width) for b, t in zip(row["sharp_upper"], turns)]
    base = producer.inputs.stress_producer.old.prior_producer.previous.producer.latest_controls.producer.BASE
    actual = base.independently_contract(original["matrix"], lower, upper)
    root = base.independently_contract(original["matrix"], row["sharp_lower"], row["sharp_upper"])
    if (actual is None or actual != (
            list(map(F, trial["actual_source_root_clipped_closed_lower"])),
            list(map(F, trial["actual_source_root_clipped_closed_upper"])))
            or type(trial["region_equals_entire_actual_source_root"]) is not bool
            or trial["region_equals_entire_actual_source_root"] != (actual == root)
            or trial["old_checked_v7_leaf_boundary_NOT_used_to_clip_this_region"] is not True
            or any(not F(a) <= l <= t <= u <= F(b) for a, b, l, t, u in zip(
                row["sharp_lower"], row["sharp_upper"], actual[0], turns, actual[1]))):
        raise ValueError("grown source-root region changed actual clipping, reference or whole-root scope")
    producer.inputs.full.hull.quadratic.reference_gate(turns, *actual, original["matrix"])
    return {"lower": list(map(str, actual[0])), "upper": list(map(str, actual[1]))}


def main():
    args = producer.arguments(test=True)
    if args.report.exists():
        raise FileExistsError(args.report)
    original, model, seed, row, arcs, digests, layer, stresses = producer.data_gate(args)
    record, digest = binding.read(args.diagnosis), binding.sha(args.diagnosis)
    scope_gate(record, seed, row, model, layer, args, digests)
    cases = {item["actual_checked_v7_OPEN_leaf"]["index"]: item for item in stresses["results"]}
    seen, checked, certified = set(), [], 0
    for item in record["results"]:
        old_leaf = item["checked_old_v7_point_origin_DATA_only"]
        old = cases[old_leaf["index"]]
        if (old_leaf["index"] in seen or old_leaf != old["actual_checked_v7_OPEN_leaf"]
                or item["actual_feasible_reference_turns"] != old["actual_fixed_feasible_anchor_turns"]
                or item["NEW_full134rod_stress_kernel_certificate"] != old["NEW_full134rod_stress_kernel_certificate"]):
            raise ValueError("grown source-root region changed or repeated actual old stress DATA")
        seen.add(old_leaf["index"])
        kernel, kernel_identity = diagonal_controls.kernel_controls(
            model, item["NEW_full134rod_stress_kernel_certificate"])
        if kernel_identity != item["fresh_NEW_full134rod_kernel_identity"]:
            raise ValueError("grown region exact full134rod inverse/model identity changed")
        widths, previous = [], None
        for trial in item["trials"]:
            target = region_control(original, row, item, trial)
            widths.append(trial["requested_root_closed_half_width"])
            if previous is not None and any(not F(a) <= F(c) <= F(d) <= F(b)
                                            for a, b, c, d in zip(
                target["lower"], target["upper"], previous["lower"], previous["upper"])):
                raise ValueError("grown root regions did not retain their entire nested predecessors")
            previous = target
            diagonal = trial["NEW_diagonal_certificate"]
            if diagonal is not None:
                diagonal_controls.bound_controls(original, kernel, target, {
                    "NEW_full134rod_energy_certificate": diagonal,
                    "NEW_full134rod_exact_closed_leaf_result": trial["NEW_diagonal_result"],
                }, arcs)
            elif trial["NEW_diagonal_result"] is not None:
                raise ValueError("grown region forged an uncertified diagonal result")
            certificate, result = trial["NEW_correlated_certificate"], trial["NEW_correlated_result"]
            if certificate is not None:
                fresh = correlated_controls.arithmetic_control(original, kernel, target, {
                    "NEW_correlated_quadratic_certificate": certificate,
                    "NEW_correlated_exact_closed_leaf_result": result,
                }, arcs)
                certified += 1
                if (type(trial["fresh_exact_strict_closed_region"]) is not bool
                        or trial["fresh_exact_strict_closed_region"] != fresh["arithmetic_strict_target_test_passed"]):
                    raise ValueError("grown root region changed exact strictness")
            elif result is not None or trial["fresh_exact_strict_closed_region"] is not False:
                raise ValueError("grown source-root region was proved without an actual certificate")
            checked.append({
                "stress_point_origin": old_leaf["index"],
                "requested_root_closed_half_width": trial["requested_root_closed_half_width"],
                "strict_closed_region": trial["fresh_exact_strict_closed_region"],
                "whole_actual_source_root": trial["region_equals_entire_actual_source_root"],
                "strict_radius_margin": result["strict_radius_margin"] if result is not None else None,
            })
        if widths != list(map(str, producer.WIDTHS)):
            raise ValueError("grown root region omitted, repeated or reordered an actual width")
    if seen != set(cases):
        raise ValueError("grown root region omitted an actual stress origin")
    rejected = []

    def reject(label, call):
        try:
            call()
        except (ValueError, KeyError, TypeError, IndexError):
            rejected.append(label)
        else:
            raise AssertionError("invalid actual grown root-region control accepted: "+label)

    first_item, first_trial = record["results"][0], record["results"][0]["trials"][0]
    for label, mutation in (
        ("grown-region-unrequested-width", lambda bad: bad.update(requested_root_closed_half_width="0")),
        ("grown-region-root-lower-escaped", lambda bad: bad[
            "actual_source_root_clipped_closed_lower"].__setitem__(0, "-100")),
        ("grown-region-root-upper-escaped", lambda bad: bad[
            "actual_source_root_clipped_closed_upper"].__setitem__(0, "100")),
        ("grown-region-closed-coordinate-omitted", lambda bad: bad[
            "actual_source_root_clipped_closed_lower"].pop()),
        ("grown-region-proper-root-subset-laundered-as-whole", lambda bad: bad.update(
            region_equals_entire_actual_source_root=not bad["region_equals_entire_actual_source_root"])),
        ("grown-region-old-leaf-clipping-laundered", lambda bad: bad.update(
            old_checked_v7_leaf_boundary_NOT_used_to_clip_this_region=False)),
    ):
        bad = deepcopy(first_trial)
        mutation(bad)
        reject(label, lambda bad=bad: region_control(original, row, first_item, bad))
    for label, mutation in (
        ("grown-regions-paid-as-current-geometry", lambda bad: bad.update(verified=True, new_geometric_payments=1)),
        ("grown-regions-paid-as-whole-root-removal", lambda bad: bad.update(candidate_whole_roots_removed=1)),
        ("grown-regions-latest-intersection-remainders-omitted", lambda bad: bad.update(
            successful_regions_NEED_fresh_latest_OPEN_intersections_and_all_remainders=False)),
        ("grown-regions-source-binding-laundered", lambda bad: bad.update(
            actual_supplied_current_audit_sha256="0"*64)),
    ):
        bad = deepcopy(record)
        mutation(bad)
        reject(label, lambda bad=bad: scope_gate(bad, seed, row, model, layer, args, digests))
    producer.unchanged(args, {**digests, args.diagnosis: digest}, seed,
                       record["modules"], binding.sha(producer.__file__))
    report = {
        "schema": SCHEMA, "verified": False, "diagnosis_sha256": digest,
        "actual_source_root_closed_regions_independently_reconstructed": checked,
        "actual_distinct_full134rod_stress_kernels_reconstructed": len(seen),
        "independent_normalized_Taylor_square_secant_sine_checks": 3*certified,
        "actual_root_subset_source_history_and_zero_payment_guards_rejected": rejected,
        "nested_regions_NOT_disjoint_paid_leaves_or_a_latest_forest_cover": True,
        "fresh_latest_OPEN_intersections_and_all_remainders_still_required": True,
        "arithmetic_only_NOT_entire_latest_model_source_history_geometry_acceptance": True,
        "source_file_sha256": seed["source_file_sha256"],
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "n27_started": False, "executed_test_sha256": binding.sha(__file__),
        "tested_probe_sha256": binding.sha(producer.__file__),
        "tested_independent_correlated_energy_sha256": binding.sha(correlated_controls.__file__),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({
        "actual_root_clipped_grown_regions_independent_controls_completed": True,
        "actual_regions": len(checked), "strict_regions": sum(item["strict_closed_region"] for item in checked),
        "actual_rejections": len(rejected), "verified": False, "new_geometric_payments": 0,
    }), flush=True)


if __name__ == "__main__":
    main()
