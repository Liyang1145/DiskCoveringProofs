"""Zero-payment adaptive signed-curvature/LOCAL diagnosis on all current roots."""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

import numpy as np

from audit_prefix_partition import linux
import n26_current_candidate_layer_identity as identity
import n26_signed_hull_local_cover as cover
import n26_typed_arithmetic_context as codec
from n26_sharp_radius_constraints import tighten
import probe_candidate_positive_curvature_hull as fixed
import probe_candidate_signed_hull_energy as suggestions
import verify_conditional_force_stage as binding


def curvature(kernel, matrix, lower, upper, reference, arcs):
    tight = [k for k, (a, c) in enumerate(zip(lower, upper))
             if c - a <= F(1, 10**7)]
    free = [k for k in range(15) if k not in tight]
    if not free:
        return None, {"diagnostic_failure": "no free coordinates"}
    _, _, _, hlo, hhi = cover.hull.hull_gate(reference, lower, upper, matrix)
    hessian = cover.hull.quadratic.hessian_minorant(kernel, matrix, hlo, hhi, arcs)
    h = np.array([[float(x) for x in row] for row in hessian])
    ff = h[np.ix_(free, free)]
    minimum = float(np.linalg.eigvalsh(ff)[0])
    record = {"tight_axes": tight, "free_axes": free,
              "floating_free_block_minimum_not_proof": minimum}
    if minimum <= 1e-12:
        return None, record
    beta = F(max(1, int(minimum / 4 * 10**12)), 10**12)
    if tight:
        cross = h[np.ix_(tight, free)]
        schur = h[np.ix_(tight, tight)] - cross @ np.linalg.solve(
            ff - float(beta) * np.eye(len(free)), cross.T)
        alpha_float = max(0., -float(np.linalg.eigvalsh(schur)[0])) * 1.02 + 1
        alpha = F(int(alpha_float * 10**8) + 1, 10**8)
    else:
        alpha = F(0)
    for _ in range(6):
        diagonal = [alpha if k in tight else -beta for k in range(15)]
        try:
            check = cover.hull.signed_curvature_gate(
                kernel, matrix, hlo, hhi, diagonal, arcs)
        except ValueError:
            alpha = 2 * alpha + 1
        else:
            return diagonal, {**record, "exact_signed_curvature_result": check}
    return None, {**record, "diagnostic_failure": "signed LDL did not certify"}


def main():
    parser = argparse.ArgumentParser()
    for name in ("resource", "resource-replay", "current-audit", "source",
                 "arithmetic-controls", "report"):
        parser.add_argument("--" + name, type=Path, required=True)
    parser.add_argument("--local-window", default="1/10000000")
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    window = F(args.local_window)
    if window <= 0:
        raise ValueError("adaptive LOCAL window must be positive")
    resource = binding.read(args.resource / "VERIFIED.json")
    if (
        binding.sha(args.resource / "VERIFIED.json") != fixed.RESOURCE_SHA
        or binding.sha(args.resource_replay) != fixed.RESOURCE_SHA
        or binding.read(args.resource_replay) != resource
        or resource["resource_acceptance_is_not_a_faster_current_source_interface"] is not True
        or resource["context_is_not_a_current_candidate_source_or_a_seed_history_substitute"] is not True
        or binding.sha(args.resource / "CONTEXT.json") != resource["files"]["CONTEXT.json"]
        or binding.sha(codec.__file__) != resource["files"]["n26_typed_arithmetic_context.py"]
    ):
        raise ValueError("adaptive diagnosis changed the zero-source arithmetic resource")
    model = codec.gate(binding.read(args.resource / "CONTEXT.json")["typed_context"])
    original, kernel = model["original"], model["original_kernel"]
    current_digest = binding.sha(args.current_audit)
    current = binding.read(args.current_audit)
    layer = identity.gate(current, current_digest, args.source)
    if F(original["radius"]) != F(current["r_strict_interval"][1]):
        raise ValueError("adaptive diagnosis changed the exact current radius")
    controls = binding.read(args.arithmetic_controls)
    if (controls["tested_signed_hull_module_sha256"] != binding.sha(cover.hull.__file__)
            or controls["arithmetic_controls_passed"] is not True
            or controls["new_geometric_payments"] != 0):
        raise ValueError("adaptive diagnosis lacks actual signed arithmetic controls")
    pending = binding.read(args.source / "PENDING-ANGLES.json")
    tiny = [tuple(map(F, row))
            for row in original["cap"]["known_candidate_tiny_angle_cells"]]
    tiny_box = tighten(original["matrix"], [a for a, _ in tiny], [c for _, c in tiny])
    reference = tiny_box[0]
    cover.hull.quadratic.reference_gate(reference, *tiny_box, original["matrix"])
    arcs = binding.force.load_trig(args.resource)[0]
    roots, failures, positives = [], [], []
    for row in pending:
        root = row["index"]
        lower, upper = tighten(original["matrix"], row["sharp_lower"], row["sharp_upper"])
        diagonal, spectral = curvature(
            kernel, original["matrix"], lower, upper, reference, arcs)
        if diagonal is None:
            failures.append({"source_OPEN_index": root, **spectral})
            print(json.dumps({"root": root, "curvature_candidate": False, **spectral,
                              "verified": False, "new_geometric_payments": 0}), flush=True)
            continue
        zero = {"reference_turns": list(map(str, reference)),
                "signed_eta": list(map(str, diagonal)),
                "difference_dual": {"q": 1, "terms": []}}
        tiny_check = cover.hull.bound(
            kernel, original["matrix"], *tiny_box, zero, original["radius"], arcs)
        if tiny_check["arithmetic_strict_exclusion_test_passed"]:
            raise AssertionError("adaptive signed curvature excludes the known feasible tiny candidate")
        positives.append(root)
        slabs = []
        for axis in spectral["free_axes"]:
            for side, cut in (("left", reference[axis] - window),
                              ("right", reference[axis] + window)):
                if not lower[axis] < cut < upper[axis]:
                    continue
                slab_lower, slab_upper = list(lower), list(upper)
                if side == "left":
                    slab_upper[axis] = cut
                else:
                    slab_lower[axis] = cut
                box = tighten(original["matrix"], slab_lower, slab_upper)
                slab = {
                    "axis": axis, "side": side, "cut": str(cut),
                    "parent_closed_lower": list(map(str, lower)),
                    "parent_closed_upper": list(map(str, upper)),
                    "both_closed_halves_include_shared_cut": True,
                }
                if box is None:
                    slab.update(kind="EMPTY", arithmetic_obligation_passed=True)
                else:
                    a, c = box
                    ref, lo, hi, _, _ = cover.hull.hull_gate(
                        reference, a, c, original["matrix"])
                    _, gradient = cover.hull.outward_point_values(kernel, ref, arcs)
                    dual, _ = suggestions.suggest_dual(
                        kernel, original["matrix"], ref, lo, hi, gradient, diagonal)
                    cert = {**zero, "difference_dual": dual}
                    result = cover.hull.bound(
                        kernel, original["matrix"], a, c, cert,
                        original["radius"], arcs)
                    slab.update(
                        kind="SIGNED-HULL-ENERGY",
                        sharp_lower=list(map(str, a)), sharp_upper=list(map(str, c)),
                        certificate=cert, arithmetic_result=result,
                        arithmetic_obligation_passed=result["arithmetic_strict_exclusion_test_passed"])
                slabs.append(slab)
                if side == "left":
                    lower[axis] = cut
                else:
                    upper[axis] = cut
                lower, upper = tighten(original["matrix"], lower, upper)
        central = {"closed_lower": list(map(str, lower)),
                   "closed_upper": list(map(str, upper))}
        try:
            local = cover.forest.local_proof(original, lower, upper)
        except ValueError as error:
            central.update(original_LOCAL_arithmetic_check_passed=False,
                           diagnostic_failure=str(error))
        else:
            central.update(original_LOCAL_arithmetic_check_passed=True,
                           original_LOCAL_result=local)
        complete = all(s["arithmetic_obligation_passed"] for s in slabs) and central[
            "original_LOCAL_arithmetic_check_passed"]
        item = {
            "source_OPEN_index": root, "actual_source_closed_box": row,
            "adaptive_curvature_diagnosis": spectral,
            "sequential_closed_slabs": slabs, "central_closed_box": central,
            "all_arithmetic_cover_obligations_passed": complete,
            "current_accepted_owned_forest_not_modified_or_replaced": True,
        }
        if complete:
            independent = cover.replay(original, kernel, arcs, row, item)
            item["independent_arithmetic_cover_replay"] = independent
        roots.append(item)
        print(json.dumps({
            "root": root, "tight_angles": len(spectral["tight_axes"]),
            "positive_curvature_angles": len(spectral["free_axes"]),
            "slabs": len(slabs),
            "strict_slabs_passed": sum(s["arithmetic_obligation_passed"] for s in slabs),
            "original_LOCAL_central_check": central["original_LOCAL_arithmetic_check_passed"],
            "all_cover_arithmetic_checks_passed": complete,
            "verified": False, "new_geometric_payments": 0}), flush=True)
    if binding.sha(args.current_audit) != current_digest:
        raise ValueError("actual current snapshot changed during adaptive diagnosis")
    report = {
        "schema": "N26-unaccepted-adaptive-signed-hull-original-LOCAL-cover-diagnosis-v1",
        "verified": False, "actual_current_audit_sha256": current_digest,
        "actual_latest_candidate_layer_identity_only": layer,
        "resource_acceptance_sha256": fixed.RESOURCE_SHA,
        "arithmetic_controls_sha256": binding.sha(args.arithmetic_controls),
        "local_window_turns": str(window),
        "actual_remaining_whole_roots_examined": len(pending),
        "roots": roots, "unsupported_curvature_roots": failures,
        "all_arithmetic_cover_roots_passed": sum(
            row["all_arithmetic_cover_obligations_passed"] for row in roots),
        "known_feasible_tiny_candidate_strict_test_false_controls": positives,
        "full_latest_source_model_ownership_replay_not_performed": True,
        "no_accepted_per_root_non_OPEN_history_replaced": True,
        "current_candidate_whole_roots_removed": 0, "new_geometric_payments": 0,
        "original_52_coordinate_LOCAL_allowance_unchanged": "7/800000",
        "LOCAL_equality_region_not_declared_empty": True,
        "independent_full_owned_history_standalone_and_actual_replay_still_required": True,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "executed_probe_sha256": binding.sha(__file__),
        "modules": {linux(Path(module.__file__)): binding.sha(module.__file__)
                    for module in (cover, cover.hull, cover.forest, codec, identity, suggestions)},
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2) + "\n")
    print(json.dumps({
        "diagnosis_completed": True, "roots_examined": len(pending),
        "all_arithmetic_cover_roots_passed": report["all_arithmetic_cover_roots_passed"],
        "unsupported_curvature_roots": len(failures),
        "verified": False, "new_geometric_payments": 0}), flush=True)


if __name__ == "__main__":
    main()
