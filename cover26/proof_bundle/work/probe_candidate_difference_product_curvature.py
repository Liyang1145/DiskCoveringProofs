"""Zero-payment diagnosis of slack-product curvature, including proper subboxes."""

import argparse
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path

import numpy as np
from scipy.optimize import minimize_scalar

from audit_prefix_partition import linux
import n26_current_candidate_layer_identity as identity
import n26_difference_product_curvature as product
import n26_signed_hull_local_cover as partition
import n26_typed_arithmetic_context as codec
from n26_sharp_radius_constraints import tighten
import probe_candidate_positive_curvature_hull as fixed
import verify_conditional_force_stage as binding


PAIRS = ([7, 8], [15, 0])


def suggest(kernel, matrix, ref, box, arcs, parts, tight):
    minorant, _ = product.integrated.integrated_minorant(
        kernel, matrix, ref, *box, arcs, parts)
    u, a = product.difference_slack(matrix, [F(0), *ref], PAIRS[0])
    v, b = product.difference_slack(matrix, [F(0), *ref], PAIRS[1])
    h = np.array([[float(value) for value in line] for line in minorant])
    cross = np.outer(list(map(float, a)), list(map(float, b)))
    cross = cross + cross.T
    free = [axis for axis in range(15) if axis not in tight]

    def eigenvalue(multiplier):
        return float(np.linalg.eigvalsh(
            (h - multiplier * cross)[np.ix_(free, free)])[0])

    numerical = minimize_scalar(
        lambda multiplier: -eigenvalue(multiplier), bounds=(0, 1),
        method="bounded", options={"xatol": 1e-12})
    multiplier = F(max(0, round(float(numerical.x) * 10**12)), 10**12)
    minimum = eigenvalue(float(multiplier))
    record = {
        "necessary_slack_pairs": [list(pair) for pair in PAIRS],
        "exact_reference_slacks": [str(u), str(v)],
        "floating_product_multiplier_NOT_proof": float(multiplier),
        "floating_corrected_free_minimum_NOT_proof": minimum,
        "tight_axes": tight, "free_axes": free,
        "exact_signed_product_curvature_certificate_constructed": False,
    }
    if minimum <= 1e-12:
        return None, record
    beta = F(max(1, int(minimum / 4 * 10**12)), 10**12)
    corrected = h - float(multiplier) * cross
    ff = corrected[np.ix_(free, free)]
    coupling = corrected[np.ix_(tight, free)]
    schur = corrected[np.ix_(tight, tight)] - coupling @ np.linalg.solve(
        ff - float(beta) * np.eye(len(free)), coupling.T)
    alpha_float = max(0., -float(np.linalg.eigvalsh(schur)[0])) * 1.02 + 1
    alpha = F(int(alpha_float * 10**8) + 1, 10**8)
    raw_product = {
        "first_constraint": list(PAIRS[0]), "second_constraint": list(PAIRS[1]),
        "multiplier": str(multiplier),
    }
    for _ in range(6):
        eta = [alpha if axis in tight else -beta for axis in range(15)]
        certificate = {
            "reference_turns": list(map(str, ref)), "parts": parts,
            "signed_eta": list(map(str, eta)), "products": [raw_product],
        }
        try:
            check = product.bound(kernel, matrix, *box, certificate, F(1, 4), arcs)
        except ValueError:
            alpha = 2 * alpha + 1
        else:
            record.update(
                exact_signed_product_curvature_certificate_constructed=True,
                curvature_check_uses_dummy_radius_only_NOT_a_geometric_payment=True,
                exact_LDL_minimum_pivot=check["exact_LDL_minimum_pivot"])
            return certificate, record
    return None, record


def main():
    parser = argparse.ArgumentParser()
    for name in ("resource", "resource-replay", "current-audit", "source", "report"):
        parser.add_argument("--" + name, type=Path, required=True)
    parser.add_argument("--indices", type=int, nargs="+", default=[29, 25, 28])
    parser.add_argument("--parts", type=int, default=32)
    parser.add_argument("--near-window", default="1/1000")
    parser.add_argument("--local-window", default="1/2500000")
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    near_window, local_window = F(args.near_window), F(args.local_window)
    if not 0 < local_window < near_window:
        raise ValueError("diagnostic window hierarchy invalid")
    accepted = binding.read(args.resource / "VERIFIED.json")
    if (binding.sha(args.resource / "VERIFIED.json") != fixed.RESOURCE_SHA
            or binding.sha(args.resource_replay) != fixed.RESOURCE_SHA
            or binding.read(args.resource_replay) != accepted
            or accepted["resource_acceptance_is_not_a_faster_current_source_interface"] is not True
            or accepted["context_is_not_a_current_candidate_source_or_a_seed_history_substitute"] is not True
            or binding.sha(args.resource / "CONTEXT.json") != accepted["files"]["CONTEXT.json"]
            or binding.sha(codec.__file__) != accepted["files"]["n26_typed_arithmetic_context.py"]):
        raise ValueError("product diagnosis changed fixed resource/model identity or scope")
    model = codec.gate(binding.read(args.resource / "CONTEXT.json")["typed_context"])
    original, kernel = model["original"], model["original_kernel"]
    current_digest = binding.sha(args.current_audit)
    current = binding.read(args.current_audit)
    layer = identity.gate(current, current_digest, args.source)
    if F(original["radius"]) != F(current["r_strict_interval"][1]):
        raise ValueError("product diagnosis changed the actual same-root radius")
    source_digest = binding.sha(args.source / "PENDING-ANGLES.json")
    rows = {row["index"]: row for row in binding.read(args.source / "PENDING-ANGLES.json")}
    tiny = [tuple(map(F, pair)) for pair in original["cap"]["known_candidate_tiny_angle_cells"]]
    tiny_box = tighten(original["matrix"], [a for a, _ in tiny], [c for _, c in tiny])
    ref = tiny_box[0]
    arcs = binding.force.load_trig(args.resource)[0]
    results = []
    for index in args.indices:
        row = rows[index]
        root_box = tighten(original["matrix"], row["sharp_lower"], row["sharp_upper"])
        tight = [axis for axis, (a, c) in enumerate(zip(*root_box))
                 if c - a <= F(1, 10**7)]
        whole_certificate, whole = suggest(
            kernel, original["matrix"], ref, root_box, arcs, args.parts, tight)
        if whole_certificate is not None:
            whole_check = product.bound(
                kernel, original["matrix"], *root_box, whole_certificate, original["radius"], arcs)
            whole.update(certificate=whole_certificate, arithmetic_result=whole_check)
        near_lo = [max(a, r - near_window) for a, r in zip(root_box[0], ref)]
        near_hi = [min(c, r + near_window) for c, r in zip(root_box[1], ref)]
        near_box = tighten(original["matrix"], near_lo, near_hi)
        if near_box is None:
            raise ValueError("requested diagnostic root has empty near-reference intersection")
        certificate, near = suggest(
            kernel, original["matrix"], ref, near_box, arcs, args.parts, tight)
        near.update(
            closed_lower=list(map(str, near_box[0])),
            closed_upper=list(map(str, near_box[1])),
            proper_subbox_only_NOT_entire_actual_source_root=near_box != root_box)
        if certificate is not None:
            lower, upper = [list(part) for part in near_box]
            slabs = []
            for axis in near["free_axes"]:
                for side, cut in (("left", ref[axis] - local_window),
                                  ("right", ref[axis] + local_window)):
                    if not lower[axis] < cut < upper[axis]:
                        continue
                    a, c = list(lower), list(upper)
                    if side == "left":
                        c[axis] = cut
                    else:
                        a[axis] = cut
                    box = tighten(original["matrix"], a, c)
                    slab = {
                        "axis": axis, "side": side, "cut": str(cut),
                        "parent_closed_lower": list(map(str, lower)),
                        "parent_closed_upper": list(map(str, upper)),
                        "both_closed_halves_include_shared_cut": True,
                    }
                    if box is None:
                        slab.update(kind="EMPTY", arithmetic_obligation_passed=True)
                    else:
                        check = product.bound(
                            kernel, original["matrix"], *box, certificate, original["radius"], arcs)
                        slab.update(
                            kind="DIFFERENCE-PRODUCT-ENERGY",
                            sharp_lower=list(map(str, box[0])), sharp_upper=list(map(str, box[1])),
                            certificate=certificate, arithmetic_result=check,
                            arithmetic_obligation_passed=check["arithmetic_strict_target_test_passed"])
                    slabs.append(slab)
                    if side == "left":
                        lower[axis] = cut
                    else:
                        upper[axis] = cut
                    lower, upper = tighten(original["matrix"], lower, upper)
            central = {"closed_lower": list(map(str, lower)),
                       "closed_upper": list(map(str, upper))}
            try:
                local = partition.forest.local_proof(original, lower, upper)
            except ValueError as error:
                central.update(original_LOCAL_check_passed=False, diagnostic_failure=str(error))
            else:
                central.update(original_LOCAL_check_passed=True, original_LOCAL_result=local)
            tiny_check = product.bound(
                kernel, original["matrix"], *tiny_box, certificate, original["radius"], arcs)
            if tiny_check["arithmetic_strict_target_test_passed"]:
                raise AssertionError("slack-product diagnostic excludes the known feasible tiny candidate")
            near.update(
                certificate=certificate, sequential_closed_slabs=slabs,
                central_closed_box=central,
                all_NEAR_SUBBOX_arithmetic_cover_checks_passed=all(
                    slab["arithmetic_obligation_passed"] for slab in slabs
                ) and central["original_LOCAL_check_passed"],
                known_feasible_tiny_candidate_not_strictly_excluded=True)
        record = {
            "source_OPEN_index": index, "actual_source_closed_box": row,
            "whole_root_curvature_diagnosis": whole,
            "near_reference_SUBBOX_diagnosis": near,
            "outside_near_SUBBOX_whole_root_obligations_NOT_proved": True,
            "source_entire_whole_root_REMOVED": False,
        }
        results.append(record)
        print(json.dumps({
            "root": index,
            "whole_root_curvature_candidate": whole["exact_signed_product_curvature_certificate_constructed"],
            "near_SUBBOX_curvature_candidate": near["exact_signed_product_curvature_certificate_constructed"],
            "near_SUBBOX_complete_arithmetic_cover": near.get(
                "all_NEAR_SUBBOX_arithmetic_cover_checks_passed", False),
            "whole_root_NOT_discharged": True, "verified": False, "new_geometric_payments": 0}),
            flush=True)
    if (binding.sha(args.current_audit) != current_digest
            or binding.sha(args.source / "PENDING-ANGLES.json") != source_digest):
        raise ValueError("actual current/source snapshot changed during product diagnosis")
    report = {
        "schema": "N26-unaccepted-necessary-slack-product-curvature-diagnosis-v1",
        "verified": False, "resource_acceptance_sha256": fixed.RESOURCE_SHA,
        "actual_current_audit_sha256": current_digest,
        "actual_latest_candidate_layer_identity_only": layer,
        "source_pending_angles_sha256": source_digest,
        "near_window_turns": str(near_window), "LOCAL_window_turns": str(local_window),
        "results": results,
        "all_complete_latest_model_source_and_history_replay_NOT_performed": True,
        "new_mode_NOT_supported_by_running_mixed_curvature_acceptance": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "executed_probe_sha256": binding.sha(__file__),
        "modules": {linux(Path(module.__file__)): binding.sha(module.__file__)
                    for module in (product, product.integrated, partition, codec, identity)},
        "lemma_sha256": binding.sha(Path(__file__).with_name(
            "n26-difference-product-curvature-proof.md")),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"diagnosis_completed": True, "roots_examined": len(results),
                      "verified": False, "new_geometric_payments": 0}), flush=True)


if __name__ == "__main__":
    main()
