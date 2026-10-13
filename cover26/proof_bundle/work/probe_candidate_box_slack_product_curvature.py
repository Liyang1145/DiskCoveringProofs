"""Actual root25 closed-domain box-slack arithmetic, no geometric acceptance."""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

import numpy as np
from scipy.optimize import minimize

from audit_prefix_partition import linux
import n26_box_slack_product_curvature as product
import n26_current_candidate_layer_identity as identity
import n26_typed_arithmetic_context as codec
import probe_candidate_difference_product_curvature as previous
import probe_candidate_positive_curvature_hull as fixed
import verify_conditional_force_stage as binding


SCHEMA = "N26-unaccepted-actual-candidate-box-slack-product-curvature-diagnosis-v1"


def suggest(kernel, matrix, reference, box, arcs, parts, tight, tiny_box):
    minorant, _ = product.difference.integrated.integrated_minorant(
        kernel, matrix, reference, *box, arcs, parts)
    h = np.array([[float(value) for value in row] for row in minorant])
    free = [axis for axis in range(15) if axis not in tight]
    block = h[np.ix_(free, free)]
    minimum = float(np.linalg.eigvalsh(block)[0])
    slack_lo = [min(a, t) for a, t in zip(box[0], tiny_box[0])]
    slack_hi = [max(b, t) for b, t in zip(box[1], tiny_box[1])]
    widths = np.array([float(slack_hi[axis]-slack_lo[axis]) for axis in free])
    target = 1e-7
    start = np.full(len(free), max(0., (target-minimum)/2)+1e-5)

    def eigenvalues(weights):
        return np.linalg.eigvalsh(block+2*np.diag(weights))

    optimized = minimize(
        lambda weights: float(np.dot(weights, widths**2)+1e-12*weights.sum()),
        start, bounds=[(0., 100.)]*len(free),
        constraints={"type": "ineq", "fun": lambda weights: eigenvalues(weights)-target},
        method="SLSQP", options={"maxiter": 250, "ftol": 1e-13, "disp": False})
    choices = [
        ("uniform-positive-diagonal", start),
        ("width-weighted-positive-diagonal", np.maximum(0., optimized.x)),
    ]
    results = []
    for name, weights in choices:
        multipliers = [F(max(0, round(float(value)*10**12)), 10**12) for value in weights]
        corrected = h.copy()
        for axis, multiplier in zip(free, multipliers):
            corrected[axis, axis] += 2*float(multiplier)
        ff = corrected[np.ix_(free, free)]
        eigenvalue = float(np.linalg.eigvalsh(ff)[0])
        numerical = {
            "strategy": name, "floating_optimizer_NOT_proof": True,
            "floating_optimizer_success": bool(optimized.success),
            "floating_optimizer_message": str(optimized.message),
            "floating_uncorrected_free_minimum_NOT_proof": minimum,
            "floating_corrected_free_minimum_NOT_proof": eigenvalue,
        }
        if eigenvalue <= 1e-12:
            results.append({"certificate": None, "numerical_suggestion_NOT_proof": numerical})
            continue
        beta = F(max(1, int(eigenvalue/4*10**12)), 10**12)
        coupling = corrected[np.ix_(tight, free)]
        schur = corrected[np.ix_(tight, tight)]-coupling@np.linalg.solve(
            ff-float(beta)*np.eye(len(free)), coupling.T)
        alpha_float = max(0., -float(np.linalg.eigvalsh(schur)[0]))*1.02+1
        alpha = F(int(alpha_float*10**8)+1, 10**8)
        boxes = [{"axis": axis, "closed_lower": str(slack_lo[axis]),
                  "closed_upper": str(slack_hi[axis]), "multiplier": str(multiplier)}
                 for axis, multiplier in zip(free, multipliers) if multiplier > 0]
        if not boxes:
            results.append({"certificate": None, "numerical_suggestion_NOT_proof": numerical})
            continue
        certificate = None
        for _ in range(6):
            proposed = {
                "reference_turns": list(map(str, reference)), "parts": parts,
                "signed_eta": [str(alpha if axis in tight else -beta) for axis in range(15)],
                "difference_products": [], "box_products": boxes,
                "difference_dual": {"q": 1, "terms": []},
            }
            try:
                checked = product.bound(kernel, matrix, *box, proposed, F(1, 4), arcs)
            except ValueError:
                alpha = 2*alpha+1
            else:
                certificate = proposed
                numerical["dummy_radius_curvature_check_NOT_payment"] = True
                break
        results.append({"certificate": certificate, "numerical_suggestion_NOT_proof": numerical})
    return results


def main():
    parser = argparse.ArgumentParser()
    for name in ("resource", "resource-replay", "current-audit", "source", "report"):
        parser.add_argument("--"+name, type=Path, required=True)
    parser.add_argument("--index", type=int, default=25)
    parser.add_argument("--parts", type=int, default=16)
    parser.add_argument("--near-window", default="1/1000")
    parser.add_argument("--local-window", default="1/2500000")
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    near_window, local_window = F(args.near_window), F(args.local_window)
    if not 0 < local_window < near_window:
        raise ValueError("box-slack diagnostic has an invalid exact window hierarchy")
    resource = binding.read(args.resource / "VERIFIED.json")
    if (binding.sha(args.resource / "VERIFIED.json") != fixed.RESOURCE_SHA
            or binding.sha(args.resource_replay) != fixed.RESOURCE_SHA
            or binding.read(args.resource_replay) != resource
            or resource["resource_acceptance_is_not_a_faster_current_source_interface"] is not True
            or resource["context_is_not_a_current_candidate_source_or_a_seed_history_substitute"] is not True
            or binding.sha(args.resource / "CONTEXT.json") != resource["files"]["CONTEXT.json"]
            or binding.sha(codec.__file__) != resource["files"]["n26_typed_arithmetic_context.py"]):
        raise ValueError("box-slack diagnostic changed fixed arithmetic DATA identity")
    model = codec.gate(binding.read(args.resource / "CONTEXT.json")["typed_context"])
    original, kernel = model["original"], model["original_kernel"]
    current, current_digest = binding.read(args.current_audit), binding.sha(args.current_audit)
    layer = identity.gate(current, current_digest, args.source)
    if F(original["radius"]) != F(current["r_strict_interval"][1]):
        raise ValueError("box-slack diagnosis changed the actual same-root radius")
    accepted = binding.read(args.source / "VERIFIED.json")
    digests = {name: binding.sha(args.source / name)
               for name in ("PENDING-ANGLES.json", "PROPOSAL.json", "SOURCE-ROOT-HISTORY.json")}
    if any(accepted["files"][name] != digest for name, digest in digests.items()):
        raise ValueError("box-slack diagnosis changed actual source/root/history DATA")
    row = next(row for row in binding.read(args.source / "PENDING-ANGLES.json") if row["index"] == args.index)
    tiny = [tuple(map(F, pair)) for pair in original["cap"]["known_candidate_tiny_angle_cells"]]
    tiny_box = previous.tighten(original["matrix"], [a for a, _ in tiny], [b for _, b in tiny])
    reference = tiny_box[0]
    root_box = previous.tighten(original["matrix"], row["sharp_lower"], row["sharp_upper"])
    tight = [axis for axis, (a, b) in enumerate(zip(*root_box)) if b-a <= F(1, 10**7)]
    near_box = previous.tighten(
        original["matrix"], [max(a, r-near_window) for a, r in zip(root_box[0], reference)],
        [min(b, r+near_window) for b, r in zip(root_box[1], reference)])
    if near_box is None:
        raise ValueError("actual root has no requested closed near-reference intersection")
    arcs = binding.force.load_trig(args.resource)[0]
    results = []
    for label, box in (("WHOLE-ROOT", root_box), ("NEAR-SUBBOX", near_box)):
        for trial in suggest(kernel, original["matrix"], reference, box, arcs, args.parts, tight, tiny_box):
            item = {**trial, "domain": label,
                    "actual_closed_lower": list(map(str, box[0])),
                    "actual_closed_upper": list(map(str, box[1])),
                    "proper_subbox_only_NOT_entire_source_root": box != root_box}
            certificate = trial["certificate"]
            if certificate is not None:
                checked = product.bound(
                    kernel, original["matrix"], *box, certificate, original["radius"], arcs)
                item["exact_arithmetic_result"] = checked
                lower, upper = list(box[0]), list(box[1])
                slabs = []
                for axis in (axis for axis in range(15) if axis not in tight):
                    for side, cut in (("left", reference[axis]-local_window),
                                      ("right", reference[axis]+local_window)):
                        if not lower[axis] < cut < upper[axis]:
                            continue
                        a, b = list(lower), list(upper)
                        if side == "left":
                            b[axis] = cut
                        else:
                            a[axis] = cut
                        slab_box = previous.tighten(original["matrix"], a, b)
                        slab = {"axis": axis, "side": side, "cut": str(cut),
                                "parent_closed_lower": list(map(str, lower)),
                                "parent_closed_upper": list(map(str, upper)),
                                "both_closed_halves_include_shared_cut": True}
                        if slab_box is None:
                            slab.update(kind="EMPTY", arithmetic_obligation_passed=True)
                        else:
                            result = product.bound(
                                kernel, original["matrix"], *slab_box, certificate, original["radius"], arcs)
                            slab.update(kind="BOX-SLACK-PRODUCT-ENERGY",
                                        sharp_lower=list(map(str, slab_box[0])),
                                        sharp_upper=list(map(str, slab_box[1])),
                                        arithmetic_result=result,
                                        arithmetic_obligation_passed=result["arithmetic_strict_target_test_passed"])
                        slabs.append(slab)
                        if side == "left":
                            lower[axis] = cut
                        else:
                            upper[axis] = cut
                        lower, upper = previous.tighten(original["matrix"], lower, upper)
                central = {"closed_lower": list(map(str, lower)), "closed_upper": list(map(str, upper))}
                try:
                    local = previous.partition.forest.local_proof(original, lower, upper)
                except ValueError as error:
                    central.update(original_LOCAL_check_passed=False, failure=str(error))
                else:
                    central.update(original_LOCAL_check_passed=True, original_LOCAL_result=local)
                tiny_check = product.bound(
                    kernel, original["matrix"], *tiny_box, certificate, original["radius"], arcs)
                if tiny_check["arithmetic_strict_target_test_passed"]:
                    raise AssertionError("box-slack arithmetic excludes the known feasible tiny candidate")
                item.update(sequential_closed_slabs=slabs, central_closed_box=central,
                            known_feasible_tiny_candidate_not_strictly_excluded=True,
                            complete_actual_domain_arithmetic_cover=all(
                                slab["arithmetic_obligation_passed"] for slab in slabs)
                            and central["original_LOCAL_check_passed"])
            results.append(item)
            print(json.dumps({
                "root": args.index, "domain": label,
                "strategy": trial["numerical_suggestion_NOT_proof"]["strategy"],
                "exact_curvature_constructed": certificate is not None,
                "strict_closed_domain_exclusion": item.get("exact_arithmetic_result", {}).get(
                    "arithmetic_strict_target_test_passed", False),
                "strict_slabs": sum(slab["arithmetic_obligation_passed"]
                                    for slab in item.get("sequential_closed_slabs", [])),
                "all_slabs": len(item.get("sequential_closed_slabs", [])),
                "complete_domain_arithmetic_cover": item.get("complete_actual_domain_arithmetic_cover", False),
                "verified": False, "new_geometric_payments": 0}), flush=True)
    for name, digest in digests.items():
        if binding.sha(args.source / name) != digest:
            raise ValueError("actual source/history DATA changed during box-slack probe")
    if binding.sha(args.current_audit) != current_digest:
        raise ValueError("actual completed current snapshot changed during box-slack probe")
    report = {
        "schema": SCHEMA, "verified": False,
        "actual_current_audit_sha256": current_digest,
        "actual_latest_candidate_layer_identity_only": layer,
        "source_OPEN_index": args.index, "actual_source_closed_box": row,
        "source_file_sha256": digests, "results": results,
        "old_actual_source_root_histories_and_partial_forests_NOT_reset": True,
        "new_mode_NOT_admitted_by_mixed_or_product_geometry_checker": True,
        "complete_latest_original_model_source_history_geometry_gate_NOT_performed": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "executed_probe_sha256": binding.sha(__file__),
        "modules": {linux(Path(module.__file__)): binding.sha(module.__file__)
                    for module in (product, product.difference, product.difference.integrated,
                                   codec, identity, previous)},
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({"box_slack_probe_completed": True, "actual_trials": len(results),
                      "verified": False, "new_geometric_payments": 0}), flush=True)


if __name__ == "__main__":
    main()
