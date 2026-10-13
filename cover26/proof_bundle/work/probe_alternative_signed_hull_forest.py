"""Zero-payment stronger Taylor/dual probes on preserved actual OPEN leaves."""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

import numpy as np

from audit_prefix_partition import linux
import n26_adaptive_rod_support_forest as forest
import n26_alternative_signed_hull_energy as signed
import n26_typed_arithmetic_context as codec
import probe_candidate_positive_curvature_hull as fixed
import probe_candidate_signed_hull_energy as dual_suggestion
import propose_candidate_adaptive_rod_support_forest as producer
import verify_conditional_force_stage as binding


def suggest(original, support, box, reference, tight, arcs):
    kernel = signed.alternative.kernel_gate(
        original["reference"], support["reference"], support["inverse"])
    ref, lo, hi, hull_lo, hull_hi = signed.hull.hull_gate(
        reference, *box, original["matrix"])
    exact_h = signed.hull.quadratic.hessian_minorant(
        kernel, original["matrix"], hull_lo, hull_hi, arcs)
    h = np.array([[float(value) for value in row] for row in exact_h])
    free = [axis for axis in range(15) if axis not in tight]
    minimum = float(np.linalg.eigvalsh(h[np.ix_(free, free)])[0])
    if minimum > 1e-10:
        free_eta = -F(max(1, int(minimum/4*10**12)), 10**12)
    else:
        shift = -minimum + max(1e-5, abs(minimum)/100)
        free_eta = F(int(shift*10**12)+1, 10**12)
    shifted_free = h[np.ix_(free, free)]+float(free_eta)*np.eye(len(free))
    coupling = h[np.ix_(tight, free)]
    schur = h[np.ix_(tight, tight)]-coupling @ np.linalg.solve(shifted_free, coupling.T)
    alpha = F(int((max(0., -float(np.linalg.eigvalsh(schur)[0]))*1.02+1)*10**8)+1, 10**8)
    for _ in range(6):
        eta = [alpha if axis in tight else free_eta for axis in range(15)]
        try:
            signed.hull.signed_curvature_gate(kernel, original["matrix"], hull_lo, hull_hi, eta, arcs)
        except ValueError:
            alpha = 2*alpha+1
        else:
            break
    else:
        return None, {"floating_free_eigenvalue_NOT_proof": minimum,
                      "exact_NEW_support_curvature_certificate_constructed": False}
    _, gradient = signed.hull.outward_point_values(kernel, ref, arcs)
    dual, numerical = dual_suggestion.suggest_dual(
        kernel, original["matrix"], ref, lo, hi, gradient, eta)
    certificates = [
        {"reference_turns": list(map(str, reference)), "signed_eta": list(map(str, eta)),
         "difference_dual": item}
        for item in (dual, {"q": 1, "terms": []})
    ]
    tested = [(certificate, signed.bound(
        original["reference"], support, original["matrix"], *box, certificate,
        original["radius"], arcs)) for certificate in certificates]
    certificate, result = max(tested, key=lambda pair: F(pair[1]["strict_energy_margin"]))
    return certificate, {
        "floating_free_eigenvalue_NOT_proof": minimum,
        "exact_NEW_support_curvature_certificate_constructed": True,
        "exact_arithmetic_result": result, **numerical,
    }


def main():
    parser = argparse.ArgumentParser()
    for name in ("resource", "resource-replay", "source", "seed", "report"):
        parser.add_argument("--" + name, type=Path, required=True)
    parser.add_argument("--limit", type=int, default=4)
    parser.add_argument("--iterations", type=int, default=100)
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
        raise ValueError("alternative signed probe changed fixed arithmetic DATA identity")
    model = codec.gate(binding.read(args.resource / "CONTEXT.json")["typed_context"])
    original, kernel = model["original"], model["original_kernel"]
    seed, seed_digest = binding.read(args.seed), binding.sha(args.seed)
    if (seed["schema"] != "N26-unaccepted-fresh-adaptive-original-rod-support-forest-diagnosis-v1"
            or seed["executed_producer_sha256"] != binding.sha(producer.__file__)
            or seed["verified"] is not False or seed["new_geometric_payments"] != 0
            or seed["candidate_whole_roots_removed"] != 0):
        raise ValueError("alternative signed probe changed actual preserved diagnostic or scope")
    source_acceptance = binding.read(args.source / "VERIFIED.json")
    for name, digest in seed["source_file_sha256"].items():
        if binding.sha(args.source / name) != digest or source_acceptance["files"][name] != digest:
            raise ValueError("alternative signed probe changed actual source/root/history DATA")
    row = next(row for row in binding.read(args.source / "PENDING-ANGLES.json")
               if row["index"] == seed["source_OPEN_index"])
    if row != seed["actual_source_closed_box"]:
        raise ValueError("alternative signed probe changed original whole-root ownership")
    arcs = binding.force.load_trig(args.resource)[0]
    result, pending, ledger = forest.replay(
        original, kernel, arcs, row, seed["nodes"], seed["alternative_supports"])
    if (result != seed["arithmetic_result"] or pending != seed["pending_closed_leaf_boxes"]
            or ledger != seed["arithmetic_ledger"]):
        raise ValueError("preserved complete adaptive root partition did not reconstruct")
    root_box = forest.tighten(original["matrix"], row["sharp_lower"], row["sharp_upper"])
    tight = [axis for axis, (a, b) in enumerate(zip(*root_box)) if b-a <= F(1, 10**7)]
    results = []
    for leaf in pending[:args.limit]:
        box = list(map(F, leaf["lower"])), list(map(F, leaf["upper"]))
        point = [(a+b)/2 for a, b in zip(*box)]
        signed.hull.hull_gate(point, *box, original["matrix"])
        support, _, numerical = producer.suggest_support(original, kernel, point, args.iterations)
        certificate, arithmetic = suggest(original, support, box, point, tight, arcs)
        item = {
            "source_OPEN_index": row["index"], "actual_source_closed_box": row,
            "old_OPEN_leaf_index": leaf["index"], "actual_closed_leaf": leaf,
            "NEW_positive_support": support, "NEW_signed_certificate": certificate,
            "signed_arithmetic_diagnosis": arithmetic,
            "weight_suggestion_NOT_proof": numerical,
            "proposed_strict_closed_leaf_only": certificate is not None
            and arithmetic["exact_arithmetic_result"]["arithmetic_strict_target_test_passed"],
        }
        results.append(item)
        print(json.dumps({
            "old_OPEN_leaf_probed": leaf["index"],
            "NEW_signed_support_exact_leaf_exclusion": item["proposed_strict_closed_leaf_only"],
            "verified": False, "new_geometric_payments": 0}), flush=True)
    if binding.sha(args.seed) != seed_digest:
        raise ValueError("old adaptive diagnostic changed during stronger signed probes")
    for name, digest in seed["source_file_sha256"].items():
        if binding.sha(args.source / name) != digest:
            raise ValueError("actual source/history DATA changed during signed support probes")
    report = {
        "schema": "N26-unaccepted-NEW-positive-rod-signed-hull-leaf-diagnosis-v1",
        "verified": False, "source_OPEN_index": row["index"],
        "old_arithmetic_forest_sha256": seed_digest, "results": results,
        "old_partition_all_nodes_and_closed_proofs_preserved": True,
        "NEW_supports_NOT_original_fixed_kernel_relabelling": True,
        "full_entire_source_root_cover_NOT_proved": True,
        "complete_latest_source_model_history_geometry_admission_NOT_performed": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "executed_probe_sha256": binding.sha(__file__),
        "tested_signed_NEW_support_module_sha256": binding.sha(signed.__file__),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({
        "NEW_signed_support_leaf_diagnosis_completed": True, "checked": len(results),
        "strict_closed_leaf_proposals": sum(row["proposed_strict_closed_leaf_only"] for row in results),
        "verified": False, "new_geometric_payments": 0}), flush=True)


if __name__ == "__main__":
    main()
