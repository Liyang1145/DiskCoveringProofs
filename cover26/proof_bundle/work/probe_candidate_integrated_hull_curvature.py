"""Unaccepted integrated-curvature certificates on actual remaining root data."""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

import numpy as np

from audit_prefix_partition import linux
import n26_current_candidate_layer_identity as identity
import n26_integrated_hull_curvature as integrated
import n26_typed_arithmetic_context as codec
from n26_sharp_radius_constraints import tighten
import probe_candidate_positive_curvature_hull as fixed
import verify_conditional_force_stage as binding


def main():
    parser = argparse.ArgumentParser()
    for name in ("resource", "resource-replay", "current-audit", "source", "report"):
        parser.add_argument("--" + name, type=Path, required=True)
    parser.add_argument("--indices", nargs="+", type=int, default=[33, 36, 32])
    parser.add_argument("--parts", type=int, default=16)
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
        raise ValueError("integrated diagnosis changed fixed zero-source resource/model identity")
    model = codec.gate(binding.read(args.resource / "CONTEXT.json")["typed_context"])
    original, kernel = model["original"], model["original_kernel"]
    current_digest = binding.sha(args.current_audit)
    current = binding.read(args.current_audit)
    layer = identity.gate(current, current_digest, args.source)
    if F(original["radius"]) != F(current["r_strict_interval"][1]):
        raise ValueError("integrated diagnosis changed the actual current radius")
    rows = {row["index"]: row for row in binding.read(args.source / "PENDING-ANGLES.json")}
    tiny = [tuple(map(F, row)) for row in original["cap"]["known_candidate_tiny_angle_cells"]]
    ref = tighten(original["matrix"], [a for a, _ in tiny], [c for _, c in tiny])[0]
    arcs = binding.force.load_trig(args.resource)[0]
    results = []
    for index in args.indices:
        row = rows[index]
        lower, upper = tighten(original["matrix"], row["sharp_lower"], row["sharp_upper"])
        matrix, partition = integrated.integrated_minorant(
            kernel, original["matrix"], ref, lower, upper, arcs, args.parts)
        h = np.array([[float(value) for value in line] for line in matrix])
        tight = [axis for axis, (a, c) in enumerate(zip(lower, upper))
                 if c - a <= F(1, 10**7)]
        free = [axis for axis in range(15) if axis not in tight]
        ff = h[np.ix_(free, free)]
        minimum = float(np.linalg.eigvalsh(ff)[0])
        result = {
            "source_OPEN_index": index, "actual_source_closed_box": row,
            "tight_axes": tight, "free_axes": free,
            "floating_integrated_free_block_minimum_not_proof": minimum,
            "exact_signed_integral_curvature_certified": False,
        }
        if minimum > 1e-12:
            beta = F(max(1, int(minimum / 4 * 10**12)), 10**12)
            cross = h[np.ix_(tight, free)]
            schur = h[np.ix_(tight, tight)] - cross @ np.linalg.solve(
                ff - float(beta) * np.eye(len(free)), cross.T)
            alpha_float = max(0., -float(np.linalg.eigvalsh(schur)[0])) * 1.02 + 1
            alpha = F(int(alpha_float * 10**8) + 1, 10**8)
            for _ in range(6):
                eta = [alpha if axis in tight else -beta for axis in range(15)]
                tested = [
                    [value + (eta[i] - F(15, integrated.hull.quadratic.ROUND_GRID)
                              if i == j else 0)
                     for j, value in enumerate(line)] for i, line in enumerate(matrix)]
                try:
                    pivots = integrated.hull.quadratic.positive_ldl(tested)
                except ValueError:
                    alpha = 2 * alpha + 1
                else:
                    result.update(
                        exact_signed_integral_curvature_certified=True,
                        signed_eta=list(map(str, eta)), parts=args.parts,
                        exact_LDL_minimum_pivot=str(min(pivots)),
                        weighted_rounding_operator_error_charged=str(
                            F(15, integrated.hull.quadratic.ROUND_GRID)),
                        exact_normalized_integral_weights_sum=partition[
                            "exact_normalized_integral_weights_sum"],
                        all_closed_Taylor_strips_and_shared_t_endpoints_covered=True,
                    )
                    break
        results.append(result)
        print(json.dumps({key: value for key, value in result.items()
                          if key != "actual_source_closed_box"}), flush=True)
    if binding.sha(args.current_audit) != current_digest:
        raise ValueError("current snapshot changed during integrated diagnosis")
    report = {
        "schema": "N26-unaccepted-integrated-hull-curvature-diagnosis-v1",
        "verified": False, "resource_acceptance_sha256": fixed.RESOURCE_SHA,
        "actual_current_audit_sha256": current_digest,
        "actual_latest_candidate_layer_identity_only": layer,
        "reference_turns": list(map(str, ref)), "parts": args.parts,
        "results": results,
        "exact_integrated_curvature_certificates": sum(
            row["exact_signed_integral_curvature_certified"] for row in results),
        "no_energy_support_or_complete_root_cover_proof_issued": True,
        "full_latest_source_model_history_replay_NOT_performed": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "executed_probe_sha256": binding.sha(__file__),
        "modules": {linux(Path(module.__file__)): binding.sha(module.__file__)
                    for module in (integrated, integrated.hull, codec, identity)},
        "lemma_sha256": binding.sha(Path(__file__).with_name(
            "n26-integrated-hull-curvature-proof.md")),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"diagnosis_completed": True,
                      "exact_integrated_curvature_certificates":
                          report["exact_integrated_curvature_certificates"],
                      "verified": False, "new_geometric_payments": 0}), flush=True)


if __name__ == "__main__":
    main()
