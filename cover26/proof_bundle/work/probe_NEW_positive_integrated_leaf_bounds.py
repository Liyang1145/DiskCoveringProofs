"""Supplemental actual v6-leaf DATA probe while preserved v7 remains running.

No forest nodes, ownership or proofs are edited. A successful whole old leaf
would need freshly checked contained newest OPEN descendants before reuse.
"""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

import numpy as np

from audit_prefix_partition import linux
import n26_NEW_positive_integrated_hull_energy as integrated
import n26_extended_signed_support_forest as forest
import n26_typed_arithmetic_context as codec
import probe_candidate_positive_curvature_hull as fixed
import probe_robust_positive_support_references as robust
import test_checked_extended_robust_forest_arithmetic as seed_controls
import verify_conditional_force_stage as binding


SCHEMA = "N26-unaccepted-supplemental-NEW-positive-integrated-old-leaf-diagnosis-v1"


def suggest(original, support, box, reference, tight, arcs, parts):
    kernel = integrated.kernel_gate(original["reference"], support)
    combined, _ = integrated.minorant(kernel, original["matrix"], reference, *box, arcs, parts)
    h = np.array([[float(value) for value in row] for row in combined])
    free = [axis for axis in range(15) if axis not in tight]
    minimum = float(np.linalg.eigvalsh(h[np.ix_(free, free)])[0])
    if minimum > 1e-10:
        free_eta = -F(max(1, int(minimum/4*10**12)), 10**12)
    else:
        free_eta = F(int((-minimum+max(1e-5, abs(minimum)/100))*10**12)+1, 10**12)
    shifted = h[np.ix_(free, free)]+float(free_eta)*np.eye(len(free))
    coupling = h[np.ix_(tight, free)]
    schur = h[np.ix_(tight, tight)]-coupling@np.linalg.solve(shifted, coupling.T)
    alpha = F(int((max(0., -float(np.linalg.eigvalsh(schur)[0]))*1.02+1)*10**8)+1, 10**8)
    failure = None
    for _ in range(6):
        certificate = {
            "reference_turns": list(map(str, reference)), "parts": parts,
            "signed_eta": [str(alpha if axis in tight else free_eta) for axis in range(15)],
            "difference_dual": {"q": 1, "terms": []},
        }
        try:
            result = integrated.bound(
                original["reference"], support, original["matrix"], *box,
                certificate, original["radius"], arcs)
        except ValueError as error:
            failure = str(error)
            alpha = 2*alpha+1
        else:
            return certificate, result, {
                "floating_free_eigenvalue_NOT_proof": minimum,
                "numerical_diagonal_suggestion_NOT_proof": True,
            }
    return None, None, {
        "floating_free_eigenvalue_NOT_proof": minimum,
        "numerical_diagonal_suggestion_NOT_proof": True, "exact_failure": failure,
    }


def main():
    parser = argparse.ArgumentParser()
    for name in ("resource", "resource-replay", "source", "seed", "seed-controls", "report"):
        parser.add_argument("--"+name, type=Path, required=True)
    parser.add_argument("--limit", type=int, default=2)
    parser.add_argument("--support-tries", type=int, default=3)
    parser.add_argument("--parts", type=int, default=16)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    if not 1 <= args.limit <= 8 or not 1 <= args.support_tries <= 6:
        raise ValueError("invalid small supplemental integrated leaf probe limits")
    resource = binding.read(args.resource / "VERIFIED.json")
    if (binding.sha(args.resource / "VERIFIED.json") != fixed.RESOURCE_SHA
            or binding.sha(args.resource_replay) != fixed.RESOURCE_SHA
            or binding.read(args.resource_replay) != resource
            or resource["resource_acceptance_is_not_a_faster_current_source_interface"] is not True
            or resource["context_is_not_a_current_candidate_source_or_a_seed_history_substitute"] is not True
            or binding.sha(args.resource / "CONTEXT.json") != resource["files"]["CONTEXT.json"]
            or binding.sha(codec.__file__) != resource["files"]["n26_typed_arithmetic_context.py"]):
        raise ValueError("supplemental integrated probe changed fixed arithmetic DATA identity")
    model = codec.gate(binding.read(args.resource / "CONTEXT.json")["typed_context"])
    original, kernel = model["original"], model["original_kernel"]
    seed, controls = binding.read(args.seed), binding.read(args.seed_controls)
    seed_digest, controls_digest = binding.sha(args.seed), binding.sha(args.seed_controls)
    if (seed["schema"] != seed_controls.producer.SCHEMA
            or seed["executed_producer_sha256"] != binding.sha(seed_controls.producer.__file__)
            or controls["schema"] != seed_controls.SCHEMA
            or controls["executed_test_sha256"] != binding.sha(seed_controls.__file__)
            or controls["diagnosis_sha256"] != seed_digest
            or controls["latest_arithmetic_result"] != seed["arithmetic_result"]
            or controls["verified"] is not False or controls["new_geometric_payments"] != 0
            or controls["candidate_whole_roots_removed"] != 0):
        raise ValueError("supplemental integrated probe changed actual checked ancestor DATA or scope")
    for module in (forest, forest.prior, forest.prior.signed):
        if seed["modules"][linux(Path(module.__file__))] != binding.sha(module.__file__):
            raise ValueError("supplemental integrated probe changed preserved old forest arithmetic")
    accepted = binding.read(args.source / "VERIFIED.json")
    for name, digest in seed["source_file_sha256"].items():
        if binding.sha(args.source / name) != digest or accepted["files"][name] != digest:
            raise ValueError("supplemental integrated probe changed actual source/root/history DATA")
    row = next(row for row in binding.read(args.source / "PENDING-ANGLES.json")
               if row["index"] == seed["source_OPEN_index"])
    seed_controls.previous.scope_gate(seed, row)
    arcs = binding.force.load_trig(args.resource)[0]
    result, pending, ledger = forest.replay(
        original, kernel, arcs, row, seed["nodes"], seed["alternative_supports"])
    if (result != seed["arithmetic_result"] or pending != seed["pending_closed_leaf_boxes"]
            or ledger != seed["arithmetic_ledger"]):
        raise ValueError("supplemental integrated probe failed exact whole ancestor forest reconstruction")
    root_box = robust.forest.prior.tighten(original["matrix"], row["sharp_lower"], row["sharp_upper"])
    tight = [axis for axis, (a, b) in enumerate(zip(*root_box)) if b-a <= F(1, 10**7)]
    results = []
    for leaf in pending[-args.limit:]:
        box = list(map(F, leaf["lower"])), list(map(F, leaf["upper"]))
        center = [(a+b)/2 for a, b in zip(*box)]
        ordered = sorted(range(len(seed["alternative_supports"])), key=lambda index: sum(
            (float(a)-float(F(b)))**2 for a, b in zip(
                center, seed["alternative_supports"][index]["suggestion_point_turns"])))
        trials = []
        for index in ordered[:args.support_tries]:
            support = seed["alternative_supports"][index]
            constant = robust.test_reference(original, support, box, center, tight, arcs)
            reference = list(map(F, constant["reference_turns"]))
            certificate, result, numerical = suggest(
                original, support, box, reference, tight, arcs, args.parts)
            trials.append({
                "support_index_DATA": index, "NEW_positive_support": support,
                "constant_hull_trial": constant, "NEW_integrated_certificate": certificate,
                "NEW_integrated_exact_arithmetic_result": result,
                "numerical_suggestion_NOT_proof": numerical,
                "strict_actual_old_closed_leaf_exclusion": certificate is not None
                and result["arithmetic_strict_target_test_passed"],
            })
        results.append({"old_OPEN_leaf_index": leaf["index"], "actual_old_closed_leaf": leaf, "trials": trials})
        print(json.dumps({
            "actual_old_OPEN_leaf": leaf["index"], "integrated_trials": len(trials),
            "constant_strict_trials": sum(trial["constant_hull_trial"]["strict_actual_closed_leaf_exclusion"]
                                          for trial in trials),
            "NEW_integrated_strict_trials": sum(trial["strict_actual_old_closed_leaf_exclusion"] for trial in trials),
            "verified": False, "new_geometric_payments": 0}), flush=True)
    for path, digest in ((args.seed, seed_digest), (args.seed_controls, controls_digest)):
        if binding.sha(path) != digest:
            raise ValueError("supplemental ancestor DATA changed during integrated probing")
    for name, digest in seed["source_file_sha256"].items():
        if binding.sha(args.source / name) != digest:
            raise ValueError("actual source/history DATA changed during supplemental integrated probing")
    report = {
        "schema": SCHEMA, "verified": False,
        "source_OPEN_index": row["index"], "actual_source_closed_box": row,
        "checked_ancestor_forest_sha256": seed_digest, "checked_ancestor_controls_sha256": controls_digest,
        "source_file_sha256": seed["source_file_sha256"], "results": results,
        "old_forest_nodes_supports_and_all_proofs_UNMODIFIED": True,
        "latest_running_forest_NOT_reset_or_relabelled": True,
        "successful_old_leaf_NEEDS_fresh_actual_newest_OPEN_descendant_reconstruction_before_reuse": True,
        "NEW_integrated_positive_support_mode_NOT_admitted_by_any_geometry_checker": True,
        "entire_root_cover_NOT_proved": True,
        "complete_latest_original_model_source_history_geometry_gate_NOT_performed": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "executed_probe_sha256": binding.sha(__file__),
        "modules": {linux(Path(module.__file__)): binding.sha(module.__file__)
                    for module in (integrated, integrated.alternative, integrated.hull, forest,
                                   codec, robust, seed_controls)},
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({"supplemental_NEW_integrated_leaf_probe_completed": True,
                      "actual_old_closed_leaves": len(results), "verified": False,
                      "new_geometric_payments": 0}), flush=True)


if __name__ == "__main__":
    main()
