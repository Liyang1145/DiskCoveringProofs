"""NEW134rod arithmetic on actual checked newest OPEN descendants only.

No forest is edited, no old SPLIT/nonOPEN proof is replaced, and no geometric
payment or complete-source acceptance is claimed. Numerical optimization is
only a suggestion for exact fresh positive kernels and closed-leaf bounds.
"""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_current_candidate_layer_identity as identity
import n26_full_candidate_face_energy as full
import n26_typed_arithmetic_context as codec
import probe_candidate_positive_curvature_hull as fixed
import probe_candidate_signed_hull_energy as dual_suggestion
import probe_full_candidate_face_energy as old_probe
import test_full_candidate_face_energy as old_full_controls
import test_support_cost_refined_forest_arithmetic as latest_controls
import verify_conditional_force_stage as binding


SCHEMA = "N26-unaccepted-checked-newest-full134rod-robust-descendant-energy-v1"


def arguments():
    parser = argparse.ArgumentParser()
    for name in ("resource", "resource-replay", "current-audit", "source",
                 "seed", "seed-controls", "ancestor-seed", "old-full-diagnosis",
                 "old-full-controls", "report"):
        parser.add_argument("--"+name, type=Path, required=True)
    parser.add_argument("--limit", type=int, default=2)
    parser.add_argument("--rounds", type=int, default=1)
    parser.add_argument("--iterations", type=int, default=220)
    parser.add_argument("--parts", type=int, default=16)
    return parser.parse_args()


def data_gate(args):
    resource = binding.read(args.resource / "VERIFIED.json")
    if (binding.sha(args.resource / "VERIFIED.json") != fixed.RESOURCE_SHA
            or binding.sha(args.resource_replay) != fixed.RESOURCE_SHA
            or binding.read(args.resource_replay) != resource
            or resource["resource_acceptance_is_not_a_faster_current_source_interface"] is not True
            or resource["context_is_not_a_current_candidate_source_or_a_seed_history_substitute"] is not True
            or binding.sha(args.resource / "CONTEXT.json") != resource["files"]["CONTEXT.json"]
            or binding.sha(codec.__file__) != resource["files"]["n26_typed_arithmetic_context.py"]):
        raise ValueError("NEW134rod descendants changed fixed arithmetic model DATA")
    context = codec.gate(binding.read(args.resource / "CONTEXT.json")["typed_context"])
    original = context["original"]
    model = full.model_gate(original["data"][0], original["reference"], original["data"][3])
    paths = (args.seed, args.seed_controls, args.ancestor_seed, args.old_full_diagnosis,
             args.old_full_controls, args.current_audit)
    digests = {path: binding.sha(path) for path in paths}
    seed, controls = binding.read(args.seed), binding.read(args.seed_controls)
    ancestor_seed = binding.read(args.ancestor_seed)
    old, old_controls = binding.read(args.old_full_diagnosis), binding.read(args.old_full_controls)
    if (seed["schema"] != latest_controls.producer.SCHEMA
            or seed["executed_producer_sha256"] != binding.sha(latest_controls.producer.__file__)
            or controls["schema"] != latest_controls.SCHEMA
            or controls["executed_test_sha256"] != binding.sha(latest_controls.__file__)
            or controls["diagnosis_sha256"] != digests[args.seed]
            or controls["latest_arithmetic_result"] != seed["arithmetic_result"]
            or controls["both_entire_actual_closed_root_partitions_and_exact_ledgers_reconstructed"] is not True
            or controls["all_previous_non_OPEN_nodes_positive_supports_and_proved_ledgers_preserved_identically"] is not True
            or len(controls["actual_rejection_controls_passed"]) != 20
            or controls["independent_sine_square_feasible_corner_midpoint_checks"] !=
            3*controls["actual_strict_energy_leaves_independently_checked"]
            or seed["verified"] is not False or controls["verified"] is not False
            or seed["new_geometric_payments"] != 0 or controls["new_geometric_payments"] != 0
            or seed["candidate_whole_roots_removed"] != 0 or controls["candidate_whole_roots_removed"] != 0):
        raise ValueError("NEW134rod descendants lack actual latest whole-forest independent controls")
    if (digests[args.ancestor_seed] != seed["old_arithmetic_forest_sha256"]
            or controls["seed_sha256"] != digests[args.ancestor_seed]
            or ancestor_seed["source_file_sha256"] != seed["source_file_sha256"]):
        raise ValueError("NEW134rod descendants changed actual retained checked ancestor forest")
    latest_controls.old_controls.previous.retention_gate(ancestor_seed, seed)
    if (old["schema"] != old_probe.SCHEMA
            or old["executed_probe_sha256"] != binding.sha(old_probe.__file__)
            or old_controls["schema"] != old_full_controls.SCHEMA
            or old_controls["executed_test_sha256"] != binding.sha(old_full_controls.__file__)
            or old_controls["tested_NEW_full134rod_module_sha256"] != binding.sha(full.__file__)
            or old_controls["diagnosis_sha256"] != digests[args.old_full_diagnosis]
            or old["checked_old_leaf_forest_sha256"] != seed["old_arithmetic_forest_sha256"]
            or old_controls["checked_old_leaf_forest_sha256"] != seed["old_arithmetic_forest_sha256"]
            or old["NEW_distinct_full134rod_edges"] != model["edges"]
            or old["verified"] is not False or old_controls["verified"] is not False
            or old["new_geometric_payments"] != 0 or old_controls["new_geometric_payments"] != 0
            or len(old_controls["actual_NEW134rod_mode_rejection_controls_passed"]) != 20):
        raise ValueError("NEW134rod descendants changed checked old fullface DATA or lineage")
    if old["modules"][linux(Path(full.__file__))] != binding.sha(full.__file__):
        raise ValueError("NEW134rod pure arithmetic changed after its actual controls")
    for module in (latest_controls.forest, latest_controls.forest.prior,
                   latest_controls.forest.prior.signed):
        if (seed["modules"][linux(Path(module.__file__))] != binding.sha(module.__file__)
                or controls["tested_modules"][Path(module.__file__).name] != binding.sha(module.__file__)):
            raise ValueError("NEW134rod descendants changed latest old-mode leaf arithmetic")
    accepted = binding.read(args.source / "VERIFIED.json")
    for item in (old, old_controls, controls):
        if item["source_file_sha256"] != seed["source_file_sha256"]:
            raise ValueError("NEW134rod descendant source/history DATA disagree")
    for name, digest in seed["source_file_sha256"].items():
        if binding.sha(args.source / name) != digest or accepted["files"][name] != digest:
            raise ValueError("NEW134rod descendant actual source/history DATA changed")
    current = binding.read(args.current_audit)
    layer = identity.gate(current, digests[args.current_audit], args.source)
    if F(original["radius"]) != F(current["r_strict_interval"][1]):
        raise ValueError("NEW134rod descendants changed actual same-root radius")
    row = next(row for row in binding.read(args.source / "PENDING-ANGLES.json")
               if row["index"] == seed["source_OPEN_index"])
    latest_controls.old_controls.previous.scope_gate(seed, row)
    if controls["actual_source_closed_box"] != row:
        raise ValueError("NEW134rod descendants changed actual whole-root DATA ownership")
    arcs = binding.force.load_trig(args.resource)[0]
    result, pending, ledger = latest_controls.forest.replay(
        original, context["original_kernel"], arcs, row,
        seed["nodes"], seed["alternative_supports"])
    if (result != seed["arithmetic_result"] or pending != seed["pending_closed_leaf_boxes"]
            or ledger != seed["arithmetic_ledger"]):
        raise ValueError("NEW134rod descendants failed entire newest old-mode forest replay")
    return original, model, seed, ancestor_seed, old, row, arcs, digests, layer


def newest_descendants(seed, old_leaf):
    """Retain all old nodes; inspect only their actual current descendants."""
    ancestor = old_leaf["index"]
    if type(ancestor) is not int or not 0 <= ancestor < len(seed["nodes"]):
        raise ValueError("NEW134rod descendant ancestor is not an actual retained node")
    pending = {leaf["index"]: leaf for leaf in seed["pending_closed_leaf_boxes"]}
    todo, found, seen = [ancestor], [], set()
    while todo:
        index = todo.pop()
        if index in seen:
            raise ValueError("actual newest descendant subtree repeats a node")
        seen.add(index)
        node = seed["nodes"][index]
        if node["kind"] == "SPLIT":
            todo.extend(reversed(node["children"]))
        elif node["kind"] == "OPEN":
            leaf = pending[index]
            if any(not F(a) <= F(c) <= F(d) <= F(b) for a, b, c, d in zip(
                    old_leaf["lower"], old_leaf["upper"], leaf["lower"], leaf["upper"])):
                raise ValueError("actual newest OPEN descendant is outside its retained old closed box")
            found.append(leaf)
    return found


def test_kernel(original, model, certificate, leaf, tight, arcs, parts, label):
    kernel, exact_identity = old_full_controls.kernel_controls(model, certificate)
    box = list(map(F, leaf["lower"])), list(map(F, leaf["upper"]))
    point = [(a+b)/2 for a, b in zip(*box)]
    angles, numerical = old_probe.stationary.stationary(kernel, original["matrix"], *box, point)
    reference = old_probe.feasible.feasible_reference(angles, *box, original["matrix"])
    energy_certificate, result = old_probe.suggest_bound(
        original, kernel, box, reference, tight, arcs, parts)
    dual_info = {}
    if energy_certificate is not None:
        ref, lo, hi, _, _ = full.hull.hull_gate(reference, *box, original["matrix"])
        _, gradient = full.hull.outward_point_values(kernel, ref, arcs)
        dual, dual_info = dual_suggestion.suggest_dual(
            kernel, original["matrix"], ref, lo, hi, gradient,
            list(map(F, energy_certificate["signed_eta"])))
        alternative = {**deepcopy(energy_certificate), "difference_dual": dual}
        alternative_result = full.bound(
            kernel, original["matrix"], *box, alternative, original["radius"], arcs)
        if F(alternative_result["strict_energy_margin"]) > F(result["strict_energy_margin"]):
            energy_certificate, result = alternative, alternative_result
    point_value = full.hull.quadratic.point_energy_gradient(kernel, [F(0), *point], arcs)[0]
    cap = F(original["radius"])**2*F(sum(kernel["weights"]), kernel["scale"])
    tiny = original["cap"]["known_candidate_tiny_angle_cells"]
    tiny_result = full.direct.bound(
        [a for a, _ in tiny], [b for _, b in tiny], kernel, F(original["radius"])**2, arcs)
    if tiny_result["radius_conditional_whole_angle_box_excluded"]:
        raise AssertionError("fresh NEW134rod support excludes known feasible tiny candidate")
    return {
        "strategy": label, "NEW_full134rod_kernel_certificate": certificate,
        "NEW_full134rod_exact_identity_controls": exact_identity,
        "actual_midpoint_turns": list(map(str, point)),
        "exact_midpoint_energy_lower": str(point_value),
        "NEW_full134rod_same_root_energy_upper": str(cap),
        "exact_midpoint_strict_energy_margin": str(point_value-cap),
        "NEW_full134rod_energy_certificate": energy_certificate,
        "NEW_full134rod_exact_closed_leaf_result": result,
        "strict_actual_newest_closed_leaf_exclusion":
            result is not None and result["arithmetic_strict_target_test_passed"],
        "known_feasible_tiny_original_same_root_control": tiny_result,
        "fresh_reference_turns": list(map(str, reference)),
        "numerical_suggestions_NOT_proofs": {**numerical, **dual_info},
    }


def unchanged_inputs(args, digests, seed):
    for path, digest in digests.items():
        if binding.sha(path) != digest:
            raise ValueError("NEW134rod newest checked inputs changed during arithmetic")
    for name, digest in seed["source_file_sha256"].items():
        if binding.sha(args.source / name) != digest:
            raise ValueError("NEW134rod actual source/history changed during arithmetic")


def main():
    args = arguments()
    if args.report.exists():
        raise FileExistsError(args.report)
    if (not 1 <= args.limit <= 4 or not 0 <= args.rounds <= 3
            or not 1 <= args.iterations <= 1000 or not 1 <= args.parts <= 256):
        raise ValueError("invalid small newest fullface arithmetic probe limits")
    original, model, seed, ancestor_seed, old, row, arcs, digests, layer = data_gate(args)
    root_box = latest_controls.producer.BASE.tighten(
        original["matrix"], row["sharp_lower"], row["sharp_upper"])
    tight = [axis for axis, (a, b) in enumerate(zip(*root_box)) if b-a <= F(1, 10**7)]
    print(json.dumps({"entire_checked_newest_forest_replayed": True,
                      "nodes_preserved": len(seed["nodes"]),
                      "OPEN_leaves_preserved": len(seed["pending_closed_leaf_boxes"]),
                      "verified": False, "new_geometric_payments": 0}), flush=True)
    results, selected = [], set()
    # Checked positive kernels are universal necessary-model DATA for this
    # same graph. Their old leaf bounds are NOT reused as descendant proofs.
    initial_kernels = [(trial["NEW_full134rod_kernel_certificate"], trial["strategy"])
                       for item in old["results"] for trial in item["trials"]]
    for ancestor_leaf in reversed(ancestor_seed["pending_closed_leaf_boxes"]):
        for leaf in newest_descendants(seed, ancestor_leaf):
            if leaf["index"] in selected or len(selected) >= args.limit:
                continue
            selected.add(leaf["index"])
            tests = [test_kernel(original, model, certificate,
                                 leaf, tight, arcs, args.parts,
                                 "universal-checked-kernel-fresh-newest-leaf-"+strategy)
                     for certificate, strategy in initial_kernels]
            for round_index in range(args.rounds):
                if any(test["strict_actual_newest_closed_leaf_exclusion"] for test in tests):
                    break
                constructed = [test for test in tests if test["NEW_full134rod_energy_certificate"] is not None]
                if not constructed:
                    break
                best = max(constructed, key=lambda test: F(
                    test["NEW_full134rod_exact_closed_leaf_result"]["strict_energy_margin"]))
                point = list(map(F, best["fresh_reference_turns"]))
                for name, weights, optimizer in old_probe.weight_suggestions(
                        original, model, point, args.iterations):
                    certificate, _ = old_probe.exact_kernel(model, weights)
                    test = test_kernel(original, model, certificate, leaf, tight, arcs, args.parts,
                                       "fresh-adversarial-reference-round"+str(round_index+1)+"-"+name)
                    test["numerical_suggestions_NOT_proofs"].update({
                        "weight_optimizer_success": bool(optimizer.success),
                        "weight_optimizer_iterations": int(optimizer.nit)})
                    tests.append(test)
            results.append({"retained_old_OPEN_ancestor": ancestor_leaf,
                            "actual_newest_OPEN_leaf": leaf, "trials": tests})
            print(json.dumps({"actual_newest_OPEN_leaf": leaf["index"],
                              "retained_old_ancestor": ancestor_leaf["index"],
                              "exact_closed_leaf_trials": len(tests),
                              "strict_actual_newest_leaf": any(
                                  test["strict_actual_newest_closed_leaf_exclusion"] for test in tests),
                              "verified": False, "new_geometric_payments": 0}), flush=True)
    if not results:
        raise ValueError("no actual newest OPEN descendant remains for this checked old supplement")
    unchanged_inputs(args, digests, seed)
    report = {
        "schema": SCHEMA, "verified": False,
        "actual_current_audit_sha256": digests[args.current_audit],
        "actual_latest_candidate_layer_identity_only": layer,
        "source_OPEN_index": row["index"], "actual_source_closed_box": row,
        "source_file_sha256": seed["source_file_sha256"],
        "checked_newest_forest_sha256": digests[args.seed],
        "checked_newest_forest_controls_sha256": digests[args.seed_controls],
        "retained_ancestor_forest_sha256": digests[args.ancestor_seed],
        "checked_old_full134rod_diagnosis_sha256": digests[args.old_full_diagnosis],
        "checked_old_full134rod_controls_sha256": digests[args.old_full_controls],
        "NEW_distinct_full134rod_edges": model["edges"], "results": results,
        "all_newest_nodes_supports_nonOPEN_proofs_and_ledgers_UNMODIFIED": True,
        "old92rod_original_kernel_weights_inverse_and_LOCAL_model_UNMODIFIED": True,
        "only_actual_contained_newest_OPEN_descendants_freshly_tested": True,
        "universal_checked_positive_kernels_reused_as_DATA_NOT_old_leaf_bound_payments": True,
        "whole_actual_root_cover_NOT_proved": True,
        "independent_actual_newest_full134rod_arithmetic_controls_still_required": True,
        "complete_latest_source_model_history_geometry_admission_NOT_performed": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "n27_started": False, "executed_probe_sha256": binding.sha(__file__),
        "modules": {linux(Path(module.__file__)): binding.sha(module.__file__)
                    for module in (full, codec, identity, old_probe, old_full_controls,
                                   latest_controls, dual_suggestion)},
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({"NEW134rod_checked_newest_descendant_probe_completed": True,
                      "actual_newest_OPEN_leaves": len(results),
                      "strict_newest_leaves": sum(any(
                          trial["strict_actual_newest_closed_leaf_exclusion"] for trial in item["trials"])
                          for item in results),
                      "verified": False, "new_geometric_payments": 0}), flush=True)


if __name__ == "__main__":
    main()
