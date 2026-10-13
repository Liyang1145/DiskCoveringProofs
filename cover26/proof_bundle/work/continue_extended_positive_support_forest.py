"""Extend the actual 775-node forest, retaining every old node/support proof."""

import argparse
from collections import deque
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_broad_positive_support_suggestion as broader
import n26_current_candidate_layer_identity as identity
import n26_extended_signed_support_forest as forest
import n26_typed_arithmetic_context as codec
import probe_alternative_signed_hull_forest as suggestion
import probe_broad_positive_support_leaves as broad_producer
import probe_candidate_positive_curvature_hull as fixed
import resume_candidate_adaptive_signed_support_forest as old_producer
import verify_conditional_force_stage as binding


SCHEMA = "N26-unaccepted-extended-positive-support-signed-forest-diagnosis-v1"


def main():
    parser = argparse.ArgumentParser()
    for name in ("resource", "resource-replay", "current-audit", "source",
                 "seed", "broader-diagnosis", "report"):
        parser.add_argument("--"+name, type=Path, required=True)
    parser.add_argument("--checks", type=int, default=127)
    parser.add_argument("--depth", type=int, default=208)
    parser.add_argument("--max-supports", type=int, default=128)
    parser.add_argument("--existing-support-tries", type=int, default=3)
    parser.add_argument("--iterations", type=int, default=180)
    parser.add_argument("--log-spread", type=float, default=3.0)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    if (args.checks <= 0 or args.depth < 0 or not 35 <= args.max_supports <= forest.MAX_SUPPORTS
            or not 1 <= args.existing_support_tries <= args.max_supports):
        raise ValueError("invalid explicitly extended positive-support limits")
    resource = binding.read(args.resource / "VERIFIED.json")
    if (binding.sha(args.resource / "VERIFIED.json") != fixed.RESOURCE_SHA
            or binding.sha(args.resource_replay) != fixed.RESOURCE_SHA
            or binding.read(args.resource_replay) != resource
            or resource["resource_acceptance_is_not_a_faster_current_source_interface"] is not True
            or resource["context_is_not_a_current_candidate_source_or_a_seed_history_substitute"] is not True
            or binding.sha(args.resource / "CONTEXT.json") != resource["files"]["CONTEXT.json"]
            or binding.sha(codec.__file__) != resource["files"]["n26_typed_arithmetic_context.py"]):
        raise ValueError("extended continuation changed zero-source arithmetic DATA identity")
    model = codec.gate(binding.read(args.resource / "CONTEXT.json")["typed_context"])
    original, kernel = model["original"], model["original_kernel"]
    current_digest = binding.sha(args.current_audit)
    current = binding.read(args.current_audit)
    layer = identity.gate(current, current_digest, args.source)
    if F(original["radius"]) != F(current["r_strict_interval"][1]):
        raise ValueError("extended continuation changed actual same-root radius")
    seed, seed_digest = binding.read(args.seed), binding.sha(args.seed)
    diagnosis, diagnosis_digest = binding.read(args.broader_diagnosis), binding.sha(args.broader_diagnosis)
    if (seed["schema"] != old_producer.SCHEMA
            or seed["executed_producer_sha256"] != binding.sha(old_producer.__file__)
            or seed["verified"] is not False or seed["new_geometric_payments"] != 0
            or seed["candidate_whole_roots_removed"] != 0
            or len(seed["alternative_supports"]) != 32
            or seed["modules"][linux(Path(forest.prior.__file__))] != binding.sha(forest.prior.__file__)
            or diagnosis["schema"] != "N26-unaccepted-broader-positive-original-rod-signed-leaf-diagnosis-v1"
            or diagnosis["old_arithmetic_forest_sha256"] != seed_digest
            or diagnosis["executed_probe_sha256"] != binding.sha(broad_producer.__file__)
            or diagnosis["broader_suggestion_module_sha256"] != binding.sha(broader.__file__)
            or diagnosis["verified"] is not False or diagnosis["new_geometric_payments"] != 0):
        raise ValueError("extended continuation changed actual old forest/new proposal or scope")
    accepted = binding.read(args.source / "VERIFIED.json")
    for name, digest in seed["source_file_sha256"].items():
        if binding.sha(args.source / name) != digest or accepted["files"][name] != digest:
            raise ValueError("extended continuation changed actual source/root/history DATA")
    row = next(row for row in binding.read(args.source / "PENDING-ANGLES.json")
               if row["index"] == seed["source_OPEN_index"])
    if row != seed["actual_source_closed_box"] or row != diagnosis["actual_source_closed_box"]:
        raise ValueError("extended continuation changed whole-root ownership")
    arcs = binding.force.load_trig(args.resource)[0]
    previous, old_pending, old_ledger = forest.prior.replay(
        original, kernel, arcs, row, seed["nodes"], seed["alternative_supports"])
    if (previous != seed["arithmetic_result"] or old_pending != seed["pending_closed_leaf_boxes"]
            or old_ledger != seed["arithmetic_ledger"]):
        raise ValueError("entire old forest and every strict leaf did not reconstruct")
    nodes, supports = deepcopy(seed["nodes"]), deepcopy(seed["alternative_supports"])
    pending_by_index = {leaf["index"]: leaf for leaf in old_pending}
    seeded = set()
    for item in diagnosis["results"]:
        strict = [trial for trial in item["broader_support_trials"]
                  if trial["strict_actual_closed_leaf_exclusion"]]
        if not strict:
            continue
        index = item["old_OPEN_leaf_index"]
        if (type(index) is not int or index in seeded or index not in pending_by_index
                or item["actual_closed_leaf"] != pending_by_index[index]
                or nodes[index] != {"kind": "OPEN"}):
            raise ValueError("broader proposal changed a real old OPEN domain")
        trial = max(strict, key=lambda value: F(value["signed_arithmetic_diagnosis"][
            "exact_arithmetic_result"]["strict_radius_margin"]))
        leaf = pending_by_index[index]
        checked = forest.prior.signed.bound(
            original["reference"], trial["NEW_positive_support"], original["matrix"],
            leaf["lower"], leaf["upper"], trial["NEW_signed_certificate"], original["radius"], arcs)
        if (checked != trial["signed_arithmetic_diagnosis"]["exact_arithmetic_result"]
                or not checked["arithmetic_strict_target_test_passed"]):
            raise ValueError("actual broad closed-leaf proposal did not reconstruct")
        support_index = len(supports)
        supports.append(deepcopy(trial["NEW_positive_support"]))
        nodes[index] = {"kind": forest.KIND, "support_index": support_index,
                        "certificate": deepcopy(trial["NEW_signed_certificate"])}
        seeded.add(index)
    print(json.dumps({
        "previous_actual_forest_replayed_and_three_broad_leaves_seeded": True,
        "old_nodes": len(seed["nodes"]), "seeded_NEW_strict_leaves": sorted(seeded),
        "verified": False, "new_geometric_payments": 0}), flush=True)
    base = forest.prior.prior
    levels = {0: 0}
    for index, node in enumerate(nodes):
        if node["kind"] == "SPLIT":
            for child in node["children"]:
                levels[child] = levels[index]+1
    queue = deque((leaf["index"], list(map(F, leaf["lower"])), list(map(F, leaf["upper"])),
                   levels[leaf["index"]]) for leaf in old_pending if leaf["index"] not in seeded)
    tiny = [tuple(map(F, pair)) for pair in original["cap"]["known_candidate_tiny_angle_cells"]]
    reference = base.tighten(original["matrix"], [a for a, _ in tiny], [b for _, b in tiny])[0]
    root_box = base.tighten(original["matrix"], row["sharp_lower"], row["sharp_upper"])
    tight = [axis for axis, (a, b) in enumerate(zip(*root_box)) if b-a <= F(1, 10**7)]
    free = [axis for axis in range(15) if axis not in tight]
    checks = 0
    while queue and checks < args.checks:
        index, lower, upper, depth = queue.popleft()
        if nodes[index] != {"kind": "OPEN"}:
            raise ValueError("extended continuation would overwrite a previously proved node")
        checks += 1
        box = base.tighten(original["matrix"], lower, upper)
        if box is None:
            nodes[index] = {"kind": "EMPTY"}
            continue
        lower, upper = box
        if max(max(abs(a-r), abs(b-r)) for a, b, r in zip(lower, upper, reference)) < F(1, 500000):
            try:
                base.local.local_proof(original, lower, upper)
            except ValueError:
                pass
            else:
                nodes[index] = {"kind": "LOCAL"}
                continue
        old = base.direct_bound(kernel, lower, upper, original["radius"], arcs)
        if old["radius_conditional_whole_angle_box_excluded"]:
            nodes[index] = {"kind": "ORIGINAL-ENERGY"}
            continue
        point = [(a+b)/2 for a, b in zip(lower, upper)]
        ordered = sorted(range(len(supports)), key=lambda support_index: sum(
            (float(a)-float(F(b)))**2 for a, b in zip(
                point, supports[support_index]["suggestion_point_turns"])))
        for support_index in ordered[:args.existing_support_tries]:
            certificate, diagnostic = suggestion.suggest(
                original, supports[support_index], box, point, tight, arcs)
            if (certificate is not None and diagnostic["exact_arithmetic_result"][
                    "arithmetic_strict_target_test_passed"]):
                nodes[index] = {"kind": forest.KIND, "support_index": support_index,
                                "certificate": certificate}
                break
        if nodes[index]["kind"] == "OPEN" and len(supports)+3 <= args.max_supports:
            trials = []
            for support, _, _ in broader.suggest(
                    original, kernel, point, args.iterations, args.log_spread):
                certificate, diagnostic = suggestion.suggest(original, support, box, point, tight, arcs)
                if certificate is not None:
                    trials.append((support, certificate, diagnostic["exact_arithmetic_result"]))
            if trials:
                support, certificate, result = max(trials, key=lambda trial: F(trial[2]["strict_radius_margin"]))
                # Retain only the exact best candidate, not every numerical try.
                support_index = len(supports)
                supports.append(support)
                if result["arithmetic_strict_target_test_passed"]:
                    nodes[index] = {"kind": forest.KIND, "support_index": support_index,
                                    "certificate": certificate}
        if nodes[index]["kind"] == "OPEN":
            axes = [axis for axis in free if lower[axis] < upper[axis]]
            if depth < args.depth and axes:
                axis = max(axes, key=lambda axis: upper[axis]-lower[axis])
                cut = (lower[axis]+upper[axis])/2
                children = [len(nodes), len(nodes)+1]
                nodes.extend(({"kind": "OPEN"}, {"kind": "OPEN"}))
                nodes[index] = {"kind": "SPLIT", "axis": axis, "mid": str(cut), "children": children}
                left, right = list(upper), list(lower)
                left[axis], right[axis] = cut, cut
                queue.extend(((children[0], list(lower), left, depth+1),
                              (children[1], right, list(upper), depth+1)))
        if checks % 8 == 0:
            print(json.dumps({
                "new_checks": checks, "nodes": len(nodes),
                "NEW_signed_leaves": sum(node["kind"] == forest.KIND for node in nodes),
                "OPEN_leaves": sum(node["kind"] == "OPEN" for node in nodes),
                "positive_supports": len(supports), "verified": False,
                "new_geometric_payments": 0}), flush=True)
    if (supports[:len(seed["alternative_supports"])] != seed["alternative_supports"] or any(
            old["kind"] != "OPEN" and old != nodes[index] for index, old in enumerate(seed["nodes"]))):
        raise AssertionError("extended continuation changed an old support or proof node")
    result, pending, ledger = forest.replay(original, kernel, arcs, row, nodes, supports)
    for path, digest in ((args.seed, seed_digest), (args.broader_diagnosis, diagnosis_digest),
                         (args.current_audit, current_digest)):
        if binding.sha(path) != digest:
            raise ValueError("extended source/seed/current snapshot changed during continuation")
    for name, digest in seed["source_file_sha256"].items():
        if binding.sha(args.source / name) != digest:
            raise ValueError("actual source/history DATA changed during extended continuation")
    report = {
        "schema": SCHEMA, "verified": False, "actual_current_audit_sha256": current_digest,
        "actual_latest_candidate_layer_identity_only": layer,
        "source_OPEN_index": row["index"], "actual_source_closed_box": row,
        "source_file_sha256": seed["source_file_sha256"],
        "old_arithmetic_forest_sha256": seed_digest, "old_arithmetic_forest_path": linux(args.seed),
        "all_previous_non_OPEN_nodes_and_positive_supports_preserved_identically": True,
        "actual_formal_source_partial_forests_DATA_not_reset": True,
        "nodes": nodes, "alternative_supports": supports,
        "arithmetic_result": result, "pending_closed_leaf_boxes": pending, "arithmetic_ledger": ledger,
        "new_diagnostic_checks": checks, "seeded_exact_broad_leaves": sorted(seeded),
        "broader_diagnosis_sha256": diagnosis_digest,
        "complete_latest_source_model_history_geometry_admission_NOT_performed": True,
        "NEW_extended_support_mode_NOT_admitted_by_running_mixed_or_product_checker": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "executed_producer_sha256": binding.sha(__file__),
        "modules": {linux(Path(module.__file__)): binding.sha(module.__file__)
                    for module in (forest, forest.prior, forest.prior.signed, broader, codec, identity, suggestion)},
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({
        "extended_positive_support_continuation_completed": True,
        "nodes": result["nodes"], "counts": result["counts"], "retained_OPEN_leaves": len(pending),
        "arithmetic_entire_root_lower_bound_cover_completed":
            result["arithmetic_entire_root_lower_bound_cover_completed"],
        "verified": False, "new_geometric_payments": 0}), flush=True)


if __name__ == "__main__":
    main()
