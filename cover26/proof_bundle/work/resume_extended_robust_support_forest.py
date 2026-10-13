"""Resume a preserved expanded forest using exact robust-reference bounds."""

import argparse
from collections import deque
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import continue_extended_positive_support_forest as initial
import n26_broad_positive_support_suggestion as broader
import n26_current_candidate_layer_identity as identity
import n26_extended_signed_support_forest as forest
import n26_typed_arithmetic_context as codec
import probe_candidate_positive_curvature_hull as fixed
import probe_robust_positive_support_references as robust
import verify_conditional_force_stage as binding


SCHEMA = "N26-unaccepted-resumed-extended-robust-support-forest-diagnosis-v1"


def descendants(nodes, root):
    if type(root) is not int or not 0 <= root < len(nodes):
        raise ValueError("robust supplement names an invalid old ancestor")
    result, queue = set(), [root]
    for index in queue:
        if index in result:
            raise ValueError("robust supplement ancestry repeats a node")
        result.add(index)
        if nodes[index]["kind"] == "SPLIT":
            queue.extend(nodes[index]["children"])
    return result


def main():
    parser = argparse.ArgumentParser()
    for name in ("resource", "resource-replay", "current-audit", "source", "seed",
                 "robust-diagnosis", "robust-controls", "report"):
        parser.add_argument("--"+name, type=Path, required=True)
    parser.add_argument("--checks", type=int, default=63)
    parser.add_argument("--depth", type=int, default=208)
    parser.add_argument("--max-supports", type=int, default=256)
    parser.add_argument("--existing-support-tries", type=int, default=3)
    parser.add_argument("--iterations", type=int, default=180)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    if args.checks <= 0 or not 32 <= args.max_supports <= forest.MAX_SUPPORTS:
        raise ValueError("invalid robust expanded forest limits")
    resource = binding.read(args.resource / "VERIFIED.json")
    if (binding.sha(args.resource / "VERIFIED.json") != fixed.RESOURCE_SHA
            or binding.sha(args.resource_replay) != fixed.RESOURCE_SHA
            or binding.read(args.resource_replay) != resource
            or resource["resource_acceptance_is_not_a_faster_current_source_interface"] is not True
            or resource["context_is_not_a_current_candidate_source_or_a_seed_history_substitute"] is not True
            or binding.sha(args.resource / "CONTEXT.json") != resource["files"]["CONTEXT.json"]
            or binding.sha(codec.__file__) != resource["files"]["n26_typed_arithmetic_context.py"]):
        raise ValueError("robust resume changed fixed arithmetic DATA identity")
    model = codec.gate(binding.read(args.resource / "CONTEXT.json")["typed_context"])
    original, kernel = model["original"], model["original_kernel"]
    current_digest = binding.sha(args.current_audit)
    current = binding.read(args.current_audit)
    layer = identity.gate(current, current_digest, args.source)
    if F(original["radius"]) != F(current["r_strict_interval"][1]):
        raise ValueError("robust resume changed actual same-root radius")
    seed, seed_digest = binding.read(args.seed), binding.sha(args.seed)
    diagnosis, diagnosis_digest = binding.read(args.robust_diagnosis), binding.sha(args.robust_diagnosis)
    controls = binding.read(args.robust_controls)
    if (seed["schema"] != initial.SCHEMA
            or seed["executed_producer_sha256"] != binding.sha(initial.__file__)
            or seed["verified"] is not False or seed["new_geometric_payments"] != 0
            or seed["candidate_whole_roots_removed"] != 0
            or seed["all_previous_non_OPEN_nodes_and_positive_supports_preserved_identically"] is not True
            or diagnosis["old_arithmetic_forest_sha256"] != seed["old_arithmetic_forest_sha256"]
            or diagnosis["executed_probe_sha256"] != binding.sha(robust.__file__)
            or diagnosis["verified"] is not False or diagnosis["new_geometric_payments"] != 0
            or controls["diagnosis_sha256"] != diagnosis_digest
            or controls["verified"] is not False or controls["new_geometric_payments"] != 0
            or controls["tested_signed_module_sha256"] != binding.sha(forest.prior.signed.__file__)):
        raise ValueError("robust resume changed old forest, supplement lineage, controls or scope")
    for module in (forest, forest.prior, forest.prior.signed):
        if seed["modules"][linux(Path(module.__file__))] != binding.sha(module.__file__):
            raise ValueError("robust resume changed old exact forest arithmetic")
    accepted = binding.read(args.source / "VERIFIED.json")
    for name, digest in seed["source_file_sha256"].items():
        if binding.sha(args.source / name) != digest or accepted["files"][name] != digest:
            raise ValueError("robust resume changed actual source/root/history DATA")
    row = next(row for row in binding.read(args.source / "PENDING-ANGLES.json")
               if row["index"] == seed["source_OPEN_index"])
    if row != seed["actual_source_closed_box"]:
        raise ValueError("robust resume changed actual whole-root ownership")
    arcs = binding.force.load_trig(args.resource)[0]
    previous, old_pending, old_ledger = forest.replay(
        original, kernel, arcs, row, seed["nodes"], seed["alternative_supports"])
    if (previous != seed["arithmetic_result"] or old_pending != seed["pending_closed_leaf_boxes"]
            or old_ledger != seed["arithmetic_ledger"]):
        raise ValueError("all old expanded forest nodes, supports and exact leaves failed reconstruction")
    nodes, supports = deepcopy(seed["nodes"]), deepcopy(seed["alternative_supports"])
    seeded, supplements = set(), []
    for item in diagnosis["results"]:
        candidates = [test for test in item["tests"] if test["strict_actual_closed_leaf_exclusion"]]
        if not candidates:
            continue
        parent_index = item["old_OPEN_leaf_index"]
        branch = descendants(nodes, parent_index)
        ancestor_box = item["actual_closed_leaf"]
        trial = max(candidates, key=lambda test: F(test["signed_arithmetic_diagnosis"][
            "exact_arithmetic_result"]["strict_radius_margin"]))
        support, certificate = trial["NEW_positive_support"], trial["NEW_signed_certificate"]
        parent_check = forest.prior.signed.bound(
            original["reference"], support, original["matrix"], ancestor_box["lower"],
            ancestor_box["upper"], certificate, original["radius"], arcs)
        if (parent_check != trial["signed_arithmetic_diagnosis"]["exact_arithmetic_result"]
                or not parent_check["arithmetic_strict_target_test_passed"]):
            raise ValueError("whole closed ancestor supplement did not reconstruct")
        support_index = len(supports)
        if support_index >= args.max_supports:
            raise ValueError("robust supplement exceeds explicit expanded table")
        supports.append(deepcopy(support))
        covered = []
        for leaf in old_pending:
            index = leaf["index"]
            if index not in branch:
                continue
            if any(F(a) < F(pa) or F(b) > F(pb)
                   for a, b, pa, pb in zip(leaf["lower"], leaf["upper"],
                                          ancestor_box["lower"], ancestor_box["upper"])):
                raise ValueError("old OPEN descendant escaped the robust ancestor's exact closed box")
            checked = forest.prior.signed.bound(
                original["reference"], support, original["matrix"], leaf["lower"], leaf["upper"],
                certificate, original["radius"], arcs)
            if checked["arithmetic_strict_target_test_passed"]:
                if nodes[index] != {"kind": "OPEN"}:
                    raise ValueError("robust supplement would overwrite an old proof")
                nodes[index] = {"kind": forest.KIND, "support_index": support_index,
                                "certificate": deepcopy(certificate)}
                seeded.add(index)
                covered.append(index)
        supplements.append({"old_ancestor_node": parent_index,
                            "old_ancestor_SPLIT_kept_identically": nodes[parent_index] == seed["nodes"][parent_index],
                            "actual_OPEN_descendants_freshly_lower_bounded": covered})
    print(json.dumps({"previous_entire_forest_replayed": True, "old_nodes": len(seed["nodes"]),
                      "robust_descendant_leaves_seeded": sorted(seeded), "verified": False,
                      "new_geometric_payments": 0}), flush=True)
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
            raise ValueError("robust resume would overwrite an old nonOPEN proof")
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
        center = [(a+b)/2 for a, b in zip(lower, upper)]
        ordered = sorted(range(len(supports)), key=lambda support_index: sum(
            (float(a)-float(F(b)))**2 for a, b in zip(
                center, supports[support_index]["suggestion_point_turns"])))
        attempted = []
        for support_index in ordered[:args.existing_support_tries]:
            trial = robust.test_reference(original, supports[support_index], box, center, tight, arcs)
            attempted.append(trial)
            if trial["strict_actual_closed_leaf_exclusion"]:
                nodes[index] = {"kind": forest.KIND, "support_index": support_index,
                                "certificate": trial["NEW_signed_certificate"]}
                break
        if nodes[index]["kind"] == "OPEN" and len(supports)+3 <= args.max_supports:
            usable = [trial for trial in attempted if trial["NEW_signed_certificate"] is not None]
            worst = center if not usable else list(map(F, max(
                usable, key=lambda trial: F(trial["signed_arithmetic_diagnosis"][
                    "exact_arithmetic_result"]["strict_radius_margin"]))["reference_turns"]))
            fresh = []
            for support, _, _ in broader.suggest(original, kernel, worst, args.iterations, 3):
                trial = robust.test_reference(original, support, box, worst, tight, arcs)
                if trial["NEW_signed_certificate"] is not None:
                    fresh.append(trial)
            if fresh:
                trial = max(fresh, key=lambda item: F(item["signed_arithmetic_diagnosis"][
                    "exact_arithmetic_result"]["strict_radius_margin"]))
                support_index = len(supports)
                supports.append(trial["NEW_positive_support"])
                if trial["strict_actual_closed_leaf_exclusion"]:
                    nodes[index] = {"kind": forest.KIND, "support_index": support_index,
                                    "certificate": trial["NEW_signed_certificate"]}
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
            print(json.dumps({"new_checks": checks, "nodes": len(nodes),
                              "NEW_signed_leaves": sum(node["kind"] == forest.KIND for node in nodes),
                              "OPEN_leaves": sum(node["kind"] == "OPEN" for node in nodes),
                              "positive_supports": len(supports), "verified": False,
                              "new_geometric_payments": 0}), flush=True)
    if (supports[:len(seed["alternative_supports"])] != seed["alternative_supports"] or any(
            old["kind"] != "OPEN" and old != nodes[index] for index, old in enumerate(seed["nodes"]))):
        raise AssertionError("robust resume changed an old support, SPLIT or proved leaf")
    result, pending, ledger = forest.replay(original, kernel, arcs, row, nodes, supports)
    for path, digest in ((args.seed, seed_digest), (args.robust_diagnosis, diagnosis_digest),
                         (args.current_audit, current_digest)):
        if binding.sha(path) != digest:
            raise ValueError("old forest/current/supplement changed during robust resume")
    for name, digest in seed["source_file_sha256"].items():
        if binding.sha(args.source / name) != digest:
            raise ValueError("actual source/history DATA changed during robust resume")
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
        "new_diagnostic_checks": checks, "robust_ancestor_supplement_replays": supplements,
        "robust_diagnosis_sha256": diagnosis_digest,
        "complete_latest_source_model_history_geometry_admission_NOT_performed": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "executed_producer_sha256": binding.sha(__file__),
        "modules": {linux(Path(module.__file__)): binding.sha(module.__file__)
                    for module in (forest, forest.prior, forest.prior.signed, broader, codec, identity, robust)},
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({"robust_expanded_forest_resume_completed": True, "nodes": result["nodes"],
                      "counts": result["counts"], "retained_OPEN_leaves": len(pending),
                      "arithmetic_entire_root_lower_bound_cover_completed":
                          result["arithmetic_entire_root_lower_bound_cover_completed"],
                      "verified": False, "new_geometric_payments": 0}), flush=True)


if __name__ == "__main__":
    main()
