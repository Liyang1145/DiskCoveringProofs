"""Actual preserved whole-root partition reconstruction; no geometry admission."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import continue_candidate_adaptive_signed_support_forest as producer
import n26_adaptive_signed_support_forest as forest
import n26_typed_arithmetic_context as codec
import probe_candidate_positive_curvature_hull as fixed
import verify_conditional_force_stage as binding


def main():
    parser = argparse.ArgumentParser()
    for name in ("resource", "resource-replay", "source", "seed", "diagnosis", "report"):
        parser.add_argument("--"+name, type=Path, required=True)
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
        raise ValueError("actual adaptive signed controls changed arithmetic DATA identity")
    model = codec.gate(binding.read(args.resource / "CONTEXT.json")["typed_context"])
    original, kernel = model["original"], model["original_kernel"]
    seed, diagnosis = binding.read(args.seed), binding.read(args.diagnosis)
    seed_digest, diagnosis_digest = binding.sha(args.seed), binding.sha(args.diagnosis)
    if (diagnosis["executed_producer_sha256"] != binding.sha(producer.__file__)
            or diagnosis["old_arithmetic_forest_sha256"] != seed_digest
            or diagnosis["verified"] is not False or diagnosis["new_geometric_payments"] != 0
            or diagnosis["candidate_whole_roots_removed"] != 0
            or diagnosis["all_previous_non_OPEN_nodes_and_positive_supports_preserved_identically"] is not True):
        raise ValueError("actual signed forest controls changed diagnostic producer, history or scope")
    for module in (forest, forest.prior, forest.signed):
        if diagnosis["modules"][linux(Path(module.__file__))] != binding.sha(module.__file__):
            raise ValueError("actual signed forest controls changed exact arithmetic")
    accepted = binding.read(args.source / "VERIFIED.json")
    for name, digest in diagnosis["source_file_sha256"].items():
        if binding.sha(args.source / name) != digest or accepted["files"][name] != digest:
            raise ValueError("actual signed forest controls changed source/root/history DATA")
    row = next(row for row in binding.read(args.source / "PENDING-ANGLES.json")
               if row["index"] == diagnosis["source_OPEN_index"])
    if row != diagnosis["actual_source_closed_box"] or row != seed["actual_source_closed_box"]:
        raise ValueError("actual signed forest controls clipped original whole-root ownership")
    if (len(diagnosis["nodes"]) < len(seed["nodes"])
            or any(old["kind"] != "OPEN" and old != diagnosis["nodes"][index]
                   for index, old in enumerate(seed["nodes"]))
            or diagnosis["alternative_supports"][:len(seed["alternative_supports"])]
            != seed["alternative_supports"]):
        raise ValueError("actual signed continuation reset an old proof node or positive support")
    arcs = binding.force.load_trig(args.resource)[0]
    result, pending, ledger = forest.replay(
        original, kernel, arcs, row, diagnosis["nodes"], diagnosis["alternative_supports"])
    if (result != diagnosis["arithmetic_result"]
            or pending != diagnosis["pending_closed_leaf_boxes"]
            or ledger != diagnosis["arithmetic_ledger"]):
        raise ValueError("entire actual adaptive signed partition, strict leaves and OPENs did not reconstruct")
    nodes = diagnosis["nodes"]
    negative = []

    def reject(label, call):
        try:
            call()
        except (ValueError, KeyError, TypeError, IndexError):
            negative.append(label)
        else:
            raise AssertionError("invalid actual adaptive signed forest accepted: "+label)

    def changed_partition(mutation):
        bad = deepcopy(nodes)
        mutation(bad)
        forest.partition(original["matrix"], row, bad, forest.prior.independently_contract, True)

    split_index = next(index for index, node in enumerate(nodes) if node["kind"] == "SPLIT")
    reject("actual-signed-root-lost-closed-half", lambda: changed_partition(
        lambda bad: bad[split_index].update(children=bad[split_index]["children"][:1])))
    reject("actual-signed-root-identified-closed-halves", lambda: changed_partition(
        lambda bad: bad[split_index].update(children=[bad[split_index]["children"][0]]*2)))
    reject("actual-signed-root-hidden-unreachable-node", lambda: changed_partition(
        lambda bad: bad.append({"kind": "OPEN"})))
    reject("actual-signed-root-unknown-geometry-mode", lambda: changed_partition(
        lambda bad: bad.__setitem__(1, {"kind": "UNKNOWN-SUPPORT"})))
    first = next(leaf for leaf in ledger if leaf["kind"] == forest.KIND)
    support = diagnosis["alternative_supports"][first["support_index"]]
    certificate = first["certificate"]

    def changed_certificate(mutation):
        bad = deepcopy(certificate)
        mutation(bad)
        forest.signed.bound(original["reference"], support, original["matrix"],
                            first["lower"], first["upper"], bad, original["radius"], arcs)

    reject("actual-signed-energy-negative-dual", lambda: changed_certificate(
        lambda bad: bad.update(difference_dual={"q": 1, "terms": [[0, 1, "-1"]]})))
    reject("actual-signed-energy-nonpositive-LDL", lambda: changed_certificate(
        lambda bad: bad.update(signed_eta=["-1000000000000"]*15)))
    reject("actual-signed-energy-false-original-kernel-mode", lambda: changed_certificate(
        lambda bad: bad.update(original_fixed_kernel_claim=True)))
    if not pending:
        raise ValueError("this partial-forest control fixture requires actual retained OPENs")
    open_index = pending[0]["index"]
    omitted = deepcopy(nodes)
    omitted[open_index] = {"kind": "EMPTY"}
    reject("actual-unproved-OPEN-region-falsely-called-empty", lambda:
           forest.partition(original["matrix"], row, omitted, forest.prior.independently_contract, True))
    tiny = original["cap"]["known_candidate_tiny_angle_cells"]
    for fresh in forest.prior.support_gate(original, diagnosis["alternative_supports"]):
        check = forest.prior.direct_bound(
            fresh, [a for a, _ in tiny], [b for _, b in tiny], original["radius"], arcs)
        if check["radius_conditional_whole_angle_box_excluded"]:
            raise AssertionError("an actual adaptive positive support excludes the feasible tiny candidate")
    if binding.sha(args.seed) != seed_digest or binding.sha(args.diagnosis) != diagnosis_digest:
        raise ValueError("actual adaptive diagnostics changed during independent reconstruction")
    report = {
        "schema": "N26-independent-actual-adaptive-NEW-signed-forest-arithmetic-controls-v1",
        "entire_actual_source_root_partition_and_all_strict_leaves_reconstructed": True,
        "all_actual_OPEN_leaves_retained_identically": True,
        "all_previous_non_OPEN_nodes_and_supports_preserved_identically": True,
        "actual_arithmetic_result": result,
        "actual_rejection_controls_passed": negative,
        "all_NEW_positive_support_feasible_tiny_candidates_not_excluded": True,
        "diagnosis_sha256": diagnosis_digest, "old_forest_sha256": seed_digest,
        "verified": False, "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "complete_latest_source_model_history_geometry_gate_NOT_executed": True,
        "whole_root_still_unproved": bool(pending),
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "tested_forest_module_sha256": binding.sha(forest.__file__),
        "tested_signed_module_sha256": binding.sha(forest.signed.__file__),
        "executed_test_sha256": binding.sha(__file__),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({"actual_adaptive_signed_partial_forest_controls_completed": True,
                      "nodes": result["nodes"], "retained_OPEN_leaves": len(pending),
                      "actual_rejections": len(negative), "verified": False,
                      "new_geometric_payments": 0}), flush=True)


if __name__ == "__main__":
    main()
