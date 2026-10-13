"""Reconstruct the actual continued product forest, without geometry admission.

These controls replay all real closed leaves, check exact old-node retention,
and exercise real partition, product and original LOCAL rejection paths.
The fixed arithmetic resource is DATA only, never a source/history shortcut.
"""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_difference_product_candidate_forest as forest
import n26_typed_arithmetic_context as codec
import continue_candidate_difference_product_forest as producer
import propose_candidate_difference_product_forest as initial
import probe_candidate_positive_curvature_hull as fixed
import verify_conditional_force_stage as binding


SCHEMA = "N26-independent-actual-product-forest-arithmetic-controls-v1"


def reconstruction(original, kernel, arcs, row, record):
    if (record["actual_source_closed_box"] != row
            or record["source_OPEN_index"] != row["index"]
            or record["verified"] is not False
            or record["new_geometric_payments"] != 0
            or record["candidate_whole_roots_removed"] != 0
            or record["complete_latest_model_source_ownership_replay_NOT_performed"] is not True):
        raise ValueError("product arithmetic diagnostic changed exact ownership or admission scope")
    result, pending, ledger = forest.replay(original, kernel, arcs, row, record["nodes"])
    if (result != record["arithmetic_result"]
            or pending != record["pending_closed_leaf_boxes"]
            or ledger != record["arithmetic_ledger"]):
        raise ValueError("actual product forest result or exact closed-leaf ledger did not reconstruct")
    return result, pending, ledger


def rejection_controls(original, kernel, arcs, row, record):
    nodes = record["nodes"]
    leaves = forest.partition(original["matrix"], row, nodes, forest.independently_contract, True)
    energy = next(leaf for leaf in leaves if leaf["kind"] == "PRODUCT-ENERGY")
    local = next(leaf for leaf in leaves if leaf["kind"] == "LOCAL")
    certificate = nodes[energy["index"]]["certificate"]
    rejected = []

    def reject(label, call):
        try:
            call()
        except (ValueError, KeyError, TypeError, IndexError):
            rejected.append(label)
        else:
            raise AssertionError("invalid actual product-forest control accepted: " + label)

    def changed_partition(mutation):
        bad = deepcopy(nodes)
        mutation(bad)
        forest.partition(original["matrix"], row, bad, forest.independently_contract, True)

    split_index = next(index for index, node in enumerate(nodes) if node["kind"] == "SPLIT")
    reject("actual-root-one-closed-half-omitted", lambda: changed_partition(
        lambda bad: bad[split_index].update(children=bad[split_index]["children"][:1])))
    reject("actual-root-shared-half-identified", lambda: changed_partition(
        lambda bad: bad[split_index].update(children=[bad[split_index]["children"][0]] * 2)))
    reject("actual-root-unreachable-hidden-node", lambda: changed_partition(
        lambda bad: bad.append({"kind": "OPEN"})))
    reject("actual-root-nonempty-energy-region-called-EMPTY", lambda: changed_partition(
        lambda bad: bad.__setitem__(energy["index"], {"kind": "EMPTY"})))
    reject("actual-root-unsupported-curvature-mode", lambda: changed_partition(
        lambda bad: bad.__setitem__(energy["index"], {"kind": "UNPROVED-PRODUCT"})))
    reject("actual-root-split-has-unknown-payment-fields", lambda: changed_partition(
        lambda bad: bad[split_index].update(fake_payment=True)))

    def changed_energy(mutation):
        bad = deepcopy(certificate)
        mutation(bad)
        forest.product.bound(
            kernel, original["matrix"], energy["lower"], energy["upper"],
            bad, original["radius"], arcs)

    reject("actual-energy-negative-product-multiplier", lambda: changed_energy(
        lambda bad: bad["products"][0].update(multiplier="-1")))
    reject("actual-energy-missing-reference-linear-product-definition", lambda: changed_energy(
        lambda bad: bad["products"][0].pop("second_constraint")))
    reject("actual-energy-duplicate-slack-product", lambda: changed_energy(
        lambda bad: bad["products"].append(deepcopy(bad["products"][0]))))
    reject("actual-energy-all-products-omitted", lambda: changed_energy(
        lambda bad: bad.update(products=[])))
    reject("actual-energy-nonpositive-corrected-curvature", lambda: changed_energy(
        lambda bad: bad.update(signed_eta=["-100000000000000000000"] * 15)))
    reject("actual-energy-unknown-certificate-proof-field", lambda: changed_energy(
        lambda bad: bad.update(reference_product_constant_falsely_zero=True)))
    reject("actual-LOCAL-full-root-substituted-for-closed-leaf", lambda:
           forest.original_forest.local_proof(
               original, list(map(F, row["sharp_lower"])), list(map(F, row["sharp_upper"]))))

    # This is a positive LOCAL replay, not an emptiness certificate.
    local_result = forest.original_forest.local_proof(
        original, list(map(F, local["lower"])), list(map(F, local["upper"])))
    if F(local_result["strict_original_LOCAL_entry_margin"]) <= 0:
        raise AssertionError("actual product-forest LOCAL entry has no original strict margin")
    tiny = [tuple(map(F, pair))
            for pair in original["cap"]["known_candidate_tiny_angle_cells"]]
    tiny_box = forest.tighten(original["matrix"], [a for a, _ in tiny], [c for _, c in tiny])
    tiny_result = forest.product.bound(
        kernel, original["matrix"], *tiny_box, certificate, original["radius"], arcs)
    if tiny_result["arithmetic_strict_target_test_passed"]:
        raise AssertionError("actual product certificate falsely excludes the feasible tiny candidate")
    return rejected, {
        "original_LOCAL_closed_leaf_replayed": True,
        "original_LOCAL_result": local_result,
        "known_feasible_tiny_candidate_not_strictly_excluded": True,
        "tiny_candidate_arithmetic_result": tiny_result,
    }


def main():
    parser = argparse.ArgumentParser()
    for name in ("resource", "resource-replay", "source", "seed", "diagnosis", "report"):
        parser.add_argument("--" + name, type=Path, required=True)
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
        raise ValueError("actual product controls changed fixed arithmetic DATA identity")
    original_model = codec.gate(binding.read(args.resource / "CONTEXT.json")["typed_context"])
    original, kernel = original_model["original"], original_model["original_kernel"]
    seed, record = binding.read(args.seed), binding.read(args.diagnosis)
    seed_digest, diagnosis_digest = binding.sha(args.seed), binding.sha(args.diagnosis)
    if (record["schema"] !=
            "N26-unaccepted-continued-root-difference-product-LOCAL-forest-diagnosis-v1"
            or record["executed_producer_sha256"] != binding.sha(producer.__file__)
            or seed["executed_producer_sha256"] != binding.sha(initial.__file__)
            or record["old_unadmitted_forest_sha256"] != seed_digest
            or record["all_previous_non_OPEN_nodes_preserved_identically"] is not True
            or record["new_product_mode_NOT_admitted_by_running_mixed_checker"] is not True):
        raise ValueError("product controls changed actual diagnostic executor or old forest lineage")
    for item in (seed, record):
        for module in (forest, forest.product):
            if item["modules"][linux(Path(module.__file__))] != binding.sha(module.__file__):
                raise ValueError("product arithmetic controls used changed exact modules")
    accepted = binding.read(args.source / "VERIFIED.json")
    source_digests = seed["source_file_sha256"]
    for name, digest in source_digests.items():
        if binding.sha(args.source / name) != digest or accepted["files"][name] != digest:
            raise ValueError("product controls changed actual source/root/history DATA")
    rows = binding.read(args.source / "PENDING-ANGLES.json")
    row = next(row for row in rows if row["index"] == record["source_OPEN_index"])
    if row != seed["actual_source_closed_box"]:
        raise ValueError("old product forest and new continuation own different actual roots")
    if len(record["nodes"]) < len(seed["nodes"]) or any(
            old["kind"] != "OPEN" and old != record["nodes"][index]
            for index, old in enumerate(seed["nodes"])):
        raise ValueError("product continuation changed a previous non-OPEN proof node")
    arcs = binding.force.load_trig(args.resource)[0]
    result, pending, ledger = reconstruction(original, kernel, arcs, row, record)
    if pending or not result["arithmetic_entire_root_lower_bound_cover_completed"]:
        raise ValueError("actual root arithmetic forest still has unproved closed leaves")
    print(json.dumps({"actual_entire_root_arithmetic_reconstructed": True,
                      "root": row["index"], "nodes": len(record["nodes"]),
                      "verified": False, "new_geometric_payments": 0}), flush=True)
    negative, positive = rejection_controls(original, kernel, arcs, row, record)
    if len(negative) != 13:
        raise ValueError("actual product-forest controls omitted a required rejection")
    for path, digest in ((args.seed, seed_digest), (args.diagnosis, diagnosis_digest)):
        if binding.sha(path) != digest:
            raise ValueError("product seed or diagnosis changed during actual arithmetic controls")
    for name, digest in source_digests.items():
        if binding.sha(args.source / name) != digest:
            raise ValueError("actual source/history DATA changed during product controls")
    report = {
        "schema": SCHEMA, "verified": False,
        "source_OPEN_index": row["index"], "actual_source_closed_box": row,
        "diagnosis_sha256": diagnosis_digest, "old_forest_sha256": seed_digest,
        "all_previous_non_OPEN_nodes_preserved_identically": True,
        "actual_entire_closed_root_arithmetic_reconstruction_passed": True,
        "actual_arithmetic_result": result,
        "rejection_controls_passed": negative, "positive_arithmetic_controls": positive,
        "arithmetic_only_NOT_complete_latest_model_source_history_or_geometry_acceptance": True,
        "new_product_mode_NOT_admitted_by_running_mixed_checker": True,
        "source_file_sha256": source_digests,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "tested_modules": {
            Path(module.__file__).name: binding.sha(module.__file__)
            for module in (forest, forest.product, forest.original_forest, codec)},
        "executed_test_sha256": binding.sha(__file__),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2) + "\n")
    print(json.dumps({
        "actual_root_product_arithmetic_controls_completed": True,
        "actual_rejection_controls": len(negative), "verified": False,
        "new_geometric_payments": 0}), flush=True)


if __name__ == "__main__":
    main()
