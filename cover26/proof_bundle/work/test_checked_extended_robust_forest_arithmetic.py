"""Independent newest v6 reconstruction, retaining its fully checked v5 seed."""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import continue_checked_extended_robust_support_forest as producer
import n26_extended_signed_support_forest as forest
import n26_typed_arithmetic_context as codec
import probe_candidate_positive_curvature_hull as fixed
import test_extended_robust_support_forest_arithmetic as previous
import verify_conditional_force_stage as binding


SCHEMA = "N26-independent-actual-checked-extended-robust-forest-continuation-controls-v1"


def leaf_controls(original, kernel, arcs, record):
    energy, local, empty = 0, 0, 0
    for number, leaf in enumerate(record["arithmetic_ledger"], 1):
        if leaf["kind"] == forest.KIND:
            previous.independent.check(original, arcs, {
                "actual_closed_leaf": leaf,
                "NEW_positive_support": record["alternative_supports"][leaf["support_index"]],
                "NEW_signed_certificate": leaf["certificate"],
                "signed_arithmetic_diagnosis": {"exact_arithmetic_result": leaf["arithmetic_result"]},
            })
            energy += 1
        elif leaf["kind"] == "ORIGINAL-ENERGY":
            previous.original_sine_controls(original, kernel, arcs, leaf)
            energy += 1
        elif leaf["kind"] == "LOCAL":
            result = previous.BASE.local.local_proof(
                original, list(map(F, leaf["lower"])), list(map(F, leaf["upper"])))
            if (result != leaf["original_LOCAL_result"]
                    or F(result["strict_original_LOCAL_entry_margin"]) <= 0):
                raise ValueError("newest actual LOCAL leaf failed its unchanged original entry proof")
            local += 1
        elif leaf["kind"] == "EMPTY":
            empty += 1
        else:
            raise ValueError("newest checked robust continuation introduced an untested leaf mode")
        if number % 16 == 0:
            print(json.dumps({"actual_newest_independent_leaf_controls": number,
                              "total": len(record["arithmetic_ledger"]), "verified": False,
                              "new_geometric_payments": 0}), flush=True)
    return energy, local, empty


def main():
    parser = argparse.ArgumentParser()
    for name in ("resource", "resource-replay", "source", "seed", "seed-controls", "diagnosis", "report"):
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
        raise ValueError("newest checked robust controls changed fixed arithmetic DATA identity")
    model = codec.gate(binding.read(args.resource / "CONTEXT.json")["typed_context"])
    original, kernel = model["original"], model["original_kernel"]
    seed, record = binding.read(args.seed), binding.read(args.diagnosis)
    controls = binding.read(args.seed_controls)
    digests = {path: binding.sha(path) for path in (args.seed, args.seed_controls, args.diagnosis)}
    if (seed["schema"] != producer.previous_producer.SCHEMA
            or seed["executed_producer_sha256"] != binding.sha(producer.previous_producer.__file__)
            or record["schema"] != producer.SCHEMA
            or record["executed_producer_sha256"] != binding.sha(producer.__file__)
            or record["old_arithmetic_forest_sha256"] != digests[args.seed]
            or record["actual_seed_independent_arithmetic_controls_sha256"] != digests[args.seed_controls]
            or record["all_previous_proved_closed_leaf_ledgers_preserved_identically"] is not True
            or controls["schema"] != previous.SCHEMA
            or controls["executed_test_sha256"] != binding.sha(previous.__file__)
            or controls["diagnosis_sha256"] != digests[args.seed]
            or controls["latest_arithmetic_result"] != seed["arithmetic_result"]
            or controls["verified"] is not False or controls["new_geometric_payments"] != 0
            or controls["candidate_whole_roots_removed"] != 0
            or len(controls["actual_rejection_controls_passed"]) != 20
            or controls["actual_strict_leaf_count_independently_tested"] != len(seed["arithmetic_ledger"])):
        raise ValueError("newest actual robust forest changed checked seed, executor or zero-payment lineage")
    for data in (seed, record):
        for module in (forest, forest.prior, previous.independent.signed):
            if data["modules"][linux(Path(module.__file__))] != binding.sha(module.__file__):
                raise ValueError("newest robust controls used changed exact forest arithmetic")
    if record["modules"][linux(Path(previous.__file__))] != binding.sha(previous.__file__):
        raise ValueError("newest continuation changed its actual independent seed tester")
    accepted = binding.read(args.source / "VERIFIED.json")
    if (record["source_file_sha256"] != seed["source_file_sha256"]
            or controls["source_file_sha256"] != seed["source_file_sha256"]):
        raise ValueError("newest robust controls changed old actual source/history DATA bindings")
    for name, digest in seed["source_file_sha256"].items():
        if binding.sha(args.source / name) != digest or accepted["files"][name] != digest:
            raise ValueError("newest robust controls changed actual source/root/history DATA")
    row = next(row for row in binding.read(args.source / "PENDING-ANGLES.json")
               if row["index"] == record["source_OPEN_index"])
    for data in (seed, record):
        previous.scope_gate(data, row)
    retained_nodes, retained_supports, retained_leaves = previous.retention_gate(seed, record)
    arcs = binding.force.load_trig(args.resource)[0]
    previous.reconstruct(original, kernel, arcs, row, seed, "v5-independently-checked-seed")
    result, pending, ledger = previous.reconstruct(
        original, kernel, arcs, row, record, "v6-checked-robust-continuation")
    energy, local, empty = leaf_controls(original, kernel, arcs, record)
    negative = previous.rejection_controls(original, kernel, arcs, row, seed, record)
    if len(negative) != 20:
        raise AssertionError("newest actual robust forest omitted a required rejection control")
    for path, digest in digests.items():
        if binding.sha(path) != digest:
            raise ValueError("newest robust inputs changed during independent arithmetic controls")
    for name, digest in seed["source_file_sha256"].items():
        if binding.sha(args.source / name) != digest:
            raise ValueError("actual source/history DATA changed during newest robust controls")
    report = {
        "schema": SCHEMA, "verified": False,
        "source_OPEN_index": row["index"], "actual_source_closed_box": row,
        "seed_sha256": digests[args.seed], "seed_controls_sha256": digests[args.seed_controls],
        "diagnosis_sha256": digests[args.diagnosis],
        "both_entire_actual_closed_root_partitions_and_exact_ledgers_reconstructed": True,
        "latest_arithmetic_result": result,
        "all_previous_non_OPEN_nodes_positive_supports_and_proved_ledgers_preserved_identically": True,
        "old_nodes_retained": retained_nodes, "old_positive_supports_retained": retained_supports,
        "old_proved_closed_leaves_retained": retained_leaves,
        "actual_strict_energy_leaves_independently_checked": energy,
        "independent_sine_square_feasible_corner_midpoint_checks": energy*3,
        "actual_original_LOCAL_leaves_reconstructed_not_declared_empty": local,
        "actual_exact_EMPTY_leaves_reconstructed": empty,
        "actual_rejection_controls_passed": negative,
        "retained_OPEN_leaves": len(pending),
        "entire_root_arithmetic_cover_completed": not pending,
        "source_file_sha256": seed["source_file_sha256"],
        "arithmetic_only_NOT_complete_latest_model_source_history_or_geometry_acceptance": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "tested_modules": {Path(module.__file__).name: binding.sha(module.__file__)
                           for module in (forest, forest.prior, previous.independent.signed,
                                          previous.BASE, codec, previous, producer)},
        "executed_test_sha256": binding.sha(__file__),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({"newest_checked_robust_forest_independent_arithmetic_controls_completed": True,
                      "strict_energy_leaves": energy, "original_LOCAL_leaves": local,
                      "OPEN_leaves": len(pending), "actual_rejections": len(negative),
                      "verified": False, "new_geometric_payments": 0}), flush=True)


if __name__ == "__main__":
    main()
