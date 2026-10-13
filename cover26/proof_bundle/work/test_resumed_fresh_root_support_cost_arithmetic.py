"""Independent actual root25 v1/v2 retention, strict leaves and closed splits."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_extended_signed_support_forest as forest
import n26_typed_arithmetic_context as codec
import probe_candidate_positive_curvature_hull as fixed
import resume_fresh_root_support_cost_forest as producer
import test_fresh_checked_positive_support_forest_arithmetic as previous
import test_support_cost_refined_forest_arithmetic as split_controls
import test_support_cost_split_policy as policy_controls
import verify_conditional_force_stage as binding


SCHEMA = "N26-independent-actual-preserved-fresh-root-support-cost-forest-controls-v1"
BASE = forest.prior.prior


def scope(record, row):
    if (record["actual_source_closed_box"] != row or record["source_OPEN_index"] != row["index"]
            or record["verified"] is not False or type(record["new_geometric_payments"]) is not int
            or record["new_geometric_payments"] != 0 or record["candidate_whole_roots_removed"] != 0
            or record["global_lower_bound_proved"] is not False
            or record["global_optimality_proved"] is not False
            or record["source_actual_partial_forests_and_paid_leaves_NOT_reset"] is not True
            or record["other_root_nodes_ownership_payments_and_acceptance_NOT_imported"] is not True
            or record["all_previous_non_OPEN_nodes_and_positive_supports_preserved_identically"] is not True
            or record["all_previous_proved_closed_leaf_ledgers_preserved_identically"] is not True
            or record["complete_latest_source_model_history_geometry_admission_NOT_performed"] is not True):
        raise ValueError("resumed fresh-root arithmetic scope changed ownership, retention or payments")


def negatives(original, kernel, arcs, row, seed, record):
    nodes, negative = record["nodes"], []
    split = next(index for index, node in enumerate(nodes) if node["kind"] == "SPLIT")
    old_split = next(index for index, node in enumerate(seed["nodes"]) if node["kind"] == "SPLIT")
    leaf = next(leaf for leaf in record["arithmetic_ledger"] if leaf["kind"] == forest.KIND)

    def reject(label, call):
        try:
            call()
        except (ValueError, KeyError, TypeError, IndexError):
            negative.append(label)
        else:
            raise AssertionError("invalid actual resumed root support forest accepted: "+label)

    def partition_change(mutation):
        bad = deepcopy(nodes)
        mutation(bad)
        forest.partition(original["matrix"], row, bad, BASE.independently_contract, True)

    for label, mutation in (
        ("actual-resumed-closed-half-omitted", lambda bad: bad[split].update(children=bad[split]["children"][:1])),
        ("actual-resumed-halves-identified", lambda bad: bad[split].update(children=[bad[split]["children"][0]]*2)),
        ("actual-resumed-hidden-unreachable-node", lambda bad: bad.append({"kind": "OPEN"})),
        ("actual-resumed-boolean-child", lambda bad: bad[split].update(children=[True, bad[split]["children"][1]])),
        ("actual-resumed-split-unknown-proof-field", lambda bad: bad[split].update(fake_payment=True)),
        ("actual-resumed-unproved-leaf-mode", lambda bad: bad.__setitem__(leaf["index"], {"kind": "UNPROVED-ENERGY"})),
        ("actual-resumed-nonempty-leaf-called-EMPTY", lambda bad: bad.__setitem__(leaf["index"], {"kind": "EMPTY"})),
    ):
        reject(label, lambda mutation=mutation: partition_change(mutation))

    def certificate_change(mutation):
        bad = deepcopy(leaf["certificate"])
        mutation(bad)
        forest.prior.signed.bound(
            original["reference"], record["alternative_supports"][leaf["support_index"]],
            original["matrix"], leaf["lower"], leaf["upper"], bad, original["radius"], arcs)

    for label, mutation in (
        ("actual-resumed-unknown-signed-proof-field", lambda bad: bad.update(fake_acceptance=True)),
        ("actual-resumed-nonpositive-LDL", lambda bad: bad.update(signed_eta=["-1000000000000000"]*15)),
        ("actual-resumed-infeasible-reference", lambda bad: bad["reference_turns"].__setitem__(0, "100")),
        ("actual-resumed-negative-difference-dual", lambda bad: bad.update(
            difference_dual={"q": 1, "terms": [[0, 1, "-1"]]})),
    ):
        reject(label, lambda mutation=mutation: certificate_change(mutation))

    def support_change(mutation):
        bad = deepcopy(record["alternative_supports"][leaf["support_index"]])
        mutation(bad)
        BASE.support_gate(original, [bad])

    for label, mutation in (
        ("actual-resumed-original-rod-omitted", lambda bad: bad["reference"]["edges"].pop()),
        ("actual-resumed-nonpositive-rod-weight", lambda bad: bad["reference"]["weight_numerators"].__setitem__(0, "0")),
        ("actual-resumed-false-exact-inverse", lambda bad: bad["inverse"]["inverse_numerators"][0].__setitem__(
            0, str(int(bad["inverse"]["inverse_numerators"][0][0])+1))),
        ("actual-resumed-forged-original-fixed-weight-label", lambda bad: bad["reference"].update(
            alternative_weights_are_DIAGNOSTIC_not_original_accepted_support=False)),
    ):
        reject(label, lambda mutation=mutation: support_change(mutation))

    def changed_old_split():
        bad = {**record, "nodes": deepcopy(nodes)}
        bad["nodes"][old_split] = {"kind": "OPEN"}
        previous.leaf_controls.previous.retention_gate(seed, bad)

    reject("actual-resumed-old-closed-split-reset", changed_old_split)
    reject("actual-resumed-old-support-prefix-omitted", lambda:
           previous.leaf_controls.previous.retention_gate(
               seed, {**record, "alternative_supports": record["alternative_supports"][1:]}))
    reject("actual-resumed-old-strict-ledger-omitted", lambda:
           previous.leaf_controls.previous.retention_gate(
               seed, {**record, "arithmetic_ledger": record["arithmetic_ledger"][1:]}))
    reject("actual-resumed-arithmetic-promoted-to-acceptance", lambda: scope({**record, "verified": True}, row))
    reject("actual-resumed-strict-leaves-promoted-to-payments", lambda: scope({**record, "new_geometric_payments": 1}, row))
    return negative


def main():
    parser = argparse.ArgumentParser()
    for name in ("resource", "resource-replay", "source", "seed", "seed-controls",
                 "policy-controls", "diagnosis", "report"):
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
        raise ValueError("resumed fresh-root controls changed fixed arithmetic DATA identity")
    model = codec.gate(binding.read(args.resource / "CONTEXT.json")["typed_context"])
    original, kernel = model["original"], model["original_kernel"]
    seed, record = binding.read(args.seed), binding.read(args.diagnosis)
    controls, policy = binding.read(args.seed_controls), binding.read(args.policy_controls)
    digests = {path: binding.sha(path) for path in
               (args.seed, args.seed_controls, args.policy_controls, args.diagnosis)}
    if (seed["schema"] != producer.previous_producer.SCHEMA
            or seed["executed_producer_sha256"] != binding.sha(producer.previous_producer.__file__)
            or record["schema"] != producer.SCHEMA
            or record["executed_producer_sha256"] != binding.sha(producer.__file__)
            or record["old_arithmetic_forest_sha256"] != digests[args.seed]
            or record["actual_seed_independent_arithmetic_controls_sha256"] != digests[args.seed_controls]
            or record["actual_split_policy_controls_sha256"] != digests[args.policy_controls]
            or controls["schema"] != previous.SCHEMA
            or controls["executed_test_sha256"] != binding.sha(previous.__file__)
            or controls["diagnosis_sha256"] != digests[args.seed]
            or controls["latest_arithmetic_result"] != seed["arithmetic_result"]
            or controls["verified"] is not False or controls["new_geometric_payments"] != 0
            or controls["candidate_whole_roots_removed"] != 0
            or len(controls["actual_rejection_controls_passed"]) != 20
            or policy["tested_producer_sha256"] != binding.sha(producer.policy.__file__)
            or policy["executed_test_sha256"] != binding.sha(policy_controls.__file__)
            or len(policy["invalid_policy_and_actual_shared_half_controls_rejected"]) != 8
            or policy["verified"] is not False or policy["new_geometric_payments"] != 0):
        raise ValueError("resumed fresh-root forest changed actual executor/seed/policy lineage")
    for data in (seed, record):
        for module in (forest, forest.prior, forest.prior.signed):
            if data["modules"][linux(Path(module.__file__))] != binding.sha(module.__file__):
                raise ValueError("resumed fresh-root controls used changed exact original-rod arithmetic")
    for module in (producer.suggestion, producer.policy):
        if record["modules"][linux(Path(module.__file__))] != binding.sha(module.__file__):
            raise ValueError("resumed fresh-root controls changed actual numerical step or split-policy producer")
    accepted = binding.read(args.source / "VERIFIED.json")
    if (record["source_file_sha256"] != seed["source_file_sha256"]
            or controls["source_file_sha256"] != seed["source_file_sha256"]):
        raise ValueError("resumed fresh-root controls changed actual source/history DATA bindings")
    for name, digest in seed["source_file_sha256"].items():
        if binding.sha(args.source / name) != digest or accepted["files"][name] != digest:
            raise ValueError("resumed fresh-root controls changed actual source/root/history DATA")
    row = next(row for row in binding.read(args.source / "PENDING-ANGLES.json")
               if row["index"] == record["source_OPEN_index"])
    if row != seed["actual_source_closed_box"]:
        raise ValueError("resumed fresh-root controls changed actual seed ownership")
    scope(record, row)
    retained_nodes, retained_supports, retained_leaves = previous.leaf_controls.previous.retention_gate(seed, record)
    arcs = binding.force.load_trig(args.resource)[0]
    previous.leaf_controls.previous.reconstruct(original, kernel, arcs, row, seed, "root25-v1-independent-seed")
    result, pending, ledger = previous.leaf_controls.previous.reconstruct(
        original, kernel, arcs, row, record, "root25-v2-preserved-support-cost")
    energy, local, empty = previous.leaf_controls.leaf_controls(original, kernel, arcs, record)
    negative = negatives(original, kernel, arcs, row, seed, record)
    if len(negative) != 20:
        raise AssertionError("resumed fresh-root arithmetic omitted a required actual rejection")
    splits, narrow = split_controls.split_decision_gate(original, row, seed, record)
    for path, digest in digests.items():
        if binding.sha(path) != digest:
            raise ValueError("resumed fresh-root inputs changed during independent arithmetic testing")
    for name, digest in seed["source_file_sha256"].items():
        if binding.sha(args.source / name) != digest:
            raise ValueError("actual source/history DATA changed during resumed fresh-root controls")
    report = {
        "schema": SCHEMA, "verified": False,
        "source_OPEN_index": row["index"], "actual_source_closed_box": row,
        "seed_sha256": digests[args.seed], "seed_controls_sha256": digests[args.seed_controls],
        "policy_controls_sha256": digests[args.policy_controls], "diagnosis_sha256": digests[args.diagnosis],
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
        "actual_new_closed_splits_and_shared_boundaries_reconstructed": splits,
        "new_actual_root_tight_coordinate_splits_checked": narrow,
        "retained_OPEN_leaves": len(pending), "entire_root_arithmetic_cover_completed": not pending,
        "source_file_sha256": seed["source_file_sha256"],
        "source_actual_partial_forests_and_paid_leaves_NOT_reset": True,
        "other_root_nodes_ownership_payments_and_acceptance_NOT_imported": True,
        "arithmetic_only_NOT_complete_latest_model_source_history_or_geometry_acceptance": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "tested_modules": {Path(module.__file__).name: binding.sha(module.__file__)
                           for module in (forest, forest.prior, forest.prior.signed, BASE, codec,
                                          previous, producer, producer.suggestion, producer.policy, split_controls)},
        "executed_test_sha256": binding.sha(__file__),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({"actual_resumed_fresh_root_independent_controls_completed": True,
                      "actual_root": row["index"], "strict_energy_leaves": energy,
                      "original_LOCAL_leaves": local, "OPEN_leaves": len(pending),
                      "actual_rejections": len(negative), "verified": False,
                      "new_geometric_payments": 0}), flush=True)


if __name__ == "__main__":
    main()
