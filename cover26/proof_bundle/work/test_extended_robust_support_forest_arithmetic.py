"""Reconstruct both actual expanded forests, all strict leaves and OPEN boxes.

This is arithmetic DATA testing, not a latest-source or geometry admission.
No producer, frozen checker, paid leaf or historical forest is modified.
"""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import continue_extended_positive_support_forest as initial
import n26_extended_signed_support_forest as forest
import n26_typed_arithmetic_context as codec
import probe_candidate_positive_curvature_hull as fixed
import resume_extended_robust_support_forest as producer
import test_alternative_signed_support_arithmetic as independent
import verify_conditional_force_stage as binding


SCHEMA = "N26-independent-actual-extended-robust-support-forest-arithmetic-controls-v1"
BASE = forest.prior.prior


def scope_gate(record, row):
    if (record["actual_source_closed_box"] != row
            or record["source_OPEN_index"] != row["index"]
            or record["verified"] is not False
            or type(record["new_geometric_payments"]) is not int
            or record["new_geometric_payments"] != 0
            or type(record["candidate_whole_roots_removed"]) is not int
            or record["candidate_whole_roots_removed"] != 0
            or record["global_lower_bound_proved"] is not False
            or record["global_optimality_proved"] is not False
            or record["all_previous_non_OPEN_nodes_and_positive_supports_preserved_identically"] is not True
            or record["complete_latest_source_model_history_geometry_admission_NOT_performed"] is not True):
        raise ValueError("expanded arithmetic forest changed actual root ownership or zero-payment scope")


def retention_gate(seed, record):
    old_nodes, nodes = seed["nodes"], record["nodes"]
    supports, old_supports = record["alternative_supports"], seed["alternative_supports"]
    if (len(nodes) < len(old_nodes) or supports[:len(old_supports)] != old_supports
            or any(old["kind"] != "OPEN" and old != nodes[index]
                   for index, old in enumerate(old_nodes))):
        raise ValueError("expanded robust forest reset an old node, split or exact positive support")
    old_ledger = {leaf["index"]: leaf for leaf in seed["arithmetic_ledger"]}
    ledger = {leaf["index"]: leaf for leaf in record["arithmetic_ledger"]}
    if (len(old_ledger) != len(seed["arithmetic_ledger"])
            or len(ledger) != len(record["arithmetic_ledger"])
            or any(ledger.get(index) != leaf for index, leaf in old_ledger.items())):
        raise ValueError("expanded robust forest changed a previously proved exact closed-leaf ledger")
    return len(old_nodes), len(old_supports), len(old_ledger)


def reconstruct(original, kernel, arcs, row, record, label):
    result, pending, ledger = forest.replay(
        original, kernel, arcs, row, record["nodes"], record["alternative_supports"])
    if (result != record["arithmetic_result"]
            or pending != record["pending_closed_leaf_boxes"]
            or ledger != record["arithmetic_ledger"]):
        raise ValueError(label+" entire forest result, OPEN boxes or exact leaf ledger did not reconstruct")
    if (result["arithmetic_entire_root_lower_bound_cover_completed"] != (not pending)
            or result["arithmetic_entire_root_strictly_empty"] !=
            (not pending and result["counts"]["LOCAL"] == 0)):
        raise ValueError(label+" arithmetic completion claim does not match actual closed leaves")
    print(json.dumps({"actual_entire_arithmetic_forest_reconstructed": label,
                      "nodes": len(record["nodes"]), "positive_supports": len(record["alternative_supports"]),
                      "strict_signed_leaves": result["counts"][forest.KIND],
                      "OPEN_leaves": len(pending), "verified": False,
                      "new_geometric_payments": 0}), flush=True)
    return result, pending, ledger


def original_sine_controls(original, kernel, arcs, leaf):
    """Use sine-square point energy instead of the direct Taylor expression."""
    lower, upper = list(map(F, leaf["lower"])), list(map(F, leaf["upper"]))
    energy_lower = F(leaf["arithmetic_result"]["boundary_Dirichlet_energy_lower"])
    for point in (lower, upper, [(a+b)/2 for a, b in zip(lower, upper)]):
        full = independent.signed.hull.quadratic.reference_gate(
            point, lower, upper, original["matrix"])[0]
        numerator = 0
        for i, j, weight in kernel["pairs"]:
            _, sine = arcs.sincos_turn((full[j]-full[i])/2)
            numerator += 4*weight*max(sine[0]**2, sine[1]**2)
        energy_upper = F(numerator, kernel["energy_denominator"]*arcs.SCALE**2)
        if energy_lower > energy_upper:
            raise AssertionError("original direct leaf bound exceeds independent feasible point energy")


def independent_leaf_controls(original, kernel, arcs, record):
    checked = 0
    for leaf in record["arithmetic_ledger"]:
        if leaf["kind"] == forest.KIND:
            index = leaf["support_index"]
            item = {
                "actual_closed_leaf": leaf,
                "NEW_positive_support": record["alternative_supports"][index],
                "NEW_signed_certificate": leaf["certificate"],
                "signed_arithmetic_diagnosis": {"exact_arithmetic_result": leaf["arithmetic_result"]},
            }
            independent.check(original, arcs, item)
        elif leaf["kind"] == "ORIGINAL-ENERGY":
            original_sine_controls(original, kernel, arcs, leaf)
        else:
            raise ValueError("actual newest forest introduced an untested exact leaf mode")
        checked += 1
        if checked % 16 == 0:
            print(json.dumps({"independent_actual_strict_leaf_controls": checked,
                              "total": len(record["arithmetic_ledger"]),
                              "verified": False, "new_geometric_payments": 0}), flush=True)
    return checked


def ancestor_gate(seed, record, original, arcs, diagnosis):
    ledger = {leaf["index"]: leaf for leaf in record["arithmetic_ledger"]}
    old_pending = {leaf["index"]: leaf for leaf in seed["pending_closed_leaf_boxes"]}
    reconstructed = []
    for item in diagnosis["results"]:
        candidates = [trial for trial in item["tests"] if trial["strict_actual_closed_leaf_exclusion"]]
        if not candidates:
            continue
        ancestor = item["old_OPEN_leaf_index"]
        branch = producer.descendants(seed["nodes"], ancestor)
        if (seed["nodes"][ancestor]["kind"] != "SPLIT"
                or record["nodes"][ancestor] != seed["nodes"][ancestor]):
            raise ValueError("robust whole-ancestor supplement replaced an already split old node")
        trial = max(candidates, key=lambda test: F(test["signed_arithmetic_diagnosis"][
            "exact_arithmetic_result"]["strict_radius_margin"]))
        parent = independent.check(original, arcs, {**trial, "actual_closed_leaf": item["actual_closed_leaf"]})
        expected = sorted(index for index in old_pending if index in branch)
        matching = [supplement for supplement in record["robust_ancestor_supplement_replays"]
                    if supplement["old_ancestor_node"] == ancestor]
        if (len(matching) != 1 or matching[0]["old_ancestor_SPLIT_kept_identically"] is not True
                or sorted(matching[0]["actual_OPEN_descendants_freshly_lower_bounded"]) != expected):
            raise ValueError("robust supplement omitted, duplicated or relabelled an actual OPEN descendant")
        for index in expected:
            leaf, node = ledger.get(index), record["nodes"][index]
            if (leaf is None or node["kind"] != forest.KIND
                    or record["alternative_supports"][node["support_index"]] != trial["NEW_positive_support"]
                    or node["certificate"] != trial["NEW_signed_certificate"]
                    or leaf["lower"] != old_pending[index]["lower"]
                    or leaf["upper"] != old_pending[index]["upper"]):
                raise ValueError("robust supplement did not freshly prove the unchanged actual descendant domain")
            ancestor_box = item["actual_closed_leaf"]
            if any(F(a) < F(pa) or F(b) > F(pb) for a, b, pa, pb in zip(
                    leaf["lower"], leaf["upper"], ancestor_box["lower"], ancestor_box["upper"])):
                raise ValueError("robust descendant escaped the closed ancestor box")
        reconstructed.append({"old_ancestor_node": ancestor, "old_SPLIT_preserved": True,
                              "strict_actual_descendant_indices": expected,
                              "whole_ancestor_strict_radius_margin": parent["strict_radius_margin"]})
    if len(reconstructed) != len(record["robust_ancestor_supplement_replays"]):
        raise ValueError("expanded robust report has an unbound extra ancestor supplement")
    return reconstructed


def rejection_controls(original, kernel, arcs, row, seed, record):
    negative = []

    def reject(label, call):
        try:
            call()
        except (ValueError, KeyError, TypeError, IndexError):
            negative.append(label)
        else:
            raise AssertionError("invalid actual expanded robust forest control accepted: "+label)

    nodes = record["nodes"]
    split = next(index for index, node in enumerate(nodes) if node["kind"] == "SPLIT")
    signed_leaf = next(leaf for leaf in record["arithmetic_ledger"] if leaf["kind"] == forest.KIND)
    open_index = record["pending_closed_leaf_boxes"][0]["index"]

    def changed_partition(mutation):
        bad = deepcopy(nodes)
        mutation(bad)
        forest.partition(original["matrix"], row, bad, BASE.independently_contract, True)

    reject("actual-closed-sibling-half-omitted", lambda: changed_partition(
        lambda bad: bad[split].update(children=bad[split]["children"][:1])))
    reject("actual-closed-sibling-halves-identified", lambda: changed_partition(
        lambda bad: bad[split].update(children=[bad[split]["children"][0]]*2)))
    reject("actual-unreachable-hidden-node", lambda: changed_partition(
        lambda bad: bad.append({"kind": "OPEN"})))
    reject("actual-boolean-child-index", lambda: changed_partition(
        lambda bad: bad[split].update(children=[True, bad[split]["children"][1]])))
    reject("actual-SPLIT-unknown-payment-field", lambda: changed_partition(
        lambda bad: bad[split].update(fake_payment=True)))
    reject("actual-nonempty-OPEN-domain-relabeled-EMPTY", lambda: changed_partition(
        lambda bad: bad.__setitem__(open_index, {"kind": "EMPTY"})))
    reject("actual-unproved-leaf-mode", lambda: changed_partition(
        lambda bad: bad.__setitem__(signed_leaf["index"], {"kind": "UNPROVED-SUPPORT"})))

    def changed_certificate(mutation):
        bad = deepcopy(signed_leaf["certificate"])
        mutation(bad)
        independent.signed.bound(
            original["reference"], record["alternative_supports"][signed_leaf["support_index"]],
            original["matrix"], signed_leaf["lower"], signed_leaf["upper"], bad, original["radius"], arcs)

    reject("actual-signed-unknown-certificate-field", lambda: changed_certificate(
        lambda bad: bad.update(fake_acceptance=True)))
    reject("actual-signed-invalid-positive-LDL", lambda: changed_certificate(
        lambda bad: bad.update(signed_eta=["-1000000000000000"]*15)))
    reject("actual-signed-infeasible-reference", lambda: changed_certificate(
        lambda bad: bad["reference_turns"].__setitem__(0, "100")))
    reject("actual-signed-negative-dual", lambda: changed_certificate(
        lambda bad: bad.update(difference_dual={"q": 1, "terms": [[0, 1, "-1"]]})))

    def changed_support(mutation):
        bad = deepcopy(record["alternative_supports"][signed_leaf["support_index"]])
        mutation(bad)
        BASE.support_gate(original, [bad])

    reject("actual-NEW-support-original-rod-omitted", lambda: changed_support(
        lambda bad: bad["reference"]["edges"].pop()))
    reject("actual-NEW-support-nonpositive-weight", lambda: changed_support(
        lambda bad: bad["reference"]["weight_numerators"].__setitem__(0, "0")))
    reject("actual-NEW-support-false-integer-inverse", lambda: changed_support(
        lambda bad: bad["inverse"]["inverse_numerators"][0].__setitem__(
            0, str(int(bad["inverse"]["inverse_numerators"][0][0])+1))))
    reject("actual-NEW-support-forged-original-fixed-label", lambda: changed_support(
        lambda bad: bad["reference"].update(
            alternative_weights_are_DIAGNOSTIC_not_original_accepted_support=False)))

    def changed_old_node():
        bad = {**record, "nodes": deepcopy(nodes)}
        bad["nodes"][514] = {"kind": "OPEN"}
        retention_gate(seed, bad)

    reject("actual-old-ancestor-SPLIT-reset", changed_old_node)
    reject("actual-original-support-prefix-omitted", lambda:
           retention_gate(seed, {**record, "alternative_supports": record["alternative_supports"][1:]}))
    reject("actual-old-strict-leaf-ledger-omitted", lambda:
           retention_gate(seed, {**record, "arithmetic_ledger": record["arithmetic_ledger"][1:]}))
    reject("actual-diagnostic-scope-promoted-to-acceptance", lambda:
           scope_gate({**record, "verified": True}, row))
    reject("actual-arithmetic-leaf-count-promoted-to-payments", lambda:
           scope_gate({**record, "new_geometric_payments": 1}, row))
    return negative


def main():
    parser = argparse.ArgumentParser()
    for name in ("resource", "resource-replay", "source", "seed", "diagnosis",
                 "robust-diagnosis", "robust-controls", "report"):
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
        raise ValueError("expanded robust controls changed fixed arithmetic DATA identity")
    model = codec.gate(binding.read(args.resource / "CONTEXT.json")["typed_context"])
    original, kernel = model["original"], model["original_kernel"]
    seed, record = binding.read(args.seed), binding.read(args.diagnosis)
    diagnosis = binding.read(args.robust_diagnosis)
    controls = binding.read(args.robust_controls)
    inputs = {path: binding.sha(path) for path in
              (args.seed, args.diagnosis, args.robust_diagnosis, args.robust_controls)}
    if (seed["schema"] != initial.SCHEMA or record["schema"] != producer.SCHEMA
            or seed["executed_producer_sha256"] != binding.sha(initial.__file__)
            or record["executed_producer_sha256"] != binding.sha(producer.__file__)
            or record["old_arithmetic_forest_sha256"] != inputs[args.seed]
            or record["robust_diagnosis_sha256"] != inputs[args.robust_diagnosis]
            or controls["diagnosis_sha256"] != inputs[args.robust_diagnosis]
            or controls["verified"] is not False or controls["new_geometric_payments"] != 0
            or controls["tested_signed_module_sha256"] != binding.sha(independent.signed.__file__)):
        raise ValueError("expanded robust arithmetic controls changed actual executor or diagnosis lineage")
    for data in (seed, record):
        for module in (forest, forest.prior, independent.signed):
            if data["modules"][linux(Path(module.__file__))] != binding.sha(module.__file__):
                raise ValueError("expanded robust controls used changed exact arithmetic modules")
    accepted = binding.read(args.source / "VERIFIED.json")
    if record["source_file_sha256"] != seed["source_file_sha256"]:
        raise ValueError("expanded robust arithmetic controls changed actual historical source bindings")
    for name, digest in seed["source_file_sha256"].items():
        if binding.sha(args.source / name) != digest or accepted["files"][name] != digest:
            raise ValueError("expanded robust controls changed actual source/root/history DATA")
    row = next(row for row in binding.read(args.source / "PENDING-ANGLES.json")
               if row["index"] == record["source_OPEN_index"])
    for data in (seed, record):
        scope_gate(data, row)
    retained_nodes, retained_supports, retained_leaves = retention_gate(seed, record)
    arcs = binding.force.load_trig(args.resource)[0]
    old_result, _, _ = reconstruct(original, kernel, arcs, row, seed, "v4-seed")
    result, pending, ledger = reconstruct(original, kernel, arcs, row, record, "v5-robust-resume")
    strict_count = independent_leaf_controls(original, kernel, arcs, record)
    ancestors = ancestor_gate(seed, record, original, arcs, diagnosis)
    negative = rejection_controls(original, kernel, arcs, row, seed, record)
    if len(negative) != 20:
        raise AssertionError("expanded robust controls omitted an actual required rejection")
    for path, digest in inputs.items():
        if binding.sha(path) != digest:
            raise ValueError("expanded robust input changed during independent arithmetic testing")
    for name, digest in seed["source_file_sha256"].items():
        if binding.sha(args.source / name) != digest:
            raise ValueError("actual source/history DATA changed during expanded robust arithmetic testing")
    report = {
        "schema": SCHEMA, "verified": False,
        "source_OPEN_index": row["index"], "actual_source_closed_box": row,
        "seed_sha256": inputs[args.seed], "diagnosis_sha256": inputs[args.diagnosis],
        "robust_diagnosis_sha256": inputs[args.robust_diagnosis],
        "robust_controls_sha256": inputs[args.robust_controls],
        "both_entire_actual_closed_root_partitions_and_exact_ledgers_reconstructed": True,
        "seed_arithmetic_result": old_result, "latest_arithmetic_result": result,
        "all_previous_non_OPEN_nodes_positive_supports_and_proved_ledgers_preserved_identically": True,
        "old_nodes_retained": retained_nodes, "old_positive_supports_retained": retained_supports,
        "old_strict_leaves_retained": retained_leaves,
        "actual_strict_leaf_count_independently_tested": strict_count,
        "independent_sine_square_feasible_corner_midpoint_checks": strict_count*3,
        "robust_ancestor_and_actual_descendant_controls": ancestors,
        "actual_rejection_controls_passed": negative,
        "retained_OPEN_leaves": len(pending),
        "entire_root_arithmetic_cover_completed": not pending,
        "actual_formal_source_partial_forests_DATA_not_reset": True,
        "source_file_sha256": seed["source_file_sha256"],
        "arithmetic_only_NOT_complete_latest_model_source_history_or_geometry_acceptance": True,
        "new_support_mode_NOT_admitted_by_running_mixed_or_product_checker": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "tested_modules": {Path(module.__file__).name: binding.sha(module.__file__)
                           for module in (forest, forest.prior, independent.signed,
                                          BASE, codec, independent, producer, initial)},
        "executed_test_sha256": binding.sha(__file__),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({"actual_extended_robust_forest_independent_arithmetic_controls_completed": True,
                      "strict_leaves": strict_count, "OPEN_leaves": len(pending),
                      "actual_rejections": len(negative), "verified": False,
                      "new_geometric_payments": 0}), flush=True)


if __name__ == "__main__":
    main()
