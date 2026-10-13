"""Actual old-proof and proper-region mode controls, NOT newest admission."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_mixed_full134rod_support_forest as mixed
import probe_balanced_full134rod_neighborhoods as inputs
import test_balanced_full134rod_neighborhoods as neighborhood_controls
import verify_conditional_force_stage as binding


SCHEMA = "N26-independent-old92-full134rod-forest-mode-arithmetic-controls-v1"


def main():
    parser = argparse.ArgumentParser()
    for name in ("resource", "resource-replay", "current-audit", "source", "seed", "seed-controls",
                 "ancestor-seed", "old-full-diagnosis", "old-full-controls", "prior-diagnosis",
                 "prior-controls", "correlated-diagnosis", "correlated-controls",
                 "old-minimax-diagnosis", "old-minimax-controls", "balanced-diagnosis", "balanced-controls",
                 "neighborhood-diagnosis", "neighborhood-controls", "report"):
        parser.add_argument("--"+name, type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    original, model, seed, row, arcs, digests, layer, stresses = inputs.data_gate(args)
    diagnosis, controls = binding.read(args.neighborhood_diagnosis), binding.read(args.neighborhood_controls)
    digests[args.neighborhood_diagnosis] = binding.sha(args.neighborhood_diagnosis)
    digests[args.neighborhood_controls] = binding.sha(args.neighborhood_controls)
    if (diagnosis["schema"] != inputs.SCHEMA
            or diagnosis["executed_probe_sha256"] != binding.sha(inputs.__file__)
            or diagnosis["checked_v7_forest_sha256"] != digests[args.seed]
            or diagnosis["source_file_sha256"] != seed["source_file_sha256"]
            or controls["schema"] != neighborhood_controls.SCHEMA
            or controls["executed_test_sha256"] != binding.sha(neighborhood_controls.__file__)
            or controls["diagnosis_sha256"] != digests[args.neighborhood_diagnosis]
            or len(controls["actual_closed_subset_and_no_payment_rejection_controls_passed"]) != 8
            or controls["verified"] is not False or controls["new_geometric_payments"] != 0):
        raise ValueError("mixed mode controls lack actual checked proper-region arithmetic")
    table = [{"mode": mixed.SUPPORT_MODE,
              "kernel_certificate": item["NEW_full134rod_stress_kernel_certificate"],
              "suggestion_point_turns": item["actual_fixed_feasible_anchor_turns"]}
             for item in stresses["results"]]
    # Load the fixed original kernel from the verified arithmetic resource,
    # never by forging a full134rod kernel's old identity flag.
    original_kernel = inputs.stress_producer.old.prior_producer.previous.producer.codec.gate(
        binding.read(args.resource / "CONTEXT.json")["typed_context"])["original_kernel"]
    before = deepcopy(seed["nodes"])
    previous_result, previous_pending, previous_ledger = mixed.replay(
        original, original_kernel, arcs, row, seed["nodes"], seed["alternative_supports"], table)
    if (previous_pending != seed["pending_closed_leaf_boxes"]
            or previous_ledger != seed["arithmetic_ledger"] or seed["nodes"] != before
            or previous_result["counts"][mixed.KIND] != 0):
        raise ValueError("mixed mode changed the actual preserved checked OLD v7 arithmetic tree")
    fixtures = []
    for support_index, item in enumerate(diagnosis["results"]):
        trial = next(trial for trial in item["trials"]
                     if trial["requested_closed_half_width"] == "1/1000")
        if trial["strict_actual_proper_closed_neighborhood"] is not True:
            raise ValueError("mixed positive mode fixture is not an actually strict proper region")
        fixture_row = {
            "sharp_lower": trial["actual_proper_closed_lower"],
            "sharp_upper": trial["actual_proper_closed_upper"],
            "arithmetic_fixture_has_NO_whole_source_root_owner": True,
        }
        nodes = [{"kind": mixed.KIND, "full_support_index": support_index,
                  "certificate": trial["NEW_stress_correlated_certificate"]}]
        result, pending, ledger = mixed.replay(
            original, original_kernel, arcs, fixture_row, nodes, seed["alternative_supports"], table)
        if (pending or result["counts"][mixed.KIND] != 1
                or result["arithmetic_entire_root_strictly_empty"] is not True
                or ledger[0]["kind"] != mixed.KIND
                or ledger[0]["arithmetic_result"] != trial["NEW_stress_correlated_result"]):
            raise ValueError("mixed NEW134rod actual proper-region fixture failed strict reconstruction")
        fixtures.append((fixture_row, nodes, result))
    rejected = []

    def reject(label, call):
        try:
            call()
        except (ValueError, KeyError, TypeError, IndexError):
            rejected.append(label)
        else:
            raise AssertionError("invalid actual mixed old92/full134rod mode accepted: "+label)

    fixture_row, nodes, _ = fixtures[0]

    def changed_node(mutation):
        bad = deepcopy(nodes)
        mutation(bad[0])
        mixed.replay(original, original_kernel, arcs, fixture_row, bad, seed["alternative_supports"], table)

    for label, mutation in (
        ("mixed-full134rod-old-support-index-field-laundered", lambda bad: bad.update(
            support_index=bad.pop("full_support_index"))),
        ("mixed-full134rod-boolean-support-index", lambda bad: bad.update(full_support_index=True)),
        ("mixed-full134rod-support-index-outside-table", lambda bad: bad.update(full_support_index=len(table))),
        ("mixed-full134rod-unknown-leaf-proof-field", lambda bad: bad.update(fake_payment=True)),
        ("mixed-full134rod-old92signed-kind-laundered", lambda bad: bad.update(kind=mixed.old.KIND)),
        ("mixed-full134rod-old92direct-kind-laundered", lambda bad: bad.update(kind="ALTERNATIVE-ENERGY")),
        ("mixed-full134rod-old92fixed-kind-laundered", lambda bad: bad.update(kind="ORIGINAL-ENERGY")),
        ("mixed-full134rod-originalLOCAL-kind-laundered", lambda bad: bad.update(kind="LOCAL")),
        ("mixed-full134rod-unknown-new-mode", lambda bad: bad.update(kind="UNPROVED-FULL134ROD")),
        ("mixed-full134rod-missing-certificate", lambda bad: bad.pop("certificate")),
        ("mixed-full134rod-old-diagonal-certificate-substituted", lambda bad: bad["certificate"].update(
            signed_eta=bad["certificate"].pop("curvature_correction"))),
    ):
        reject(label, lambda mutation=mutation: changed_node(mutation))

    def changed_table(mutation):
        bad = deepcopy(table)
        mutation(bad[0])
        mixed.full_support_gate(model, bad)

    for label, mutation in (
        ("mixed-full134rod-old92support-mode-substituted", lambda bad: bad.update(mode="NEW-POSITIVE-SUPPORT")),
        ("mixed-full134rod-unknown-table-proof-field", lambda bad: bad.update(fake_owner=28)),
        ("mixed-full134rod-old92weights-substituted", lambda bad: bad["kernel_certificate"].update(
            weight_numerators=bad["kernel_certificate"]["weight_numerators"][:92])),
        ("mixed-full134rod-old46inverse-substituted", lambda bad: bad["kernel_certificate"].update(
            inverse_numerators=[row[:46] for row in bad["kernel_certificate"]["inverse_numerators"][:46]])),
        ("mixed-full134rod-false-NEW60inverse-entry", lambda bad:
            bad["kernel_certificate"]["inverse_numerators"][0].__setitem__(
                0, str(int(bad["kernel_certificate"]["inverse_numerators"][0][0])+1))),
        ("mixed-full134rod-zero-weight", lambda bad: bad["kernel_certificate"]["weight_numerators"].__setitem__(0, 0)),
        ("mixed-full134rod-wrong-suggestion-frame", lambda bad: bad.update(suggestion_point_turns=["0"]*14)),
    ):
        reject(label, lambda mutation=mutation: changed_table(mutation))
    reject("mixed-full134rod-empty-distinct-support-table", lambda: mixed.full_support_gate(model, []))
    reject("mixed-full134rod-hidden-unreachable-new-leaf", lambda: mixed.replay(
        original, original_kernel, arcs, fixture_row, nodes+deepcopy(nodes), seed["alternative_supports"], table))
    full_leaf = diagnosis["results"][0]["actual_checked_v7_OPEN_leaf"]
    reject("mixed-full134rod-proper-subset-paid-as-whole-old-leaf", lambda: mixed.replay(
        original, original_kernel, arcs,
        {"sharp_lower": full_leaf["lower"], "sharp_upper": full_leaf["upper"]},
        nodes, seed["alternative_supports"], table))
    retained_record = {**seed, "full134rod_supports": table}
    mixed.retention_gate(seed, retained_record)
    nonopen = next(index for index, node in enumerate(seed["nodes"]) if node["kind"] != "OPEN")
    bad_retained = {**retained_record, "nodes": deepcopy(seed["nodes"])}
    bad_retained["nodes"][nonopen] = {"kind": "OPEN"}
    reject("mixed-full134rod-old-nonOPEN-node-reset", lambda: mixed.retention_gate(seed, bad_retained))
    reject("mixed-full134rod-old-support-prefix-truncated", lambda: mixed.retention_gate(
        seed, {**retained_record, "alternative_supports": seed["alternative_supports"][1:]}))
    reject("mixed-full134rod-old-proof-ledger-truncated", lambda: mixed.retention_gate(
        seed, {**retained_record, "arithmetic_ledger": seed["arithmetic_ledger"][1:]}))
    reject("mixed-full134rod-new-support-prefix-reset", lambda: mixed.retention_gate(
        retained_record, {**retained_record, "full134rod_supports": table[1:]}))
    if len(rejected) != 25:
        raise AssertionError("mixed full134rod mode omitted a required actual guard")
    inputs.stress_producer.old.prior_producer.previous.producer.unchanged_inputs(args, digests, seed)
    report = {
        "schema": SCHEMA, "verified": False,
        "actual_checked_OLD_v7_arithmetic_tree_reconstructed_WITHOUT_becoming_newest_v8": True,
        "old_v7_nodes_checked": len(seed["nodes"]), "old_v7_strict_ledgers_checked": len(seed["arithmetic_ledger"]),
        "actual_NEW134rod_proper_region_mode_fixtures_checked": len(fixtures),
        "proper_region_fixtures_HAVE_NO_whole_source_root_owner": True,
        "old_and_NEWEST_running_nodes_supports_and_proofs_UNMODIFIED": True,
        "actual_mixed_mode_rejection_controls_passed": rejected,
        "latest_v8_or_v3_actual_whole_forests_NOT_checked_or_admitted_here": True,
        "arithmetic_mode_controls_NOT_full_model_source_history_geometry_acceptance": True,
        "source_file_sha256": seed["source_file_sha256"],
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
        "executed_test_sha256": binding.sha(__file__),
        "tested_mixed_forest_module_sha256": binding.sha(mixed.__file__),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({"distinct_old92_full134rod_forest_mode_controls_completed": True,
                      "actual_old_v7_nodes_checked": len(seed["nodes"]),
                      "actual_proper_region_fixtures": len(fixtures), "actual_rejections": len(rejected),
                      "latest_whole_forest_or_geometry_admission": False,
                      "verified": False, "new_geometric_payments": 0}), flush=True)


if __name__ == "__main__":
    main()
