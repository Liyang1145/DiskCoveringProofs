"""Actual broad leaf proofs and explicit expanded-table guards, zero payments."""

import argparse
from copy import deepcopy
import json
from pathlib import Path

import n26_extended_signed_support_forest as extended
import n26_typed_arithmetic_context as codec
import probe_broad_positive_support_leaves as producer
import probe_candidate_positive_curvature_hull as fixed
import test_alternative_signed_support_arithmetic as independent
import verify_conditional_force_stage as binding


def main():
    parser = argparse.ArgumentParser()
    for name in ("resource", "resource-replay", "seed", "diagnosis", "report"):
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
        raise ValueError("broader/extended arithmetic controls changed model DATA identity")
    model = codec.gate(binding.read(args.resource / "CONTEXT.json")["typed_context"])
    original, kernel = model["original"], model["original_kernel"]
    seed, diagnosis = binding.read(args.seed), binding.read(args.diagnosis)
    diagnosis_digest = binding.sha(args.diagnosis)
    if (diagnosis["old_arithmetic_forest_sha256"] != binding.sha(args.seed)
            or diagnosis["executed_probe_sha256"] != binding.sha(producer.__file__)
            or diagnosis["verified"] is not False or diagnosis["new_geometric_payments"] != 0
            or diagnosis["candidate_whole_roots_removed"] != 0):
        raise ValueError("broader actual diagnostic scope/old forest/producer changed")
    arcs = binding.force.load_trig(args.resource)[0]
    proved = []
    for item in diagnosis["results"]:
        for trial in item["broader_support_trials"]:
            if trial["strict_actual_closed_leaf_exclusion"]:
                adapted = {**trial, "actual_closed_leaf": item["actual_closed_leaf"]}
                result = independent.check(original, arcs, adapted)
                proved.append({"leaf_index": item["old_OPEN_leaf_index"],
                               "strategy": trial["numerical_suggestion_NOT_proof"]["strategy"],
                               "exact_reconstructed_result": result})
    if not proved:
        raise ValueError("broader controls have no actual strict leaf proof")
    first = next(item for item in diagnosis["results"]
                 if item["at_least_one_strict_actual_closed_leaf_exclusion"])
    trial = next(trial for trial in first["broader_support_trials"]
                 if trial["strict_actual_closed_leaf_exclusion"])
    supports = [*deepcopy(seed["alternative_supports"]), deepcopy(trial["NEW_positive_support"])]
    leaf = first["actual_closed_leaf"]
    row = {**deepcopy(seed["actual_source_closed_box"]),
           "sharp_lower": leaf["lower"], "sharp_upper": leaf["upper"]}
    nodes = [{"kind": extended.KIND, "support_index": 32,
              "certificate": trial["NEW_signed_certificate"]}]
    positive, pending, _ = extended.replay(original, kernel, arcs, row, nodes, supports)
    if pending or not positive["arithmetic_entire_root_strictly_empty"]:
        raise AssertionError("expanded table did not reconstruct the actual closed LEAF-only proof")
    negative = []

    def reject(label, call):
        try:
            call()
        except (ValueError, KeyError, TypeError, IndexError):
            negative.append(label)
        else:
            raise AssertionError("invalid expanded positive-support mode accepted: "+label)

    reject("extended-original32entry-prefix-omitted",
           lambda: extended.support_gate(original, supports[:31]))
    reject("extended-table-exceeds-explicit256entry-limit",
           lambda: extended.support_gate(original, supports*8))

    def changed_support(mutation):
        bad = deepcopy(supports)
        mutation(bad)
        extended.support_gate(original, bad)

    reject("extended-new-entry-unknown-support-mode", lambda: changed_support(
        lambda bad: bad[32].update(mode="UNPROVED-SUPPORT")))
    reject("extended-new-entry-nonpositive-weight", lambda: changed_support(
        lambda bad: bad[32]["reference"]["weight_numerators"].__setitem__(0, "-1")))
    reject("extended-new-entry-changes-original-rods", lambda: changed_support(
        lambda bad: bad[32]["reference"]["edges"].pop()))
    reject("extended-new-entry-false-ground-inverse", lambda: changed_support(
        lambda bad: bad[32]["inverse"]["inverse_numerators"][0].__setitem__(
            0, str(int(bad[32]["inverse"]["inverse_numerators"][0][0])+1))))
    reject("extended-new-entry-forged-original-fixed-mode", lambda: changed_support(
        lambda bad: bad[32]["reference"].update(
            alternative_weights_are_DIAGNOSTIC_not_original_accepted_support=False)))
    reject("extended-new-entry-unknown-proof-field", lambda: changed_support(
        lambda bad: bad[32].update(fake_acceptance=True)))
    reject("extended-new-entry-relabelled-as-old-direct-mode", lambda: extended.replay(
        original, kernel, arcs, row, [{"kind": "ALTERNATIVE-ENERGY", "support_index": 32}], supports))
    reject("extended-boolean-signed-support-index", lambda: extended.replay(
        original, kernel, arcs, row, [{**nodes[0], "support_index": True}], supports))
    reject("extended-signed-support-index-out-of-table", lambda: extended.replay(
        original, kernel, arcs, row, [{**nodes[0], "support_index": 33}], supports))
    bad_node = deepcopy(nodes[0])
    bad_node["certificate"]["signed_eta"] = ["-1000000000000"]*15
    reject("extended-signed-curvature-not-positive-LDL", lambda: extended.replay(
        original, kernel, arcs, row, [bad_node], supports))
    if binding.sha(args.diagnosis) != diagnosis_digest:
        raise ValueError("actual broad diagnosis changed during independent controls")
    report = {
        "schema": "N26-independent-broad-positive-support-and-extended-table-arithmetic-controls-v1",
        "actual_broad_strict_trial_proofs_reconstructed": proved,
        "independent_sine_square_corner_midpoint_checks": 3*len(proved),
        "extended_table_32old_plus_NEW_entry_actual_LEAF_proof_reconstructed": True,
        "invalid_extended_table_and_actual_leaf_controls_rejected": negative,
        "actual_proper_closed_LEAF_only_NOT_whole_source_root": True,
        "diagnosis_sha256": diagnosis_digest,
        "verified": False, "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "complete_latest_source_model_history_geometry_gate_NOT_executed": True,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "tested_extended_forest_module_sha256": binding.sha(extended.__file__),
        "tested_signed_module_sha256": binding.sha(extended.prior.signed.__file__),
        "executed_test_sha256": binding.sha(__file__),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({"broad_and_extended_arithmetic_controls_completed": True,
                      "actual_strict_trial_proofs": len(proved), "actual_rejections": len(negative),
                      "verified": False, "new_geometric_payments": 0}), flush=True)


if __name__ == "__main__":
    main()
