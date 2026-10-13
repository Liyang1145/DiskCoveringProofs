"""Actual OLD v7 fixture intersections/remainders, not newest v8 admission."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

import n26_preserved_closed_subbox_partition as cutter
import probe_balanced_full134rod_neighborhoods as inputs
import test_balanced_full134rod_neighborhoods as controls_module
import verify_conditional_force_stage as binding


SCHEMA = "N26-independent-preserved-closed-subbox-partition-arithmetic-controls-v1"
mixed = cutter.mixed


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
            or controls["schema"] != controls_module.SCHEMA
            or controls["executed_test_sha256"] != binding.sha(controls_module.__file__)
            or controls["diagnosis_sha256"] != digests[args.neighborhood_diagnosis]
            or len(controls["actual_closed_subset_and_no_payment_rejection_controls_passed"]) != 8):
        raise ValueError("closed-subbox fixture lacks actual proper-region controls")
    original_kernel = inputs.stress_producer.old.prior_producer.previous.producer.codec.gate(
        binding.read(args.resource / "CONTEXT.json")["typed_context"])["original_kernel"]
    table = [{"mode": mixed.SUPPORT_MODE, "kernel_certificate": item["NEW_full134rod_stress_kernel_certificate"],
              "suggestion_point_turns": item["actual_fixed_feasible_anchor_turns"]}
             for item in stresses["results"]]
    nodes = deepcopy(seed["nodes"])
    decisions, targets = [], []
    for support_index, item in enumerate(diagnosis["results"]):
        trial = next(trial for trial in item["trials"] if trial["requested_closed_half_width"] == "1/1000")
        old_index = item["actual_checked_v7_OPEN_leaf"]["index"]
        before = deepcopy(nodes)
        nodes, target_index, actual, cuts = cutter.isolate(
            original["matrix"], row, nodes, old_index,
            trial["actual_proper_closed_lower"], trial["actual_proper_closed_upper"])
        if (any(node["kind"] != "OPEN" and node != nodes[index] for index, node in enumerate(before))
                or nodes[target_index] != {"kind": "OPEN"}):
            raise ValueError("actual subbox fixture reset a previous nonOPEN proof")
        kernel = mixed.correlated.full.kernel_gate(model, table[support_index]["kernel_certificate"])
        certificate = trial["NEW_stress_correlated_certificate"]
        result = mixed.correlated.bound(
            kernel, original["matrix"], actual["lower"], actual["upper"], certificate,
            original["radius"], arcs)
        if result["arithmetic_strict_target_test_passed"] is not True:
            raise ValueError("actual isolated whole closed target lacks a fresh strict bound")
        nodes[target_index] = {"kind": mixed.KIND, "full_support_index": support_index,
                               "certificate": certificate}
        decisions.extend(cuts)
        targets.append({"old_v7_OPEN_ancestor": old_index, "actual_NEW_fixture_target": target_index,
                        "actual_closed_lower": actual["lower"], "actual_closed_upper": actual["upper"],
                        "fresh_strict_radius_margin": result["strict_radius_margin"]})
    result, pending, ledger = mixed.replay(
        original, original_kernel, arcs, row, nodes, seed["alternative_supports"], table)
    retained = mixed.retention_gate(seed, {
        "nodes": nodes, "alternative_supports": seed["alternative_supports"],
        "full134rod_supports": table, "arithmetic_ledger": ledger})
    if result["counts"][mixed.KIND] != 2 or not pending:
        raise ValueError("proper-subset fixture silently paid remainders or lost a strict target")
    rejected = []

    def reject(label, call):
        try:
            call()
        except (ValueError, KeyError, TypeError, IndexError):
            rejected.append(label)
        else:
            raise AssertionError("invalid actual closed-subbox refinement accepted: "+label)

    first = diagnosis["results"][0]
    leaf = first["actual_checked_v7_OPEN_leaf"]
    target = next(trial for trial in first["trials"] if trial["requested_closed_half_width"] == "1/1000")
    nonopen = next(index for index, node in enumerate(seed["nodes"]) if node["kind"] != "OPEN")
    for label, index, lower, upper in (
        ("subbox-old-nonOPEN-proof-overwritten", nonopen, target["actual_proper_closed_lower"], target["actual_proper_closed_upper"]),
        ("subbox-boolean-source-node", True, target["actual_proper_closed_lower"], target["actual_proper_closed_upper"]),
        ("subbox-hidden-source-node", len(seed["nodes"]), target["actual_proper_closed_lower"], target["actual_proper_closed_upper"]),
        ("subbox-unproved-whole-leaf-paid-as-proper-subset", leaf["index"], leaf["lower"], leaf["upper"]),
        ("subbox-coordinate-omitted", leaf["index"], target["actual_proper_closed_lower"][:-1], target["actual_proper_closed_upper"]),
        ("subbox-source-domain-escaped", leaf["index"], ["-100"]*15, ["100"]*15),
        ("subbox-reversed-closed-interval", leaf["index"], ["100"]*15, ["-100"]*15),
    ):
        reject(label, lambda index=index, lower=lower, upper=upper: cutter.isolate(
            original["matrix"], row, seed["nodes"], index, lower, upper))
    cut_node = decisions[0]["old_OPEN_node"]
    for label, mutation in (
        ("subbox-one-closed-half-lost", lambda bad: bad[cut_node].update(children=bad[cut_node]["children"][:1])),
        ("subbox-two-halves-identified", lambda bad: bad[cut_node].update(children=[bad[cut_node]["children"][0]]*2)),
        ("subbox-hidden-unreachable-remainder", lambda bad: bad.append({"kind": "OPEN"})),
    ):
        bad = deepcopy(nodes)
        mutation(bad)
        reject(label, lambda bad=bad: mixed.partition(
            original["matrix"], row, bad, mixed.old.prior.prior.tighten, False))
    if len(rejected) != 10:
        raise AssertionError("actual closed-subbox partition omitted a required guard")
    inputs.stress_producer.old.prior_producer.previous.producer.unchanged_inputs(args, digests, seed)
    report = {
        "schema": SCHEMA, "verified": False, "seed_OLD_v7_sha256": digests[args.seed],
        "actual_old_v7_fixture_closed_targets": targets,
        "actual_old_v7_fixture_fresh_closed_splits": len(decisions),
        "both_closed_halves_shared_boundaries_and_all_remainders_reconstructed": True,
        "old_nonOPEN_nodes_support_prefix_and_strict_ledger_preserved": list(retained),
        "remaining_OPEN_fixture_regions": len(pending),
        "actual_preserved_subbox_rejection_controls_passed": rejected,
        "fixture_is_NOT_a_successor_of_NEWEST_running_v8_or_a_current_geometry_admission": True,
        "all_original_and_NEWEST_running_histories_UNMODIFIED": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
        "source_file_sha256": seed["source_file_sha256"],
        "executed_test_sha256": binding.sha(__file__),
        "tested_closed_subbox_module_sha256": binding.sha(cutter.__file__),
        "tested_mixed_forest_module_sha256": binding.sha(mixed.__file__),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({"preserved_closed_subbox_actual_arithmetic_controls_completed": True,
                      "strict_fixture_targets": len(targets), "actual_closed_splits": len(decisions),
                      "remaining_OPEN_fixture_regions": len(pending), "actual_rejections": len(rejected),
                      "latest_whole_forest_or_geometry_admission": False,
                      "verified": False, "new_geometric_payments": 0}), flush=True)


if __name__ == "__main__":
    main()
