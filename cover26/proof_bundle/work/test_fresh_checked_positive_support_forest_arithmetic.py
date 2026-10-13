"""Independent actual fresh-root weighted forest and donor-DATA-only checks."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_extended_signed_support_forest as forest
import n26_typed_arithmetic_context as codec
import probe_candidate_positive_curvature_hull as fixed
import propose_fresh_checked_positive_support_forest as producer
import test_checked_extended_robust_forest_arithmetic as leaf_controls
import verify_conditional_force_stage as binding


SCHEMA = "N26-independent-actual-fresh-root-universal-positive-support-forest-controls-v1"
BASE = forest.prior.prior


def scope(record, row, donor):
    if (record["actual_source_closed_box"] != row or record["source_OPEN_index"] != row["index"]
            or record["source_OPEN_index"] == donor["source_OPEN_index"]
            or record["verified"] is not False or record["new_geometric_payments"] != 0
            or record["candidate_whole_roots_removed"] != 0
            or record["global_lower_bound_proved"] is not False
            or record["global_optimality_proved"] is not False
            or record["source_actual_partial_forests_and_paid_leaves_NOT_reset"] is not True
            or record["other_root_nodes_ownership_payments_and_acceptance_NOT_imported"] is not True
            or record["history_mode"] != "FRESH-DIAGNOSIS-ONLY"
            or record["borrowed_support_donor_root_index_DATA_only"] != donor["source_OPEN_index"]
            or record["borrowed_support_prefix_entries"] != len(donor["alternative_supports"])
            or record["alternative_supports"][:len(donor["alternative_supports"])] != donor["alternative_supports"]):
        raise ValueError("fresh arithmetic diagnostic changed actual ownership, donor prefix or zero-payment scope")


def negatives(original, kernel, arcs, row, record, donor):
    nodes, negative = record["nodes"], []
    split = next(index for index, node in enumerate(nodes) if node["kind"] == "SPLIT")
    leaf = next(leaf for leaf in record["arithmetic_ledger"] if leaf["kind"] == forest.KIND)

    def reject(label, call):
        try:
            call()
        except (ValueError, KeyError, TypeError, IndexError):
            negative.append(label)
        else:
            raise AssertionError("invalid actual fresh weighted forest accepted: "+label)

    def partition_change(mutation):
        bad = deepcopy(nodes)
        mutation(bad)
        forest.partition(original["matrix"], row, bad, BASE.independently_contract, True)

    reject("actual-fresh-closed-half-omitted", lambda: partition_change(
        lambda bad: bad[split].update(children=bad[split]["children"][:1])))
    reject("actual-fresh-halves-identified", lambda: partition_change(
        lambda bad: bad[split].update(children=[bad[split]["children"][0]]*2)))
    reject("actual-fresh-hidden-unreachable-node", lambda: partition_change(
        lambda bad: bad.append({"kind": "OPEN"})))
    reject("actual-fresh-boolean-child", lambda: partition_change(
        lambda bad: bad[split].update(children=[True, bad[split]["children"][1]])))
    reject("actual-fresh-split-unknown-proof-field", lambda: partition_change(
        lambda bad: bad[split].update(fake_payment=True)))
    reject("actual-fresh-unproved-leaf-mode", lambda: partition_change(
        lambda bad: bad.__setitem__(leaf["index"], {"kind": "UNPROVED-ENERGY"})))
    reject("actual-fresh-nonempty-leaf-called-EMPTY", lambda: partition_change(
        lambda bad: bad.__setitem__(leaf["index"], {"kind": "EMPTY"})))

    def certificate_change(mutation):
        bad = deepcopy(leaf["certificate"])
        mutation(bad)
        forest.prior.signed.bound(
            original["reference"], record["alternative_supports"][leaf["support_index"]],
            original["matrix"], leaf["lower"], leaf["upper"], bad, original["radius"], arcs)

    reject("actual-fresh-unknown-signed-proof-field", lambda: certificate_change(
        lambda bad: bad.update(fake_acceptance=True)))
    reject("actual-fresh-negative-positive-LDL", lambda: certificate_change(
        lambda bad: bad.update(signed_eta=["-1000000000000000"]*15)))
    reject("actual-fresh-infeasible-reference", lambda: certificate_change(
        lambda bad: bad["reference_turns"].__setitem__(0, "100")))
    reject("actual-fresh-negative-difference-dual", lambda: certificate_change(
        lambda bad: bad.update(difference_dual={"q": 1, "terms": [[0, 1, "-1"]]})))

    def support_change(mutation):
        bad = deepcopy(record["alternative_supports"][leaf["support_index"]])
        mutation(bad)
        BASE.support_gate(original, [bad])

    reject("actual-fresh-original-rod-omitted", lambda: support_change(
        lambda bad: bad["reference"]["edges"].pop()))
    reject("actual-fresh-nonpositive-rod-weight", lambda: support_change(
        lambda bad: bad["reference"]["weight_numerators"].__setitem__(0, "0")))
    reject("actual-fresh-false-exact-inverse", lambda: support_change(
        lambda bad: bad["inverse"]["inverse_numerators"][0].__setitem__(
            0, str(int(bad["inverse"]["inverse_numerators"][0][0])+1))))
    reject("actual-fresh-forged-original-fixed-weight-label", lambda: support_change(
        lambda bad: bad["reference"].update(
            alternative_weights_are_DIAGNOSTIC_not_original_accepted_support=False)))
    reject("actual-fresh-donor-positive-support-prefix-omitted", lambda:
           scope({**record, "alternative_supports": record["alternative_supports"][1:]}, row, donor))
    reject("actual-fresh-donor-root-ownership-transplanted", lambda:
           scope({**record, "source_OPEN_index": donor["source_OPEN_index"]}, row, donor))
    reject("actual-fresh-arithmetic-promoted-to-acceptance", lambda:
           scope({**record, "verified": True}, row, donor))
    reject("actual-fresh-strict-leaves-promoted-to-payments", lambda:
           scope({**record, "new_geometric_payments": 1}, row, donor))
    reject("actual-fresh-other-root-forest-imported", lambda:
           scope({**record, "other_root_nodes_ownership_payments_and_acceptance_NOT_imported": False}, row, donor))
    return negative


def main():
    parser = argparse.ArgumentParser()
    for name in ("resource", "resource-replay", "source", "support-diagnosis",
                 "support-controls", "diagnosis", "report"):
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
        raise ValueError("fresh weighted forest controls changed fixed arithmetic DATA identity")
    model = codec.gate(binding.read(args.resource / "CONTEXT.json")["typed_context"])
    original, kernel = model["original"], model["original_kernel"]
    record, donor = binding.read(args.diagnosis), binding.read(args.support_diagnosis)
    controls = binding.read(args.support_controls)
    digests = {path: binding.sha(path) for path in
               (args.diagnosis, args.support_diagnosis, args.support_controls)}
    if (record["schema"] != producer.SCHEMA
            or record["executed_producer_sha256"] != binding.sha(producer.__file__)
            or donor["schema"] != producer.support_producer.SCHEMA
            or donor["executed_producer_sha256"] != binding.sha(producer.support_producer.__file__)
            or record["borrowed_universal_support_data_sha256"] != digests[args.support_diagnosis]
            or record["borrowed_support_independent_controls_sha256"] != digests[args.support_controls]
            or controls["schema"] != leaf_controls.SCHEMA
            or controls["executed_test_sha256"] != binding.sha(leaf_controls.__file__)
            or controls["diagnosis_sha256"] != digests[args.support_diagnosis]
            or controls["latest_arithmetic_result"] != donor["arithmetic_result"]
            or controls["verified"] is not False or controls["new_geometric_payments"] != 0):
        raise ValueError("fresh actual arithmetic controls changed donor-DATA or producer lineage")
    for module in (forest, forest.prior, forest.prior.signed):
        if (record["modules"][linux(Path(module.__file__))] != binding.sha(module.__file__)
                or donor["modules"][linux(Path(module.__file__))] != binding.sha(module.__file__)):
            raise ValueError("fresh actual forest controls used changed exact original-rod arithmetic")
    accepted = binding.read(args.source / "VERIFIED.json")
    for name, digest in record["source_file_sha256"].items():
        if binding.sha(args.source / name) != digest or accepted["files"][name] != digest:
            raise ValueError("fresh controls changed actual source/root/history DATA")
    attempted = {item["source_OPEN_index"] for item in binding.read(args.source / "PROPOSAL.json")["forests"]}
    attempted.update(item["source_OPEN_index"] for item in binding.read(args.source / "SOURCE-ROOT-HISTORY.json"))
    if record["source_OPEN_index"] in attempted:
        raise ValueError("fresh controls would approve resetting an actual owned partial forest")
    row = next(row for row in binding.read(args.source / "PENDING-ANGLES.json")
               if row["index"] == record["source_OPEN_index"])
    scope(record, row, donor)
    arcs = binding.force.load_trig(args.resource)[0]
    result, pending, ledger = forest.replay(
        original, kernel, arcs, row, record["nodes"], record["alternative_supports"])
    if (result != record["arithmetic_result"] or pending != record["pending_closed_leaf_boxes"]
            or ledger != record["arithmetic_ledger"]):
        raise ValueError("entire actual fresh weighted forest, strict ledger or OPEN domains failed reconstruction")
    energy, local, empty = leaf_controls.leaf_controls(original, kernel, arcs, record)
    negative = negatives(original, kernel, arcs, row, record, donor)
    if len(negative) != 20:
        raise AssertionError("fresh actual weighted forest omitted a required rejection")
    checked_kernels = forest.support_gate(original, record["alternative_supports"])
    tiny = original["cap"]["known_candidate_tiny_angle_cells"]
    for candidate in checked_kernels:
        if candidate.get("original_candidate_92_rod_46_free_vertex_kernel") is not None:
            raise AssertionError("fresh universal support forged the original fixed-kernel label")
        test = BASE.direct_bound(candidate, [a for a, _ in tiny], [b for _, b in tiny],
                                 original["radius"], arcs)
        if test["radius_conditional_whole_angle_box_excluded"]:
            raise AssertionError("fresh universal support excludes the known feasible tiny candidate")
    for path, digest in digests.items():
        if binding.sha(path) != digest:
            raise ValueError("actual fresh forest or universal support DATA changed during independent testing")
    for name, digest in record["source_file_sha256"].items():
        if binding.sha(args.source / name) != digest:
            raise ValueError("actual source/history DATA changed during fresh independent controls")
    report = {
        "schema": SCHEMA, "verified": False,
        "source_OPEN_index": row["index"], "actual_source_closed_box": row,
        "diagnosis_sha256": digests[args.diagnosis],
        "universal_support_DATA_sha256": digests[args.support_diagnosis],
        "universal_support_independent_controls_sha256": digests[args.support_controls],
        "entire_actual_fresh_closed_root_partition_and_exact_ledger_reconstructed": True,
        "latest_arithmetic_result": result,
        "actual_strict_energy_leaves_independently_checked": energy,
        "independent_sine_square_feasible_corner_midpoint_checks": energy*3,
        "actual_original_LOCAL_leaves_reconstructed_not_declared_empty": local,
        "actual_exact_EMPTY_leaves_reconstructed": empty,
        "all_universal_positive_support_known_feasible_tiny_controls_passed": len(checked_kernels),
        "actual_rejection_controls_passed": negative,
        "other_root_nodes_ownership_payments_and_acceptance_NOT_imported": True,
        "all_borrowed_universal_positive_support_prefix_entries_preserved": len(donor["alternative_supports"]),
        "source_actual_partial_forests_and_paid_leaves_NOT_reset": True,
        "retained_OPEN_leaves": len(pending),
        "entire_root_arithmetic_cover_completed": not pending,
        "source_file_sha256": record["source_file_sha256"],
        "arithmetic_only_NOT_complete_latest_model_source_history_or_geometry_acceptance": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "tested_modules": {Path(module.__file__).name: binding.sha(module.__file__)
                           for module in (forest, forest.prior, forest.prior.signed,
                                          BASE, codec, leaf_controls, producer)},
        "executed_test_sha256": binding.sha(__file__),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({"actual_fresh_weighted_forest_independent_controls_completed": True,
                      "root": row["index"], "strict_energy_leaves": energy,
                      "original_LOCAL_leaves": local, "OPEN_leaves": len(pending),
                      "actual_rejections": len(negative), "verified": False,
                      "new_geometric_payments": 0}), flush=True)


if __name__ == "__main__":
    main()
