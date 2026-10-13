"""Distinct full-source geometry acceptance of newest root25/grown-root28 forests.

No diagnostic producer or typed arithmetic resource is imported or executed.
The COMPLETE actual source replay occurs before every forest geometry bound.
"""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import inspect
import json
from pathlib import Path
import sys
from types import ModuleType

from audit_prefix_partition import linux
import n26_latest_candidate_complete_source_replay as source_backend
import n26_mixed_full134rod_support_forest as forest
import verify_conditional_force_stage as binding


INPUT_SCHEMA = "N26-latest-signed-grown-full134rod-frozen-forest-input-bindings-v1"
SCHEMA = "N26-accepted-latest-signed-grown-full134rod-partial-forests-v1"
CHECKER = "verify_latest_candidate_signed_full134rod_forests.py"
MODES = ["latest-root25-extended-signed", "latest-root28-grown-full134rod"]
WORKSPACE = binding.local_path("/mnt/c/Users/Administrator/Documents/Codex/2026-10-09/n-26")
LEGACY_ROOT25_SEED_SCHEMA = "N26-unaccepted-preserved-fresh-root-support-cost-forest-continuation-v1"
RECORDS = {
    25: ("ROOT25-DIAGNOSIS.json", "ROOT25-CONTROLS.json", "ROOT25-SEED.json"),
    28: ("ROOT28-GROWN-DIAGNOSIS.json", "ROOT28-GROWN-CONTROLS.json", "ROOT28-V8.json"),
}
REQUIRED_DIAGNOSES = {
    25: "N26-unaccepted-checked-root25-support-cost-continuation-v1",
    28: "N26-unaccepted-checked-v8-grown-source-root-full134rod-intersection-forest-v1",
}
REQUIRED_CONTROLS = {
    25: "N26-independent-actual-checked-root25-support-cost-continuation-controls-v1",
    28: "N26-independent-actual-v8-grown-full134rod-intersection-forest-controls-v1",
}
PRODUCERS = {
    25: "continue_checked_root25_support_cost_forest.py",
    28: "continue_checked_root28_grown_full134rod_intersections.py",
}
TESTERS = {
    25: "test_checked_root25_support_cost_continuation.py",
    28: "test_checked_root28_grown_full134rod_intersections.py",
}


def executed_modules():
    """Transitive local import owners, including from-import function owners."""
    queue = [sys.modules[__name__], source_backend, forest, binding,
             *list(sys.modules.values())]
    seen, result = set(), {}
    for module in queue:
        if not isinstance(module, ModuleType):
            continue
        if module.__name__ in seen:
            continue
        seen.add(module.__name__)
        filename = getattr(module, "__file__", None)
        if filename is None:
            continue
        path = Path(filename).resolve()
        try:
            path.relative_to(WORKSPACE.resolve())
        except ValueError:
            continue
        if path.suffix != ".py":
            continue
        if path.name in result and binding.sha(result[path.name]) != binding.sha(path):
            raise ValueError("latest geometry imports different local versions under one file name")
        result[path.name] = path
        for value in vars(module).values():
            if isinstance(value, ModuleType):
                queue.append(value)
            elif inspect.isfunction(value) or inspect.isclass(value):
                owner = sys.modules.get(getattr(value, "__module__", None))
                if owner is not None:
                    queue.append(owner)
    return result


def unpaid_scope(record, *, legacy_seed=False):
    if (record["verified"] is not False or record["new_geometric_payments"] != 0
            or record["candidate_whole_roots_removed"] != 0
            or record["global_lower_bound_proved"] is not False
            or record["global_optimality_proved"] is not False):
        raise ValueError("latest forest discovery/control was promoted to a geometry or global proof")
    if "n27_started" in record:
        if record["n27_started"] is not False:
            raise ValueError("latest forest discovery/control changed the n-specific status")
    elif not (legacy_seed and record["schema"] == LEGACY_ROOT25_SEED_SCHEMA
              and type(record["source_OPEN_index"]) is int and record["source_OPEN_index"] == 25):
        raise ValueError("only the specifically identified historical root25-v2 baseline omits n27 status")


def retention(seed, record):
    """Pure immutable old node/support/strict-ledger contract; no geometry."""
    unpaid_scope(seed, legacy_seed=True)
    unpaid_scope(record)
    if (type(seed["source_OPEN_index"]) is not int
            or record["source_OPEN_index"] != seed["source_OPEN_index"]
            or record["actual_source_closed_box"] != seed["actual_source_closed_box"]
            or record["source_file_sha256"] != seed["source_file_sha256"]):
        raise ValueError("latest forest continuation changed the exact source/history owner")
    # Historical old92-only records have NO full134rod field. Its absent
    # table is explicitly empty for this structural prefix contract, not a
    # fabricated new support/kernel or an admitted grown proof mode.
    if (len(record["nodes"]) < len(seed["nodes"])
            or record["alternative_supports"][:len(seed["alternative_supports"])]
            != seed["alternative_supports"]
            or record.get("full134rod_supports", [])[:len(seed.get("full134rod_supports", []))]
            != seed.get("full134rod_supports", [])
            or any(node["kind"] != "OPEN" and node != record["nodes"][number]
                   for number, node in enumerate(seed["nodes"]))):
        raise ValueError("latest geometry continuation reset an old node or either support prefix")
    old_ledger = {leaf["index"]: leaf for leaf in seed["arithmetic_ledger"]}
    new_ledger = {leaf["index"]: leaf for leaf in record["arithmetic_ledger"]}
    if (len(old_ledger) != len(seed["arithmetic_ledger"])
            or len(new_ledger) != len(record["arithmetic_ledger"])
            or any(new_ledger.get(index) != leaf for index, leaf in old_ledger.items())):
        raise ValueError("latest geometry continuation reset or repeated a strict old ledger")
    return len(seed["nodes"]), len(seed["alternative_supports"]), len(old_ledger)


def root_gate(incoming, records):
    if not isinstance(incoming, list) or len({row["index"] for row in incoming}) != len(incoming):
        raise ValueError("latest geometry source has duplicate whole-root ownership")
    by_index = {row["index"]: row for row in incoming}
    if set(records) != {25, 28}:
        raise ValueError("this distinct geometry interface requires BOTH actual newest root25 and root28")
    for index, record in records.items():
        if (type(record["source_OPEN_index"]) is not int
                or record["source_OPEN_index"] != index or index not in by_index
                or record["actual_source_closed_box"] != by_index[index]):
            raise ValueError("latest forest reopened a paid root or clipped the actual entire source root")
        unpaid_scope(record)
    return by_index


def required_role_gate(index, record, control):
    unpaid_scope(record)
    unpaid_scope(control)
    if (record["schema"] != REQUIRED_DIAGNOSES[index]
            or control["schema"] != REQUIRED_CONTROLS[index]):
        raise ValueError("latest geometry requires the ACTUAL distinct newest producer/control roles")


def records_gate(records, controls, seeds, digests, copied, incoming):
    root_gate(incoming, records)
    retained = {}
    for index in (25, 28):
        record, control, seed = records[index], controls[index], seeds[index]
        required_role_gate(index, record, control)
        record_name, _, seed_name = RECORDS[index]
        if (control["diagnosis_sha256"] != digests[record_name]
                or control["source_file_sha256"] != record["source_file_sha256"]
                or record["executed_producer_sha256"] != copied[PRODUCERS[index]]
                or control["executed_test_sha256"] != copied[TESTERS[index]]
                or control["latest_arithmetic_result"] != record["arithmetic_result"]
                or control["retained_OPEN_leaves"] != len(record["pending_closed_leaf_boxes"])):
            raise ValueError("latest forest lacks its ACTUAL own producer and independent controls")
        for path, digest in record["modules"].items():
            if copied.get(binding.local_path(path).name) != digest:
                raise ValueError("latest diagnostic's actual arithmetic module bytes are not frozen")
        for name, digest in control["tested_modules"].items():
            if copied.get(name) != digest:
                raise ValueError("latest independent arithmetic used different frozen modules")
        retained[index] = retention(seed, record)
        if index == 25:
            if (record["old_arithmetic_forest_sha256"] != digests[seed_name]
                    or control["seed_sha256"] != digests[seed_name]
                    or control["both_entire_actual_closed_root_partitions_and_exact_ledgers_reconstructed"]
                    is not True
                    or control["all_previous_non_OPEN_nodes_positive_supports_and_proved_ledgers_preserved_identically"]
                    is not True
                    or len(control["actual_rejection_controls_passed"]) != 20
                    or record.get("full134rod_supports", [])):
                raise ValueError("root25 latest-v3 lineage or distinct old92 signed mode changed")
        else:
            if (record["actual_checked_latest_v8_forest_sha256"] != digests[seed_name]
                    or control["actual_checked_latest_v8_forest_sha256"] != digests[seed_name]
                    or record["actual_checked_latest_v8_controls_sha256"]
                    != digests["ROOT28-V8-CONTROLS.json"]
                    or control["actual_checked_latest_v8_controls_sha256"]
                    != digests["ROOT28-V8-CONTROLS.json"]
                    or control["tested_own_producer_sha256"] != copied[PRODUCERS[index]]
                    or control["entire_old_and_new_actual_closed_partitions_and_exact_ledgers_reconstructed"]
                    is not True
                    or control["independent_BFS_all_nodes_and_actual_latest_OPEN_parent_walks_checked"]
                    is not True
                    or control["both_closed_halves_shared_boundaries_and_all_remainders_reconstructed"]
                    is not True
                    or len(control["actual_latest_lineage_grown_region_subset_history_and_payment_guards_rejected"])
                    != 23
                    or control["fresh_grown_full134rod_strict_whole_closed_targets_independently_checked"]
                    != len(record["fresh_actual_latest_OPEN_intersection_targets"])
                    or control["grown_region_evidence_and_fresh_selection"]
                    != record["grown_region_evidence_and_fresh_selection"]
                    or not isinstance(record["full134rod_supports"], list)
                    or not record["full134rod_supports"]):
                raise ValueError("root28 actual grown-v9 was replaced by an old fixture or lost ancestry controls")
    return retained


def metadata_gate(folder):
    manifest = binding.read(folder / "MANIFEST.json")
    if (manifest["schema"] != INPUT_SCHEMA or manifest["radius_scope"] != "same-root-Rstar"
            or manifest["acceptance_checker_file"] != CHECKER
            or manifest["supported_forest_modes"] != MODES
            or manifest["complete_latest_source_model_history_replay_required"] is not True
            or manifest["typed_resource_not_a_source_replay_substitute"] is not True
            or manifest["latest_grown_v9_and_root25_v3_NOT_reset"] is not True):
        raise ValueError("latest forest geometry changed its distinct executor, full scope or history policy")
    copied = manifest["copied_files"]
    for name, digest in copied.items():
        if binding.sha(folder / name) != digest:
            raise ValueError("latest forest sealed input changed: "+name)
    for name, path in executed_modules().items():
        if copied.get(name) != binding.sha(path):
            raise ValueError("latest geometry imports unsealed or different source/arithmetic code: "+name)
    if binding.sha(__file__) != copied[CHECKER]:
        raise ValueError("latest forest did not execute its OWN frozen geometry main")
    records = {index: binding.read(folder / RECORDS[index][0]) for index in (25, 28)}
    controls = {index: binding.read(folder / RECORDS[index][1]) for index in (25, 28)}
    seeds = {index: binding.read(folder / RECORDS[index][2]) for index in (25, 28)}
    incoming = binding.read(folder / "SOURCE-PENDING-ANGLES.json")
    digests = {name: copied[name] for name in (
        *(name for names in RECORDS.values() for name in names), "ROOT28-V8-CONTROLS.json")}
    retained = records_gate(records, controls, seeds, digests, copied, incoming)
    v8_control = binding.read(folder / "ROOT28-V8-CONTROLS.json")
    unpaid_scope(v8_control)
    if (v8_control["schema"] != "N26-independent-actual-checked-support-cost-continuation-controls-v1"
            or v8_control["diagnosis_sha256"] != digests["ROOT28-V8.json"]
            or v8_control["source_file_sha256"] != seeds[28]["source_file_sha256"]
            or len(v8_control["actual_rejection_controls_passed"]) != 20):
        raise ValueError("latest grown geometry lost the actual v8 independent baseline")
    guard = binding.read(folder / "INTERFACE-CONTRACT-CONTROLS.json")
    if (guard["schema"] != "N26-independent-latest-signed-full134rod-ownership-retention-role-contracts-v1"
            or guard["verified"] is not False or guard["new_geometric_payments"] != 0
            or guard["candidate_whole_roots_removed"] != 0
            or guard["actual_v8_was_REJECTED_as_grown_v9_NOT_used_to_replace_it"] is not True
            or guard["actual_grown_v9_and_its_automatic_controls_NOT_replaced_by_this_baseline_test"] is not True
            or guard["ENTIRE_source_model_history_and_latest_forest_geometry_acceptance_NOT_executed"] is not True
            or len(guard["actual_ownership_unpaid_scope_retention_and_producer_role_guards_rejected"]) != 31
            or guard["tested_own_full_geometry_executor_sha256"] != binding.sha(__file__)
            or guard["tested_complete_source_backend_sha256"] != binding.sha(source_backend.__file__)
            or guard["executed_test_sha256"] != copied["test_latest_signed_full134_geometry_contracts.py"]
            or guard["actual_root25_v2_to_v3_retention_counts_checked"] != list(retained[25])
            or guard["actual_root28_v8_baseline_self_retention_mechanism_checked"] != [
                len(seeds[28]["nodes"]), len(seeds[28]["alternative_supports"]),
                len(seeds[28]["arithmetic_ledger"])]):
        raise ValueError("latest geometry lacks actual ownership/retention/producer-role guards")
    for key, filename in (
        ("root25-seed", "ROOT25-SEED.json"), ("root25-diagnosis", "ROOT25-DIAGNOSIS.json"),
        ("root25-controls", "ROOT25-CONTROLS.json"), ("root28-v8", "ROOT28-V8.json"),
        ("root28-v8-controls", "ROOT28-V8-CONTROLS.json"),
    ):
        if guard["actual_input_sha256"][key] != copied[filename]:
            raise ValueError("latest geometry contracts tested different actual histories")
    proof_source = binding.local_path(manifest["arithmetic_proof_time_source"])
    proof_acceptance = binding.read(proof_source / "VERIFIED.json")
    if (binding.sha(proof_source / "VERIFIED.json") != manifest["proof_time_source_acceptance_sha256"]
            or proof_acceptance != binding.read(folder / "PROOF-SOURCE-ACCEPTANCE.json")):
        raise ValueError("latest forest arithmetic DATA source provenance changed")
    if (guard["actual_source_acceptance_sha256"] != manifest["proof_time_source_acceptance_sha256"]
            or guard["actual_source_pending_sha256"] != proof_acceptance["files"]["PENDING-ANGLES.json"]):
        raise ValueError("latest geometry contracts changed actual proof-time source DATA identity")
    for record in (*records.values(), *seeds.values()):
        for name, digest in record["source_file_sha256"].items():
            if (proof_acceptance["files"].get(name) != digest
                    or binding.sha(proof_source / name) != digest):
                raise ValueError("latest forest changed actual old source/root/history DATA")
    return manifest, records, controls, seeds, retained


def input_gate(folder):
    manifest, records, controls, seeds, retained = metadata_gate(folder)
    paths = tuple(binding.local_path(manifest[key]) for key in (
        "source", "source_replay", "formal_current", "formal_final",
        "candidate_owner_current", "candidate_owner_final"))
    for key, name in (
        ("formal_current", "SOURCE-CURRENT-AUDIT.json"),
        ("formal_final", "SOURCE-FINAL-DIGEST-RECHECK.json"),
        ("candidate_owner_current", "SOURCE-OWNER-CURRENT.json"),
        ("candidate_owner_final", "SOURCE-OWNER-FINAL.json"),
    ):
        path = binding.local_path(manifest[key])
        if (binding.sha(path) != manifest[key+"_sha256"]
                or binding.read(path) != binding.read(folder / name)):
            raise ValueError("latest geometry changed a formal or candidate-owner proof-time pair")
    actual, original_values, incoming, inventory, old_payments, history, layer = source_backend.gate(*paths)
    if (binding.sha(paths[0] / "VERIFIED.json") != manifest["source_acceptance_sha256"]
            or actual != binding.read(folder / "SOURCE-ACCEPTANCE.json")
            or incoming != binding.read(folder / "SOURCE-PENDING-ANGLES.json")
            or [history[index] for index in sorted(history)]
            != binding.read(folder / "SOURCE-ROOT-HISTORY.json")):
        raise ValueError("latest geometry lost actual full source acceptance, roots or newest accepted history")
    formal = binding.read(paths[2])
    proof_source = binding.local_path(manifest["arithmetic_proof_time_source"])
    for path in (proof_source / "VERIFIED.json",
                 *(proof_source / name for name in records[25]["source_file_sha256"]),
                 *(proof_source / name for name in records[28]["source_file_sha256"])):
        if formal["files"].get(linux(path)) != binding.sha(path):
            raise ValueError("forest arithmetic proof-time source is not an identically bound current ancestor")
        inventory.append(path)
    root_gate(incoming, records)
    for index in (25, 28):
        prior = history.get(index)
        if prior is not None:
            nodes = records[index]["nodes"]
            if (len(nodes) < len(prior["nodes"])
                    or any(node["kind"] != "OPEN" and nodes[number] != node
                           for number, node in enumerate(prior["nodes"]))):
                raise ValueError("new forest would reset an ACTUALLY accepted newer per-root history")
    return (manifest, records, controls, seeds, retained, actual, original_values,
            incoming, inventory, old_payments, history, layer)


def reconstruct(original_values, row, record, full=False):
    original, kernel, arcs = original_values[3], original_values[5], original_values[6]
    if full:
        result, pending, ledger = forest.replay(
            original, kernel, arcs, row, record["nodes"], record["alternative_supports"],
            record["full134rod_supports"])
    else:
        result, pending, ledger = forest.old.replay(
            original, kernel, arcs, row, record["nodes"], record["alternative_supports"])
    if (result != record["arithmetic_result"]
            or pending != record["pending_closed_leaf_boxes"] or ledger != record["arithmetic_ledger"]):
        raise ValueError("latest actual geometry model failed ENTIRE forest/strict-ledger reconstruction")
    return result, pending, ledger


def derive(values):
    _, records, _, seeds, _, _, original_values, incoming, _, _, history, _ = values
    by_index = root_gate(incoming, records)
    payments, classified, ledgers = [], [], []
    remaining_history = deepcopy(history)
    for index in (25, 28):
        row, record = by_index[index], records[index]
        # Independently replay the actual OLD baseline with the TRUE freshly
        # reconstructed source model before extending it; never a typed cache.
        reconstruct(original_values, row, seeds[index])
        result, pending, ledger = reconstruct(original_values, row, record, full=index == 28)
        retention(seeds[index], {**record, "arithmetic_ledger": ledger})
        closed = not pending
        strictly_empty = closed and result["counts"]["LOCAL"] == 0
        classification = {
            "source_OPEN_index": index, "actual_source_closed_box": row,
            "forest_mode": MODES[0 if index == 25 else 1],
            "source_candidate_root_fully_lower_bounded": closed,
            "source_candidate_root_strictly_empty": strictly_empty,
            "fresh_full_source_geometry_result": result,
            "unresolved_closed_leaf_boxes": len(pending),
        }
        classified.append(classification)
        ledgers.append({"source_OPEN_index": index, "exact_closed_leaf_ledger": ledger})
        if closed:
            payments.append(classification)
            remaining_history.pop(index, None)
        else:
            remaining_history[index] = {
                "source_OPEN_index": index, "actual_source_closed_box": row,
                "forest_mode": classification["forest_mode"], "nodes": record["nodes"],
                "alternative_supports": record["alternative_supports"],
                "full134rod_supports": record.get("full134rod_supports", []),
                "accepted_source_classification": classification,
                "strict_closed_leaf_ledger": ledger,
                "prior_accepted_history_retained_identically": history.get(index),
                "actual_latest_arithmetic_baseline_retained_identically": seeds[index],
            }
        print(json.dumps({"actual_entire_latest_forest_geometry_replayed": index,
                          "remaining_OPEN_leaves": len(pending),
                          "new_whole_root_lower_bound": closed}), flush=True)
    indices = {row["source_OPEN_index"] for row in payments}
    remaining = [row for row in incoming if row["index"] not in indices]
    retained = [remaining_history[index] for index in sorted(remaining_history)]
    if (len(payments)+len(remaining) != len(incoming)
            or any(row["source_candidate_root_strictly_empty"]
                   and row["fresh_full_source_geometry_result"]["counts"]["LOCAL"] for row in payments)):
        raise ValueError("latest forest lost a whole root or falsely emptied original LOCAL equality")
    return payments, remaining, classified, ledgers, retained


def controls(values):
    _, records, _, seeds, _, _, original_values, incoming, _, _, history, _ = values
    rejected = []

    def reject(label, call):
        try:
            call()
        except (ValueError, KeyError, TypeError, IndexError):
            rejected.append(label)
        else:
            raise AssertionError("invalid actual latest geometry forest accepted: "+label)

    for index in (25, 28):
        seed, record = seeds[index], records[index]
        old_ledger_index = seed["arithmetic_ledger"][0]["index"]
        for label, mutation in (
            ("discovery-promoted-to-current-geometry", lambda bad: bad.update(verified=True)),
            ("proper-subsets-promoted-to-whole-root-payment", lambda bad:
             bad.update(candidate_whole_roots_removed=1)),
            ("newest-positive-support-prefix-reset", lambda bad: bad["alternative_supports"].pop(0)),
            ("newest-strict-ledger-reset", lambda bad, old_ledger_index=old_ledger_index:
             bad.update(arithmetic_ledger=[
                 leaf for leaf in bad["arithmetic_ledger"] if leaf["index"] != old_ledger_index])),
            ("newest-nonOPEN-node-reset", lambda bad:
             bad["nodes"].__setitem__(0, {"kind": "OPEN"})),
        ):
            bad = deepcopy(record)
            mutation(bad)
            reject(str(index)+"-"+label, lambda bad=bad, seed=seed: retention(seed, bad))
        bad_records = dict(records)
        bad_records[index] = deepcopy(record)
        bad_records[index]["actual_source_closed_box"]["sharp_lower"][0] = "-100"
        reject(str(index)+"-entire-current-root-clipped-or-escaped",
               lambda bad_records=bad_records: root_gate(incoming, bad_records))
        row = record["actual_source_closed_box"]
        for label, mutation in (
            ("hidden-unreachable-OPEN-remainder", lambda nodes: nodes.append({"kind": "OPEN"})),
            ("one-closed-root-half-lost", lambda nodes: nodes[0].update(children=nodes[0]["children"][:1])),
            ("closed-halves-identified", lambda nodes:
             nodes[0].update(children=[nodes[0]["children"][0]]*2)),
        ):
            bad_nodes = deepcopy(record["nodes"])
            mutation(bad_nodes)
            reject(str(index)+"-"+label, lambda bad_nodes=bad_nodes, row=row:
                   forest.partition(original_values[3]["matrix"], row, bad_nodes,
                                    forest.old.prior.prior.independently_contract, True))
    negative_roots = {25: records[25]}
    reject("latest-root28-omitted-for-an-easier-root25-only-interface",
           lambda: root_gate(incoming, negative_roots))
    bad = deepcopy(records)
    bad[28]["source_OPEN_index"] = True
    reject("boolean-current-root-owner", lambda: root_gate(incoming, bad))
    bad = deepcopy(records)
    bad[28]["source_OPEN_index"] = 1794
    reject("previously-paid-original-LOCAL-root-reopened", lambda: root_gate(incoming, bad))
    positive = source_backend.mixed.checker.constant.prior_checker.base.source.tiny_control(original_values)
    if (positive["known_feasible_root_tiny_box_not_energy_excluded"] is not True
            or positive["original_LOCAL_leaf_and_52_coordinate_allowance_preserved"] is not True):
        raise ValueError("latest geometry lost actual feasible-root or original LOCAL positive control")
    if len(rejected) != 21:
        raise ValueError("latest geometry omitted an actual whole-partition/retention/ownership control")
    return positive, rejected


def verify(folder, report_path):
    if report_path.exists():
        raise FileExistsError(report_path)
    values = input_gate(folder)
    manifest, _, _, _, retention_counts, _, original_values, incoming, inventory, _, history, layer = values
    payments, remaining, classified, ledgers, retained = derive(values)
    positive, negatives = controls(values)
    # Dynamic local imports and every originally bound current byte must
    # still match AFTER the complete source/forest computation, not merely
    # a newly computed digest of possibly changed external input.
    metadata_gate(folder)
    formal = binding.read(binding.local_path(manifest["formal_current"]))
    for text, digest in formal["files"].items():
        if binding.sha(text) != digest:
            raise ValueError("latest geometry original formal dependency changed during execution")
    outputs = {
        "ROOT-PAYMENTS.json": payments, "PENDING-ANGLES.json": remaining,
        "ROOT-CLASSIFICATION.json": classified, "LOWER-LEDGER.json": ledgers,
        "REMAINING-ROOT-HISTORY.json": retained, "POSITIVE-CONTROLS.json": positive,
        "CERTIFICATE.json": {
            "schema": SCHEMA+"-certificate", "radius_scope": "same-root-Rstar",
            "discharged_actual_source_root_indices": [row["source_OPEN_index"] for row in payments],
            "all_uncovered_whole_roots_and_latest_partial_histories_retained": True,
            "original_LOCAL_lower_bound_is_NOT_emptiness": True,
        },
    }
    for name, data in outputs.items():
        binding.area.base.publish_or_match(folder / name, data)
    inventory.extend(folder / name for name in manifest["copied_files"])
    unique = {linux(Path(path)): Path(path) for path in inventory}
    digests = {text: binding.sha(path) for text, path in unique.items()}
    for text, digest in digests.items():
        if binding.sha(text) != digest:
            raise ValueError("latest geometry actual full source/dependency changed during final binding")
    for key in ("formal_current", "formal_final", "candidate_owner_current", "candidate_owner_final"):
        if binding.sha(binding.local_path(manifest[key])) != manifest[key+"_sha256"]:
            raise ValueError("latest geometry formal/source-owner pair changed during execution")
    report = {
        "schema": SCHEMA, "verified": True, "radius_scope": "same-root-Rstar",
        "radius_upper": str(original_values[3]["radius"]),
        "accepted_forest_modes": MODES, "actual_full_source_replay": layer,
        "source_acceptance_sha256": manifest["source_acceptance_sha256"],
        "source_actual_remaining_candidate_roots": len(incoming),
        "new_whole_candidate_source_roots_lower_bounded": len(payments),
        "new_strictly_empty_source_roots": sum(row["source_candidate_root_strictly_empty"] for row in payments),
        "unresolved_closed_angle_boxes": len(remaining),
        "actual_latest_root25_v3_and_root28_grown_v9_replayed_not_reset": True,
        "actual_old_baselines_and_every_strict_ledger_freshly_reconstructed": True,
        "actual_latest_baseline_retention_counts": retention_counts,
        "remaining_root_partial_histories_retained": len(retained),
        "retained_prior_accepted_history_entries": len(history),
        "strict_closed_leaf_ledgers_verified_here": sum(len(row["exact_closed_leaf_ledger"]) for row in ledgers),
        "original_52_coordinate_local_allowance_unchanged": "7/800000",
        "LOCAL_equality_feasible_regions_never_declared_empty": True,
        "source_identity_and_arithmetic_controls_NOT_used_as_geometry_substitutes": True,
        "negative_controls_rejected": negatives,
        "current_global_combinatorial_frontier_nodes_removed": 0,
        "actual_publication_current_adoption_and_independent_final_still_required": True,
        "unrestricted_reduction_final_joint_acceptance": False,
        "full_catalog_complete": False, "global_lower_bound_proved": False,
        "global_optimality_proved": False, "n27_started": False,
        "files": {name: binding.sha(folder / name) for name in dict.fromkeys(
            ["MANIFEST.json", *manifest["copied_files"], *outputs])},
        "source_files": digests, "executed_checker_file": CHECKER,
        "executed_checker_sha256": binding.sha(__file__),
    }
    with report_path.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({key: value for key, value in report.items()
                      if key not in ("files", "source_files")}, indent=2), flush=True)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    verify(args.input, args.report)


if __name__ == "__main__":
    main()
