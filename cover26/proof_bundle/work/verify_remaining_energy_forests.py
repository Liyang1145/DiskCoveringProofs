"""Exact closure of every retained current OPEN by new full-graph energy forests."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path
import subprocess
import sys

from audit_prefix_partition import linux
import n26_hybrid_box_forest as forest
import n26_quadratic_energy_minorant as energy
import verify_current_force_open_overlay as current
import verify_last_hard_hybrid_overlay as hybrid
import verify_quadratic_type_overlay as quadratic
import verify_selected_type_trees as typed
import verify_terminal_catalog as catalog


read, sha = typed.read, catalog.sha


def remap_nodes(nodes, offset, count):
    result = deepcopy(nodes)
    for node in result:
        if node.get("kind") == "QUADRATIC_ENERGY":
            k = node["kernel_index"]
            if type(k) is not int or not 0 <= k < count:
                raise ValueError("remaining discovery energy leaf has invalid local kernel ownership")
            node["kernel_index"] += offset
    return result


def source_gate(folder):
    manifest = read(folder / "MANIFEST.json")
    if manifest["schema"] != "N26-remaining-current-OPEN-energy-forest-bindings-v1":
        raise ValueError("wrong remaining forest bindings")
    for name, digest in manifest["copied_files"].items():
        if sha(folder / name) != digest:
            raise ValueError("remaining forest sealed input changed: " + name)
    source = catalog.local_path(manifest["source_overlay"])
    accepted, inventory = typed.bound(source)
    replay = catalog.local_path(manifest["source_overlay_replay"])
    audit_path = catalog.local_path(manifest["source_current_audit"])
    audit = read(audit_path)
    if (read(replay) != accepted or read(folder / "SOURCE-ACCEPTANCE.json") != accepted
            or sha(source / "VERIFIED.json") != manifest["source_acceptance_sha256"]
            or sha(audit_path) != manifest["source_current_audit_sha256"]
            or read(folder / "SOURCE-CURRENT-AUDIT.json") != audit
            or not audit["current_bound_bytes_rechecked"]
            or not audit["actual_current_whole_OPEN_force_standalone_replay_matched_and_bound"]
            or audit["global_optimality_proved"] is not False
            or audit["files"].get(linux(source / "VERIFIED.json")) != sha(source / "VERIFIED.json")
            or audit["radius_scope"] != accepted["radius_scope"]
            or audit["r_strict_interval"] != accepted["r_strict_interval"]):
        raise ValueError("remaining forest lacks actual matching current acceptance/replay/audit")
    for text, digest in audit["files"].items():
        path = catalog.local_path(text)
        if sha(path) != digest:
            raise ValueError("remaining forest prior current dependency changed")
        inventory.append(path)
    inventory.extend([replay, audit_path])
    for module in (current, hybrid, quadratic, energy, forest):
        if sha(module.__file__) != accepted["files"][Path(module.__file__).name]:
            raise ValueError("remaining forest executed different sealed arithmetic")
    print("Reconstructing the current force layer and every prior selected proof.", flush=True)
    v = current.source_gate(source)
    inventory.extend(v["inventory"])
    classes, pending, payments, unpaid = current.derive(
        v["classes"], v["pending"], v["domains"], v["certificate"], v["radius"], v["arcs"])
    frontier, removal, closed, member_count = current.transfer(v, classes, pending)
    hybrid.match(source, (("CLASSIFICATION.json", classes), ("PENDING-TYPES.json", pending),
                          ("LOWER-LEDGER.json", payments), ("UNPAID-CHECKS.json", unpaid),
                          ("RSTAR-COMPETITOR-FRONTIER.json", frontier),
                          ("CONDITIONAL-REMOVAL-LEDGER.json", removal)))
    if (len(payments) != accepted["new_strict_whole_current_OPEN_force_payments"]
            or closed != accepted["new_complete_type_exclusions"]
            or member_count != accepted["new_current_terminal_paths_removed"]):
        raise ValueError("remaining forest current force acceptance did not reconstruct")
    index = read(folder / "DISCOVERY-INDEX.json")
    old_hash, registry_hash, radius, _, _, _, older_pending = v["proposal_gate_inputs"]
    if (index["schema"] != "N26-unaccepted-actual-remaining-OPEN-hybrid-batch-index-v1"
            or index["verified"] is not False or index["global_optimality_proved"] is not False
            or index["radius_scope"] != typed.SCOPE
            or index["current_source_acceptance_sha256"] != manifest["source_acceptance_sha256"]
            or index["older_discovery_acceptance_sha256"] != old_hash
            or index["registry_acceptance_sha256"] != registry_hash):
        raise ValueError("remaining forest batch changed its current/older lineage or radius scope")
    by_group = {row["group_index"]: row for row in classes}
    now = {row["group_index"]: {box["index"]: box for box in row["closed_OPEN_boxes"]} for row in pending}
    before = {row["group_index"]: {box["index"]: box for box in row["closed_OPEN_boxes"]} for row in older_pending}
    expected_keys = {(i, parent) for i, boxes in now.items() for parent in boxes}
    paid_keys = {(row["group_index"], row["source_OPEN_index"]) for row in payments}
    sibling_lineage = []
    for i in sorted({key[0] for key in expected_keys}):
        if (set(before[i]) - set(now[i]) != {parent for j, parent in paid_keys if j == i}
                or not set(now[i]) <= set(before[i])
                or any(now[i][parent] != before[i][parent] for parent in now[i])):
            raise ValueError("older-to-current differences are not exactly verified sibling force payments")
        sibling_lineage.append({"group_index": i, "older_OPEN": len(before[i]),
                                "current_OPEN": len(now[i]), "verified_paid_siblings": len(before[i]) - len(now[i])})
    if len(index["records"]) != len(manifest["root_inputs"]):
        raise ValueError("remaining forest has omitted or hidden discovery roots")
    seen, expected_forests, kernels = set(), [], []
    for record, copied in zip(index["records"], manifest["root_inputs"]):
        i, parent = record["group_index"], record["source_OPEN_index"]
        key = i, parent
        if (type(i) is not int or type(parent) is not int or key in seen or key not in expected_keys
                or copied["group_index"] != i or copied["source_OPEN_index"] != parent):
            raise ValueError("remaining forest duplicates or substitutes a current OPEN owner")
        seen.add(key)
        discovery_file, kernel_file = folder / copied["discovery"], folder / copied["kernels"]
        if (sha(discovery_file) != record["proposal_sha256"]
                or sha(kernel_file) != record["kernels_sha256"]):
            raise ValueError("remaining forest copied different actual discovery or kernel bytes")
        discovery, new_kernels = read(discovery_file), read(kernel_file)
        if (discovery["schema"] != "N26-unaccepted-hybrid-force-quadratic-residual-forest-v1"
                or discovery["verified"] is not False or discovery["global_optimality_proved"] is not False
                or discovery["radius_scope"] != typed.SCOPE
                or discovery["source_acceptance_sha256"] != old_hash
                or discovery["source_registry_acceptance_sha256"] != registry_hash
                or discovery["group_index"] != i or discovery["source_OPEN_index"] != parent
                or discovery["spec"] != by_group[i]["spec"]
                or discovery["source_closed_OPEN_box"] != now[i][parent]
                or discovery["source_closed_OPEN_box"] != before[i][parent]
                or discovery["kernels_sha256"] != sha(kernel_file)
                or not isinstance(new_kernels, list)):
            raise ValueError("remaining discovery changed actual full type, current parent or explicit older source")
        for row in new_kernels:
            if (set(row) != {"group_index", "certificate"} or type(row["group_index"]) is not int
                    or row["group_index"] != i or row["certificate"]["spec"] != by_group[i]["spec"]):
                raise ValueError("remaining kernel changed its full graph or canonical owner")
        offset = len(kernels)
        expected_forests.append({key: discovery[key] for key in
                                ("group_index", "spec", "source_OPEN_index", "source_closed_OPEN_box")})
        expected_forests[-1]["nodes"] = remap_nodes(discovery["nodes"], offset, len(new_kernels))
        kernels.extend(new_kernels)
    if seen != expected_keys:
        raise ValueError("remaining forest omitted an actual current OPEN root")
    certificate = read(folder / "FORESTS.json")
    if certificate != expected_forests or read(folder / "NEW-KERNELS.json") != kernels:
        raise ValueError("remaining forest global kernel mapping differs from original local certificate ownership")
    print("Checking every new positive full-graph kernel, including unused parent kernels.", flush=True)
    checked = [energy.kernel_gate(row["certificate"]["spec"], row["certificate"]) for row in kernels]
    return {"manifest": manifest, "accepted": accepted, "inventory": inventory,
            "classes": classes, "pending": pending, "domains": v["domains"], "radius": radius, "arcs": v["arcs"],
            "cv": v["cv"], "table": v["table"], "certificate": certificate,
            "kernels": kernels, "checked": checked, "frontier": frontier, "removal": removal,
            "prior_digests": audit["files"], "lineage": {
                "current_source_acceptance_sha256": manifest["source_acceptance_sha256"],
                "older_discovery_acceptance_sha256": old_hash, "registry_acceptance_sha256": registry_hash,
                "exact_current_parent_dictionaries_and_same_full_graph_matrices": True,
                "classification_equality_not_assumed_after_verified_sibling_payments": True,
                "all_older_to_current_OPEN_differences_explained_by_verified_sibling_payments": sibling_lineage}}


def derive(v):
    classes, pending, results, ledgers = hybrid.derive(
        v["classes"], v["pending"], v["domains"], v["certificate"], v["checked"], v["radius"], v["arcs"])
    if any(not row["source_OPEN_box_fully_excluded"] for row in results):
        raise ValueError("all-root closure layer cannot pay an unclosed forest or discard an OPEN half")
    frontier, removals, closed, members = current.transfer(v, classes, pending)
    return classes, pending, results, ledgers, frontier, removals, closed, members


def controls(v, ledgers):
    matrices = {row["group_index"]: row["matrix"] for row in v["domains"]}
    positive = {"two_coordinate_exact_energy_identities": 0, "feasible_radius_one_energy_controls": 0}
    used = set()
    for group in ledgers:
        for leaf in group["leaves"]:
            if leaf["kind"] != "QUADRATIC_ENERGY":
                raise ValueError("this declared all-energy remaining batch has a different leaf kind")
            k = leaf["kernel_index"]
            if k not in used:
                quadratic.identity_control(v["checked"][k])
                positive["two_coordinate_exact_energy_identities"] += 1
                used.add(k)
            ref = leaf["certificate"]["reference_turns"]
            if energy.bound(v["checked"][k], matrices[group["group_index"]], ref, ref,
                            leaf["certificate"], F(1), v["arcs"])["radius_at_most_Rstar_whole_box_excluded"]:
                raise AssertionError("remaining energy falsely excludes feasible radius-one rods")
            positive["feasible_radius_one_energy_controls"] += 1
    negatives = []

    def reject(label, call):
        try:
            call()
        except (ValueError, KeyError, TypeError, IndexError):
            negatives.append(label)
        else:
            raise AssertionError("invalid remaining forest accepted: " + label)

    row = next(row for row in v["certificate"] if len(row["nodes"]) > 1)
    matrix, root = matrices[row["group_index"]], row["source_closed_OPEN_box"]
    bad = deepcopy(row["nodes"])
    split = next(node for node in bad if node["kind"] == "SPLIT")
    split["children"][1] = split["children"][0]
    reject("closed-half-repeated-or-discarded", lambda: forest.independent_leaves(matrix, root, bad))
    reject("hidden-OPEN-node", lambda: forest.independent_leaves(matrix, root, row["nodes"] + [{"kind": "OPEN"}]))
    reject("nonempty-parent-falsely-EMPTY", lambda: forest.replay(
        row["spec"], matrix, root, [{"kind": "EMPTY"}], v["checked"], v["radius"], v["arcs"]))
    leaf = next(x for group in ledgers for x in group["leaves"] if x["kind"] == "QUADRATIC_ENERGY")
    k = leaf["kernel_index"]
    bad_kernel = deepcopy(v["kernels"][k]["certificate"])
    bad_kernel["inverse_numerators"][0][0] = str(int(bad_kernel["inverse_numerators"][0][0]) + 1)
    reject("changed-new-ground-inverse", lambda: energy.kernel_gate(v["checked"][k]["spec"], bad_kernel))
    bad_kernel = deepcopy(v["kernels"][k]["certificate"])
    bad_kernel["weight_numerators"][0] = 0
    reject("nonpositive-new-rod-weight", lambda: energy.kernel_gate(v["checked"][k]["spec"], bad_kernel))
    bad_kernel = deepcopy(v["kernels"][k]["certificate"])
    bad_kernel["weight_numerators"].pop()
    reject("omitted-full-graph-rod", lambda: energy.kernel_gate(v["checked"][k]["spec"], bad_kernel))
    bad_cert = deepcopy(leaf["certificate"])
    bad_cert["difference_dual"]["terms"] = [[0, 1, "-1"]]
    leaf_matrix = next(matrices[g["group_index"]] for g in ledgers if leaf in g["leaves"])
    reject("negative-energy-difference-dual", lambda: energy.bound(
        v["checked"][k], leaf_matrix, leaf["lower"], leaf["upper"], bad_cert, v["radius"], v["arcs"]))
    bad_rows = deepcopy(v["certificate"])
    bad_rows[0]["source_closed_OPEN_box"]["lower"][0] = str(F(bad_rows[0]["source_closed_OPEN_box"]["lower"][0]) + 1)
    reject("changed-current-source-parent", lambda: hybrid.derive(
        v["classes"], v["pending"], v["domains"], bad_rows, v["checked"], v["radius"], v["arcs"]))
    reject("duplicate-current-parent-ownership", lambda: hybrid.derive(
        v["classes"], v["pending"], v["domains"], v["certificate"] * 2, v["checked"], v["radius"], v["arcs"]))
    bad_v = {**v, "certificate": [{**v["certificate"][0], "nodes": [{"kind": "OPEN"}]}]}
    reject("unpaid-root-promoted-to-whole-closure", lambda: derive(bad_v))
    return positive, negatives


def verify(folder, report_path):
    if report_path.exists():
        raise FileExistsError(report_path)
    v = source_gate(folder)
    hashes = {linux(path): sha(path) for path in v["inventory"]}
    if any(hashes.get(text) != digest for text, digest in v["prior_digests"].items()):
        raise ValueError("remaining source current audit bytes changed during reconstruction")
    if hashes[linux(catalog.local_path(v["manifest"]["source_current_audit"]))] != v["manifest"]["source_current_audit_sha256"]:
        raise ValueError("remaining source current audit changed during reconstruction")
    print("Replaying every entire closed energy leaf and independent BFS/DFS partition.", flush=True)
    classes, pending, results, ledgers, frontier, removals, closed, members = derive(v)
    positive, negatives = controls(v, ledgers)
    for name, value in (("SOURCE-LINEAGE.json", v["lineage"]), ("CLASSIFICATION.json", classes),
                        ("PENDING-TYPES.json", pending), ("FOREST-RESULTS.json", results),
                        ("LOWER-LEDGER.json", ledgers), ("RSTAR-COMPETITOR-FRONTIER.json", frontier),
                        ("CONDITIONAL-REMOVAL-LEDGER.json", removals), ("POSITIVE-CONTROLS.json", positive)):
        typed.publish_or_match(folder / name, value)
    manifest, accepted = v["manifest"], v["accepted"]
    report = {
        "schema": "N26-accepted-all-retained-current-OPEN-energy-forest-overlay-v1",
        "verified": True, "radius_scope": typed.SCOPE, "radius_upper": str(v["radius"]),
        "r_strict_interval": accepted["r_strict_interval"],
        "source_acceptance_sha256": manifest["source_acceptance_sha256"],
        "source_current_audit_sha256": manifest["source_current_audit_sha256"],
        "all_previously_selected_force_energy_residual_and_whole_OPEN_layers_semantically_reconstructed": True,
        "all_current_retained_roots_explicitly_accounted_for_and_strictly_closed": len(results),
        "all_new_positive_full_graph_kernels_and_exact_ground_inverses_checked": len(v["checked"]),
        "accepted_closed_forests": results,
        "independent_BFS_DFS_closed_boxes_and_every_strict_leaf_bound_recomputed": True,
        "older_current_parent_lineage_and_verified_sibling_payment_differences_reconstructed": True,
        "new_complete_type_exclusions": closed, "new_current_terminal_paths_removed": members,
        "unresolved_current_competitor_types": sum(not row["radius_at_most_Rstar_type_excluded"] for row in classes),
        "unresolved_current_competitor_closed_boxes": sum(len(row["closed_OPEN_boxes"]) for row in pending),
        "conditional_frontier_pending_subtrees": len(frontier["pending_states"]),
        "conditional_frontier_families": frontier["families"],
        "all_previous_paid_layers_closed_boundaries_and_isomorphic_candidate_paths_retained": True,
        "no_float_symbolic_or_optimization_library_used_by_standalone_checker": True,
        "positive_controls": positive, "negative_controls_rejected": negatives,
        "unrestricted_reduction_final_joint_acceptance": False,
        "full_catalog_complete": False, "global_lower_bound_proved": False,
        "global_optimality_proved": False, "n27_started": False,
        "files": {name: sha(folder / name) for name in [
            "MANIFEST.json", *manifest["copied_files"], "SOURCE-LINEAGE.json", "CLASSIFICATION.json",
            "PENDING-TYPES.json", "FOREST-RESULTS.json", "LOWER-LEDGER.json",
            "RSTAR-COMPETITOR-FRONTIER.json", "CONDITIONAL-REMOVAL-LEDGER.json", "POSITIVE-CONTROLS.json"]},
        "source_files": hashes, "executed_checker_sha256": sha(__file__),
    }
    if report["executed_checker_sha256"] != report["files"]["verify_remaining_energy_forests.py"]:
        raise ValueError("remaining forest executed a different sealed checker")
    for text, digest in hashes.items():
        if sha(catalog.local_path(text)) != digest:
            raise ValueError("remaining forest source bytes changed during replay")
    for name, digest in manifest["copied_files"].items():
        if sha(folder / name) != digest:
            raise ValueError("remaining forest sealed inputs changed during replay")
    report_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k: value for k, value in report.items() if k not in ("files", "source_files", "accepted_closed_forests")},
                     indent=2), flush=True)


def build(args):
    if args.output.exists():
        raise FileExistsError(args.output)
    accepted, _ = typed.bound(args.source)
    index = read(args.index)
    args.output.mkdir(parents=True)
    copies = [(args.source / name, name) for name in accepted["files"] if name.endswith(".py")]
    copies.extend([(args.source / "VERIFIED.json", "SOURCE-ACCEPTANCE.json"),
                   (args.current_audit, "SOURCE-CURRENT-AUDIT.json"), (args.index, "DISCOVERY-INDEX.json"),
                   (Path(__file__), "verify_remaining_energy_forests.py"),
                   (Path(__file__).with_name("n26-remaining-energy-forests-proof.md"), "PROOF.md")])
    root_inputs, certificates, kernels = [], [], []
    for row in index["records"]:
        i, parent = row["group_index"], row["source_OPEN_index"]
        discovery_path, kernels_path = catalog.local_path(row["proposal"]), catalog.local_path(row["kernels"])
        discovery_name, kernels_name = f"DISCOVERY-g{i}-p{parent}.json", f"KERNELS-g{i}-p{parent}.json"
        copies.extend([(discovery_path, discovery_name), (kernels_path, kernels_name)])
        root_inputs.append({"group_index": i, "source_OPEN_index": parent,
                            "discovery": discovery_name, "kernels": kernels_name})
        discovery, new_kernels = read(discovery_path), read(kernels_path)
        certificates.append({key: discovery[key] for key in
                             ("group_index", "spec", "source_OPEN_index", "source_closed_OPEN_box")})
        certificates[-1]["nodes"] = remap_nodes(discovery["nodes"], len(kernels), len(new_kernels))
        kernels.extend(new_kernels)
    for original, name in copies:
        (args.output / name).write_bytes(original.read_bytes())
    for name, data in (("FORESTS.json", certificates), ("NEW-KERNELS.json", kernels)):
        (args.output / name).write_text(json.dumps(data, separators=(",", ":")) + "\n", encoding="utf-8")
    manifest = {
        "schema": "N26-remaining-current-OPEN-energy-forest-bindings-v1",
        "source_overlay": linux(args.source.resolve()), "source_overlay_replay": linux(args.source_replay.resolve()),
        "source_acceptance_sha256": sha(args.source / "VERIFIED.json"),
        "source_current_audit": linux(args.current_audit.resolve()),
        "source_current_audit_sha256": sha(args.current_audit), "root_inputs": root_inputs,
        "copied_files": {name: sha(args.output / name) for _, name in copies},
    }
    manifest["copied_files"].update({name: sha(args.output / name) for name in ("FORESTS.json", "NEW-KERNELS.json")})
    (args.output / "MANIFEST.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    subprocess.run([sys.executable, str(args.output / "verify_remaining_energy_forests.py"),
                    "--input", str(args.output), "--report", str(args.output / "VERIFIED.json")], check=True)


def main():
    parser = argparse.ArgumentParser()
    for key in ("input", "report", "source", "source-replay", "current-audit", "index", "output"):
        parser.add_argument("--" + key, type=Path)
    args = parser.parse_args()
    if args.input and args.report:
        verify(args.input.resolve(), args.report.resolve())
    elif all((args.source, args.source_replay, args.current_audit, args.index, args.output)):
        build(args)
    else:
        parser.error("provide standalone replay or all remaining forest build inputs")


if __name__ == "__main__":
    main()
