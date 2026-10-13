"""Accept new positive kernels and hybrid forests on an explicitly unchanged old OPEN."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path
import subprocess
import sys

from audit_prefix_partition import linux
import n26_correlated_arc_force as correlated
import n26_hybrid_box_forest as hybrid
import n26_quadratic_box_forest as old_forest
import n26_quadratic_energy_minorant as energy
import verify_quadratic_residual_overlay as residual
import verify_quadratic_type_overlay as quadratic
import verify_selected_type_trees as typed
import verify_terminal_catalog as catalog


read, sha = typed.read, catalog.sha


def match(folder, pairs):
    for name, data in pairs:
        if read(folder / name) != data:
            raise ValueError("source semantic reconstruction differs: " + name)


def lineage_gate(discovery, accepted, source_manifest, older_accepted,
                 old_classes, old_pending, current_classes, current_pending, domains):
    if (discovery["schema"] != "N26-unaccepted-hybrid-force-quadratic-residual-forest-v1"
            or discovery["verified"] is not False or discovery["global_optimality_proved"] is not False
            or discovery["radius_scope"] != typed.SCOPE
            or discovery["radius_scope"] != accepted["radius_scope"]
            or discovery["source_acceptance_sha256"] != source_manifest["source_acceptance_sha256"]
            or discovery["source_registry_acceptance_sha256"] != older_accepted["source_acceptance_sha256"]):
        raise ValueError("hybrid discovery has wrong explicit older-source lineage or radius scope")
    index, parent = discovery["group_index"], discovery["source_OPEN_index"]
    if type(index) is not int or type(parent) is not int:
        raise ValueError("hybrid discovery ownership indices must be integers")
    before = next(row for row in old_classes if row["group_index"] == index)
    now = next(row for row in current_classes if row["group_index"] == index)
    older = next(row for row in old_pending if row["group_index"] == index)
    current = next(row for row in current_pending if row["group_index"] == index)
    box = next(row for row in current["closed_OPEN_boxes"] if row["index"] == parent)
    old_box = next(row for row in older["closed_OPEN_boxes"] if row["index"] == parent)
    domain = next(row for row in domains if row["group_index"] == index)
    if (before != now or older != current
            or before["spec"] != discovery["spec"] or current["spec"] != discovery["spec"]
            or old_box != box or box != discovery["source_closed_OPEN_box"]):
        raise ValueError("older-source hybrid OPEN, complete type or exact domain changed in current source")
    return {
        "group_index": index, "source_OPEN_index": parent,
        "discovery_older_source_acceptance_sha256": discovery["source_acceptance_sha256"],
        "full_current_and_older_type_classification_and_pending_identical": True,
        "complete_OPEN_dictionary_identical": True,
        "exact_matrix_from_same_bound_registry": domain["matrix"],
        "current_terminal_member_indices": [row["catalog_member_index"] for row in now["members"]],
    }


def source_gate(folder):
    manifest = read(folder / "MANIFEST.json")
    if manifest["schema"] != "N26-last-hard-hybrid-additive-overlay-bindings-v1":
        raise ValueError("wrong additive hybrid bindings")
    for name, digest in manifest["copied_files"].items():
        if sha(folder / name) != digest:
            raise ValueError("hybrid sealed input changed: " + name)
    source = catalog.local_path(manifest["source_overlay"])
    accepted, inventory = typed.bound(source)
    if (read(catalog.local_path(manifest["source_overlay_replay"])) != accepted
            or sha(source / "VERIFIED.json") != manifest["source_acceptance_sha256"]
            or read(folder / "SOURCE-ACCEPTANCE.json") != accepted):
        raise ValueError("hybrid current source lacks actual matching acceptance and replay")
    for module in (residual, quadratic, old_forest, energy, correlated):
        if sha(module.__file__) != accepted["files"][Path(module.__file__).name]:
            raise ValueError("hybrid executed a different previously sealed gate")
    if sha(hybrid.__file__) != manifest["copied_files"]["n26_hybrid_box_forest.py"]:
        raise ValueError("hybrid executed different additive traversal")
    values = residual.source_gate(source)
    (source_manifest, older_accepted, paths, cv, table, old_classes, old_pending,
     old_ledger, domains, radius, arcs, old_kernels, old_checked, old_certificate,
     old_frontier, old_removal) = values
    inventory.extend(paths)
    inventory.append(catalog.local_path(manifest["source_overlay_replay"]))
    classes, pending, results, ledgers = residual.derive(
        old_classes, old_pending, domains, old_certificate, old_checked, radius, arcs)
    frontier, removal = quadratic.frontier(cv[3], table, classes, pending, cv[5], radius)
    match(source, (("CLASSIFICATION.json", classes), ("PENDING-TYPES.json", pending),
                   ("FOREST-RESULTS.json", results), ("LOWER-LEDGER.json", ledgers),
                   ("RSTAR-COMPETITOR-FRONTIER.json", frontier),
                   ("CONDITIONAL-REMOVAL-LEDGER.json", removal)))
    if results != accepted["selected_residual_forests"] or F(accepted["radius_upper"]) != radius:
        raise ValueError("hybrid current residual acceptance claims do not reconstruct")
    discovery = read(folder / "DISCOVERY.json")
    lineage = lineage_gate(discovery, accepted, source_manifest, older_accepted,
                           old_classes, old_pending, classes, pending, domains)
    lineage["current_source_acceptance_sha256"] = manifest["source_acceptance_sha256"]
    if discovery["kernels_sha256"] != sha(folder / "NEW-KERNELS.json"):
        raise ValueError("hybrid changed its new-kernel discovery bytes")
    certificate = read(folder / "FORESTS.json")
    expected = [{key: discovery[key] for key in
                 ("group_index", "spec", "source_OPEN_index", "source_closed_OPEN_box", "nodes")}]
    if certificate != expected:
        raise ValueError("hybrid forest is not the explicit original discovery")
    by_group = {row["group_index"]: row for row in classes}
    kernels = read(folder / "NEW-KERNELS.json")
    if not isinstance(kernels, list) or not kernels:
        raise ValueError("hybrid has no independently checkable new kernels")
    checked = []
    for row in kernels:
        if (set(row) != {"group_index", "certificate"} or type(row["group_index"]) is not int
                or row["group_index"] != discovery["group_index"]
                or row["certificate"]["spec"] != by_group[row["group_index"]]["spec"]):
            raise ValueError("new hybrid kernel substituted a partial or different graph")
        checked.append(energy.kernel_gate(by_group[row["group_index"]]["spec"], row["certificate"]))
    return {
        "manifest": manifest, "accepted": accepted, "inventory": inventory, "cv": cv,
        "table": table, "classes": classes, "pending": pending, "domains": domains,
        "radius": radius, "arcs": arcs, "certificate": certificate,
        "kernels": kernels, "checked": checked, "frontier": frontier, "removal": removal,
        "lineage": lineage,
        "lineage_inputs": (discovery, accepted, source_manifest, older_accepted,
                           old_classes, old_pending, classes, pending, domains),
    }


def derive(classification, source_pending, domains, certificate, checked, radius, arcs):
    classes = {row["group_index"]: row for row in classification}
    pending = {row["group_index"]: {box["index"]: box for box in row["closed_OPEN_boxes"]}
               for row in source_pending}
    matrices = {row["group_index"]: row["matrix"] for row in domains}
    if (len(classes) != len(classification) or len(pending) != len(source_pending)
            or len(matrices) != len(domains)):
        raise ValueError("hybrid source has duplicate canonical ownership")
    seen, results, ledgers, replacements = set(), [], [], {}
    for row in certificate:
        index, parent = row["group_index"], row["source_OPEN_index"]
        key = index, parent
        if (type(index) is not int or type(parent) is not int or key in seen
                or index not in pending or parent not in pending[index]
                or row["spec"] != classes[index]["spec"]
                or row["source_closed_OPEN_box"] != pending[index][parent]):
            raise ValueError("hybrid forest targets a changed, duplicate or already paid OPEN")
        seen.add(key)
        result, boxes, ledger = hybrid.replay(row["spec"], matrices[index], pending[index][parent],
                                              row["nodes"], checked, radius, arcs)
        results.append({"group_index": index, "source_OPEN_index": parent, **result})
        ledgers.append({"group_index": index, "source_OPEN_index": parent,
                        "spec": row["spec"], "leaves": ledger})
        replacements[key] = (result, [{"index": parent, "kind": "OPEN",
                                      "parent_source_OPEN_index": parent,
                                      "hybrid_forest_node_index": box["index"],
                                      "lower": box["lower"], "upper": box["upper"]} for box in boxes])
    new_classes, new_pending = deepcopy(classification), deepcopy(source_pending)
    if len(new_classes) != len(new_pending):
        raise ValueError("hybrid source class/pending ownership differs")
    for row, unresolved in zip(new_classes, new_pending):
        index = row["group_index"]
        if unresolved["group_index"] != index or unresolved["spec"] != row["spec"]:
            raise ValueError("hybrid source classes and pending rows reordered")
        retained, margins, extra_nodes, changed = [], [], 0, False
        for box in unresolved["closed_OPEN_boxes"]:
            value = replacements.get((index, box["index"]))
            if value is None:
                retained.append(box)
                continue
            result, boxes = value
            changed = True
            retained.extend(boxes)
            row["counts"]["OPEN"] -= 1
            for kind, count in result["counts"].items():
                row["counts"][kind] = row["counts"].get(kind, 0) + count
            extra_nodes += result["nodes"] - 1
            if result["minimum_strict_radius_margin"] is not None:
                margins.append(F(result["minimum_strict_radius_margin"]))
        if changed:
            unresolved["closed_OPEN_boxes"] = retained
            row["nodes"] += extra_nodes
            row["unresolved_closed_boxes"] = len(retained)
            row["radius_at_most_Rstar_type_excluded"] = not retained
            if row["minimum_strict_margin"] is not None:
                margins.append(F(row["minimum_strict_margin"]))
            row["minimum_strict_margin"] = str(min(margins)) if margins else None
            row["proof_source"] = "all-prior-sealed-layers-plus-new-positive-kernel-hybrid-closed-forest"
    return new_classes, new_pending, results, ledgers


def controls(v, ledgers):
    row = v["certificate"][0]
    matrix = next(x["matrix"] for x in v["domains"] if x["group_index"] == row["group_index"])
    root, nodes = row["source_closed_OPEN_box"], row["nodes"]
    checked, radius, arcs = v["checked"], v["radius"], v["arcs"]
    paid = ledgers[0]["leaves"]
    positive = {"exact_two_coordinate_energy_identities": 0, "radius_one_energy_controls": 0,
                "radius_one_correlated_force_controls": 0}
    for k in sorted({leaf["kernel_index"] for leaf in paid if leaf["kind"] == "QUADRATIC_ENERGY"}):
        quadratic.identity_control(checked[k])
        positive["exact_two_coordinate_energy_identities"] += 1
    for leaf in paid:
        if leaf["kind"] == "QUADRATIC_ENERGY":
            ref = leaf["certificate"]["reference_turns"]
            if energy.bound(checked[leaf["kernel_index"]], matrix, ref, ref,
                            leaf["certificate"], F(1), arcs)["radius_at_most_Rstar_whole_box_excluded"]:
                raise AssertionError("hybrid energy falsely excludes feasible radius-one rods")
            positive["radius_one_energy_controls"] += 1
        elif leaf["kind"] == "CORRELATED_FORCE":
            ref = leaf["lower"]
            energy.reference_gate(ref, ref, ref, matrix)
            result = correlated.force_check(row["spec"], ref, ref, matrix, leaf["certificate"], arcs)
            if F(result["required_radius_lower"]) > 1:
                raise AssertionError("hybrid force falsely excludes feasible radius-one rods")
            positive["radius_one_correlated_force_controls"] += 1
    negatives = []

    def reject(label, call):
        try:
            call()
        except (ValueError, KeyError, TypeError, IndexError, StopIteration):
            negatives.append(label)
        else:
            raise AssertionError("invalid hybrid certificate accepted: " + label)

    leaf = next(x for x in paid if x["kind"] == "QUADRATIC_ENERGY")
    k = leaf["kernel_index"]
    bad = deepcopy(v["kernels"][k]["certificate"])
    bad["inverse_numerators"][0][0] = str(int(bad["inverse_numerators"][0][0]) + 1)
    reject("changed-new-ground-inverse", lambda: energy.kernel_gate(row["spec"], bad))
    bad = deepcopy(v["kernels"][k]["certificate"])
    bad["weight_numerators"] = bad["weight_numerators"][:-1]
    reject("omitted-full-graph-rod", lambda: energy.kernel_gate(row["spec"], bad))
    bad = deepcopy(v["kernels"][k]["certificate"])
    bad["weight_numerators"][0] = 0
    reject("nonpositive-new-rod-weight", lambda: energy.kernel_gate(row["spec"], bad))
    bad_spec = deepcopy(row["spec"])
    bad_spec["next"] = 25
    reject("partial-graph-kernel-substitution",
           lambda: energy.kernel_gate(bad_spec, v["kernels"][k]["certificate"]))
    bad_nodes = deepcopy(nodes)
    split = next(x for x in bad_nodes if x["kind"] == "SPLIT")
    split["children"][1] = split["children"][0]
    reject("repeated-or-discarded-closed-half",
           lambda: hybrid.independent_leaves(matrix, root, bad_nodes))
    reject("hidden-OPEN-node",
           lambda: hybrid.independent_leaves(matrix, root, nodes + [{"kind": "OPEN"}]))
    reject("nonempty-root-falsely-EMPTY",
           lambda: hybrid.replay(row["spec"], matrix, root, [{"kind": "EMPTY"}], checked, radius, arcs))
    bad_cert = deepcopy(leaf["certificate"])
    bad_cert["difference_dual"]["terms"] = [[0, 1, "-1"]]
    reject("negative-energy-difference-dual", lambda: energy.bound(
        checked[k], matrix, leaf["lower"], leaf["upper"], bad_cert, radius, arcs))
    force_leaf = next(x for x in paid if x["kind"] == "CORRELATED_FORCE")
    bad_cert = deepcopy(force_leaf["certificate"])
    bad_cert["mu"] = [[0, 1, "-1"]]
    reject("negative-correlated-force-dual", lambda: correlated.force_check(
        row["spec"], force_leaf["lower"], force_leaf["upper"], matrix, bad_cert, arcs))
    bad_cert = deepcopy(force_leaf["certificate"])
    bad_cert["g"] = [0] * len(bad_cert["g"])
    bad_cert["f"] = [0] * len(bad_cert["f"])
    reject("zero-flow-strict-payment", lambda: correlated.force_check(
        row["spec"], force_leaf["lower"], force_leaf["upper"], matrix, bad_cert, arcs))
    reject("duplicate-current-source-OPEN", lambda: derive(
        v["classes"], v["pending"], v["domains"], v["certificate"] * 2, checked, radius, arcs))
    bad_rows = deepcopy(v["certificate"])
    bad_rows[0]["source_OPEN_index"] = -1
    reject("already-paid-or-noncurrent-parent", lambda: derive(
        v["classes"], v["pending"], v["domains"], bad_rows, checked, radius, arcs))
    for label, field, value in (
            ("conditional-proof-promoted-to-U", "radius_scope", "unconditional-original-U"),
            ("older-discovery-source-silently-relabelled", "source_acceptance_sha256", "0" * 64)):
        bad_discovery = deepcopy(v["lineage_inputs"][0])
        bad_discovery[field] = value
        reject(label, lambda: lineage_gate(bad_discovery, *v["lineage_inputs"][1:]))
    bad_discovery = deepcopy(v["lineage_inputs"][0])
    bad_discovery["source_closed_OPEN_box"]["lower"][0] = str(
        F(bad_discovery["source_closed_OPEN_box"]["lower"][0]) + F(1, 10**20))
    reject("changed-entire-source-OPEN-dictionary",
           lambda: lineage_gate(bad_discovery, *v["lineage_inputs"][1:]))
    reject("nonstrict-force-radius-equality", lambda: hybrid.replay(
        row["spec"], matrix, force_leaf,
        [{"kind": "CORRELATED_FORCE", "certificate": force_leaf["certificate"]}],
        checked, F(force_leaf["required_radius_lower"]), arcs))
    return positive, negatives


def verify(folder, report_path):
    if report_path.exists():
        raise FileExistsError(report_path)
    print("Reconstructing the sealed current source and checking every new positive kernel.", flush=True)
    v = source_gate(folder)
    hashes = {linux(path): sha(path) for path in v["inventory"]}
    print("Replaying every hybrid closed leaf and independent BFS/DFS partition.", flush=True)
    classes, pending, results, ledgers = derive(v["classes"], v["pending"], v["domains"],
                                               v["certificate"], v["checked"], v["radius"], v["arcs"])
    current, removals = quadratic.frontier(v["cv"][3], v["table"], classes, pending, v["cv"][5], v["radius"])
    key = lambda row: (row["B"], tuple(row["prefix"]))
    old_states, new_states = {key(x): x for x in v["frontier"]["pending_states"]}, {
        key(x): x for x in current["pending_states"]}
    old_paid, new_paid = {key(x): x for x in v["removal"]}, {key(x): x for x in removals}
    if (not set(new_states) <= set(old_states) or not set(old_paid) <= set(new_paid)
            or set(old_states) - set(new_states) != set(new_paid) - set(old_paid)
            or any(new_states[k] != old_states[k] for k in new_states)
            or any(new_paid[k] != old_paid[k] for k in old_paid)):
        raise ValueError("hybrid terminal transfer lost a previous proof or unaffected state")
    newly_closed = sorted({x["group_index"] for x in classes if x["radius_at_most_Rstar_type_excluded"]}
                          - {x["group_index"] for x in v["classes"] if x["radius_at_most_Rstar_type_excluded"]})
    expected_members = {key(member) for x in v["classes"] if x["group_index"] in newly_closed
                        for member in x["members"]}
    if set(old_states) - set(new_states) != expected_members:
        raise ValueError("hybrid closure did not remove exactly its actual current terminal members")
    for row in v["table"]["rows"]:
        if row["same_canonical_type_as_known_candidate"] and key(row) not in new_states:
            raise ValueError("hybrid transfer lost an isomorphic candidate path")
    print("Checking feasible controls and deliberate invalid-certificate mutations.", flush=True)
    positive, negatives = controls(v, ledgers)
    for name, value in (("SOURCE-LINEAGE.json", v["lineage"]), ("CLASSIFICATION.json", classes),
                        ("PENDING-TYPES.json", pending), ("FOREST-RESULTS.json", results),
                        ("LOWER-LEDGER.json", ledgers), ("RSTAR-COMPETITOR-FRONTIER.json", current),
                        ("CONDITIONAL-REMOVAL-LEDGER.json", removals), ("POSITIVE-CONTROLS.json", positive)):
        typed.publish_or_match(folder / name, value)
    manifest, accepted = v["manifest"], v["accepted"]
    report = {
        "schema": "N26-accepted-last-hard-additive-positive-kernel-hybrid-overlay-v1",
        "verified": True, "radius_scope": typed.SCOPE, "radius_upper": str(v["radius"]),
        "r_strict_interval": accepted["r_strict_interval"],
        "source_acceptance_sha256": manifest["source_acceptance_sha256"],
        "older_discovery_source_explicitly_linked_to_unchanged_current_OPEN": True,
        "source_full_force_and_prior_energy_and_residual_layers_semantically_replayed": True,
        "previous_energy_only_kernel_equality_gate_unchanged": True,
        "all_new_kernel_full_graph_positive_weights_ground_inverses_and_Schur_gates_recomputed": len(v["checked"]),
        "selected_hybrid_forests": results,
        "all_closed_halves_independent_BFS_DFS_boxes_and_strict_leaf_bounds_replayed": True,
        "new_complete_type_exclusions": newly_closed,
        "new_current_terminal_paths_removed": len(new_paid) - len(old_paid),
        "newly_closed_actual_current_member_indices": v["lineage"]["current_terminal_member_indices"],
        "unresolved_current_competitor_types": sum(not x["radius_at_most_Rstar_type_excluded"] for x in classes),
        "unresolved_current_competitor_closed_boxes": sum(len(x["closed_OPEN_boxes"]) for x in pending),
        "conditional_frontier_pending_subtrees": len(current["pending_states"]),
        "conditional_frontier_families": current["families"],
        "all_other_types_boxes_previous_paid_layers_and_candidate_paths_retained": True,
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
    if report["executed_checker_sha256"] != report["files"]["verify_last_hard_hybrid_overlay.py"]:
        raise ValueError("hybrid ran a different sealed checker")
    for text, digest in hashes.items():
        if sha(catalog.local_path(text)) != digest:
            raise ValueError("hybrid source changed during replay")
    for name, digest in manifest["copied_files"].items():
        if sha(folder / name) != digest:
            raise ValueError("hybrid sealed input changed during replay")
    report_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k: x for k, x in report.items() if k not in ("files", "source_files")}, indent=2), flush=True)


def build(args):
    if args.output.exists():
        raise FileExistsError(args.output)
    accepted, _ = typed.bound(args.source)
    discovery = read(args.discovery)
    args.output.mkdir(parents=True)
    copies = [(args.source / name, name) for name in accepted["files"] if name.endswith(".py")]
    copies.extend([(args.source / "VERIFIED.json", "SOURCE-ACCEPTANCE.json"),
                   (args.discovery, "DISCOVERY.json"), (args.kernels, "NEW-KERNELS.json"),
                   (Path(hybrid.__file__), "n26_hybrid_box_forest.py"),
                   (Path(__file__), "verify_last_hard_hybrid_overlay.py"),
                   (Path(__file__).with_name("n26-last-hard-hybrid-proof.md"), "PROOF.md")])
    for original, name in copies:
        (args.output / name).write_bytes(original.read_bytes())
    certificate = [{key: discovery[key] for key in
                    ("group_index", "spec", "source_OPEN_index", "source_closed_OPEN_box", "nodes")}]
    (args.output / "FORESTS.json").write_text(json.dumps(certificate, separators=(",", ":")) + "\n", encoding="utf-8")
    manifest = {
        "schema": "N26-last-hard-hybrid-additive-overlay-bindings-v1",
        "source_overlay": linux(args.source.resolve()),
        "source_overlay_replay": linux(args.source_replay.resolve()),
        "source_acceptance_sha256": sha(args.source / "VERIFIED.json"),
        "copied_files": {name: sha(args.output / name) for _, name in copies},
    }
    manifest["copied_files"]["FORESTS.json"] = sha(args.output / "FORESTS.json")
    (args.output / "MANIFEST.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    subprocess.run([sys.executable, str(args.output / "verify_last_hard_hybrid_overlay.py"),
                    "--input", str(args.output), "--report", str(args.output / "VERIFIED.json")], check=True)


def main():
    parser = argparse.ArgumentParser()
    for key in ("input", "report", "source", "source-replay", "discovery", "kernels", "output"):
        parser.add_argument("--" + key, type=Path)
    args = parser.parse_args()
    if args.input and args.report:
        verify(args.input.resolve(), args.report.resolve())
    elif all((args.source, args.source_replay, args.discovery, args.kernels, args.output)):
        build(args)
    else:
        parser.error("provide standalone replay or all additive-hybrid build inputs")


if __name__ == "__main__":
    main()
