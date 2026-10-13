"""Standalone selected residual energy forests, preserving all previous layers."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path
import subprocess
import sys

from audit_prefix_partition import linux
import n26_quadratic_box_forest as forest
import n26_quadratic_energy_minorant as energy
import verify_quadratic_type_overlay as previous
import verify_selected_type_trees as typed
import verify_terminal_catalog as catalog


read, sha = typed.read, catalog.sha


def source_gate(folder):
    manifest = read(folder / "MANIFEST.json")
    if manifest["schema"] != "N26-quadratic-residual-overlay-bindings-v1":
        raise ValueError("wrong residual overlay bindings")
    for name, digest in manifest["copied_files"].items():
        if sha(folder / name) != digest:
            raise ValueError("residual overlay sealed input changed")
    source = catalog.local_path(manifest["source_overlay"])
    accepted, inventory = typed.bound(source)
    if (read(catalog.local_path(manifest["source_overlay_replay"])) != accepted
            or sha(source / "VERIFIED.json") != manifest["source_acceptance_sha256"]
            or read(folder / "SOURCE-ACCEPTANCE.json") != accepted
            or sha(previous.__file__) != accepted["files"]["verify_quadratic_type_overlay.py"]
            or sha(energy.__file__) != accepted["files"]["n26_quadratic_energy_minorant.py"]):
        raise ValueError("residual source lacks its actual unchanged sealed replay")
    values = previous.source_gate(source)
    old_manifest, base, paths, cv, table, classification, pending, domains, radius, arcs, proposal, kernels, checked, positive, replayed = values
    inventory.extend(paths)
    inventory.append(catalog.local_path(manifest["source_overlay_replay"]))
    a, b, c, d = previous.derive(classification, pending, domains, proposal, kernels, checked, radius, arcs)
    prior_frontier, prior_removal = previous.frontier(cv[3], table, a, b, cv[5], radius)
    for name, data in (("CLASSIFICATION.json", a), ("PENDING-TYPES.json", b), ("LOWER-LEDGER.json", c),
                       ("UNPAID-CHECKS.json", d), ("RSTAR-COMPETITOR-FRONTIER.json", prior_frontier),
                       ("CONDITIONAL-REMOVAL-LEDGER.json", prior_removal)):
        if read(source / name) != data:
            raise ValueError("previous complete quadratic payment layer did not replay")
    if sha(folder / "KERNELS.json") != accepted["files"]["KERNELS.json"]:
        raise ValueError("residual forest changed the accepted positive kernels")
    discovery = read(folder / "DISCOVERY.json")
    if (discovery["schema"] != "N26-unaccepted-current-quadratic-residual-closed-half-forests-v1"
            or discovery["verified"] is not False or discovery["radius_scope"] != accepted["radius_scope"]
            or discovery["source_overlay_acceptance_sha256"] != manifest["source_acceptance_sha256"]
            or discovery["source_kernels_sha256"] != sha(folder / "KERNELS.json")
            or discovery["source_registry_acceptance_sha256"] != accepted["source_acceptance_sha256"]):
        raise ValueError("residual discovery changed its current source or conditional radius")
    selected = manifest["selected_groups"]
    if (not isinstance(selected, list) or not selected or any(type(i) is not int for i in selected)
            or len(set(selected)) != len(selected)):
        raise ValueError("invalid selected residual groups")
    rows = [row for row in discovery["forests"] if row["group_index"] in selected]
    if set(row["group_index"] for row in rows) != set(selected):
        raise ValueError("selected residual group is absent from discovery")
    certificate = read(folder / "FORESTS.json")
    expected = [{"group_index": row["group_index"], "spec": row["spec"],
                 "source_OPEN_index": row["source_OPEN_index"],
                 "source_closed_OPEN_box": row["source_closed_OPEN_box"], "nodes": row["nodes"]} for row in rows]
    if certificate != expected or sha(forest.__file__) != manifest["copied_files"]["n26_quadratic_box_forest.py"]:
        raise ValueError("residual forest source boxes, nodes or executed arithmetic changed")
    return manifest, accepted, inventory, cv, table, a, b, c, domains, radius, arcs, kernels, checked, certificate, prior_frontier, prior_removal


def derive(classification, source_pending, domains, certificate, checked, radius, arcs):
    classes = {row["group_index"]: row for row in classification}
    pending = {row["group_index"]: {box["index"]: box for box in row["closed_OPEN_boxes"]}
               for row in source_pending}
    matrices = {row["group_index"]: row["matrix"] for row in domains}
    seen, results, ledgers, replacements = set(), [], [], {}
    for row in certificate:
        index, parent = row["group_index"], row["source_OPEN_index"]
        key = index, parent
        if (type(index) is not int or type(parent) is not int or key in seen
                or index not in pending or parent not in pending[index]
                or row["spec"] != classes[index]["spec"]
                or row["source_closed_OPEN_box"] != pending[index][parent]):
            raise ValueError("residual forest targets a changed, duplicate or already paid source OPEN")
        seen.add(key)
        result, open_boxes, ledger = forest.replay(row["spec"], matrices[index], pending[index][parent],
                                                  row["nodes"], checked, radius, arcs)
        results.append({"group_index": index, "source_OPEN_index": parent, **result})
        ledgers.append({"group_index": index, "source_OPEN_index": parent,
                        "spec": row["spec"], "leaves": ledger})
        replacements[key] = (result, [{"index": parent, "kind": "OPEN", "parent_source_OPEN_index": parent,
                                      "residual_forest_node_index": box["index"],
                                      "lower": box["lower"], "upper": box["upper"]} for box in open_boxes])
    new_classes, new_pending = deepcopy(classification), deepcopy(source_pending)
    for row, unresolved in zip(new_classes, new_pending):
        index = row["group_index"]
        retained, margins, extra_nodes = [], [], 0
        changed = False
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
            row["proof_source"] = "all-prior-force-and-energy-layers-plus-independent-closed-residual-forests"
    return new_classes, new_pending, results, ledgers


def verify(folder, report_path):
    if report_path.exists():
        raise FileExistsError(report_path)
    values = source_gate(folder)
    manifest, accepted, inventory, cv, table, old_class, old_pending, old_ledger, domains, radius, arcs, kernels, checked, certificate, old_frontier, old_removal = values
    hashes = {linux(path): sha(path) for path in inventory}
    classification, pending, results, ledgers = derive(old_class, old_pending, domains, certificate, checked, radius, arcs)
    current, removals = previous.frontier(cv[3], table, classification, pending, cv[5], radius)
    key = lambda row: (row["B"], tuple(row["prefix"]))
    old_states, new_states = {key(row): row for row in old_frontier["pending_states"]}, {
        key(row): row for row in current["pending_states"]}
    old_paid, new_paid = {key(row): row for row in old_removal}, {key(row): row for row in removals}
    if (not set(new_states) <= set(old_states) or not set(old_paid) <= set(new_paid)
            or set(old_states) - set(new_states) != set(new_paid) - set(old_paid)
            or any(new_states[k] != old_states[k] for k in new_states)
            or any(new_paid[k] != old_paid[k] for k in old_paid)):
        raise ValueError("residual terminal filter lost an old proof or unaffected sibling")
    negatives = []

    def reject(label, call):
        try:
            call()
        except (ValueError, KeyError, TypeError, IndexError):
            negatives.append(label)
        else:
            raise AssertionError("invalid residual forest accepted: " + label)

    example = next(row for row in certificate if any(node["kind"] == "SPLIT" for node in row["nodes"]))
    matrix = next(row["matrix"] for row in domains if row["group_index"] == example["group_index"])
    root = example["source_closed_OPEN_box"]
    bad = deepcopy(example["nodes"])
    split = next(node for node in bad if node["kind"] == "SPLIT")
    split["children"][1] = split["children"][0]
    reject("closed-half-discarded-or-repeated", lambda: forest.replay(
        example["spec"], matrix, root, bad, checked, radius, arcs))
    reject("hidden-OPEN-node", lambda: forest.replay(
        example["spec"], matrix, root, example["nodes"] + [{"kind": "OPEN"}], checked, radius, arcs))
    reject("nonempty-parent-falsely-EMPTY", lambda: forest.replay(
        example["spec"], matrix, root, [{"kind": "EMPTY"}], checked, radius, arcs))
    bad = deepcopy(example["nodes"])
    leaf = next(node for node in bad if node["kind"] == "QUADRATIC_ENERGY")
    leaf["certificate"]["difference_dual"]["terms"] = [[0, 1, "-1"]]
    reject("negative-leaf-difference-dual", lambda: forest.replay(
        example["spec"], matrix, root, bad, checked, radius, arcs))
    reject("duplicate-source-OPEN-forest", lambda: derive(
        old_class, old_pending, domains, certificate + certificate[:1], checked, radius, arcs))
    bad_rows = deepcopy(certificate)
    bad_rows[0]["source_OPEN_index"] = -1
    reject("noncurrent-or-already-paid-parent", lambda: derive(
        old_class, old_pending, domains, bad_rows, checked, radius, arcs))
    positive_controls = 0
    for row in certificate:
        matrix = next(item["matrix"] for item in domains if item["group_index"] == row["group_index"])
        _, _, ledger = forest.replay(row["spec"], matrix, row["source_closed_OPEN_box"],
                                     row["nodes"], checked, radius, arcs)
        for leaf in ledger:
            if leaf["kind"] != "QUADRATIC_ENERGY":
                continue
            reference = leaf["certificate"]["reference_turns"]
            check = energy.bound(checked[leaf["kernel_index"]], matrix, reference, reference,
                                 leaf["certificate"], F(1), arcs)
            if check["radius_at_most_Rstar_whole_box_excluded"]:
                raise AssertionError("residual leaf falsely excluded feasible radius-one rods")
            positive_controls += 1
    for name, data in (("CLASSIFICATION.json", classification), ("PENDING-TYPES.json", pending),
                       ("FOREST-RESULTS.json", results), ("LOWER-LEDGER.json", ledgers),
                       ("RSTAR-COMPETITOR-FRONTIER.json", current),
                       ("CONDITIONAL-REMOVAL-LEDGER.json", removals)):
        typed.publish_or_match(folder / name, data)
    newly_closed = sorted(set(row["group_index"] for row in classification if row["radius_at_most_Rstar_type_excluded"])
                          - set(row["group_index"] for row in old_class if row["radius_at_most_Rstar_type_excluded"]))
    report = {
        "schema": "N26-accepted-current-quadratic-residual-closed-forest-overlay-v1",
        "verified": True, "radius_scope": accepted["radius_scope"], "radius_upper": str(radius),
        "r_strict_interval": accepted["r_strict_interval"],
        "source_acceptance_sha256": manifest["source_acceptance_sha256"],
        "source_overlay_full_force_and_prior_energy_layers_semantically_replayed": True,
        "source_full_type_trees_and_all_previous_paid_boxes_unchanged": True,
        "selected_residual_forests": results,
        "all_closed_halves_independent_BFS_DFS_boxes_and_strict_leaf_bounds_replayed": True,
        "new_complete_type_exclusions": newly_closed,
        "new_current_terminal_paths_removed": len(new_paid) - len(old_paid),
        "unresolved_current_competitor_types": sum(not row["radius_at_most_Rstar_type_excluded"] for row in classification),
        "unresolved_current_competitor_closed_boxes": sum(len(row["closed_OPEN_boxes"]) for row in pending),
        "conditional_frontier_pending_subtrees": len(current["pending_states"]),
        "conditional_frontier_families": current["families"],
        "all_unselected_types_boxes_siblings_and_isomorphic_candidate_paths_retained": True,
        "radius_one_rod_positive_controls": positive_controls, "negative_controls_rejected": negatives,
        "unrestricted_reduction_final_joint_acceptance": False,
        "full_catalog_complete": False, "global_lower_bound_proved": False,
        "global_optimality_proved": False, "n27_started": False,
        "files": {name: sha(folder / name) for name in [
            "MANIFEST.json", *manifest["copied_files"], "CLASSIFICATION.json", "PENDING-TYPES.json",
            "FOREST-RESULTS.json", "LOWER-LEDGER.json", "RSTAR-COMPETITOR-FRONTIER.json",
            "CONDITIONAL-REMOVAL-LEDGER.json"]},
        "source_files": hashes, "executed_checker_sha256": sha(__file__)}
    if report["executed_checker_sha256"] != report["files"]["verify_quadratic_residual_overlay.py"]:
        raise ValueError("residual overlay executed different arithmetic")
    for text, digest in hashes.items():
        if sha(catalog.local_path(text)) != digest:
            raise ValueError("residual source bytes changed during replay")
    for name, digest in manifest["copied_files"].items():
        if sha(folder / name) != digest:
            raise ValueError("residual sealed input changed during replay")
    report_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in report.items() if key not in ("files", "source_files")}, indent=2),
          flush=True)


def build(args):
    if args.output.exists():
        raise FileExistsError(args.output)
    accepted, _ = typed.bound(args.source)
    discovery = read(args.discovery)
    certificate = [{key: row[key] for key in
                    ("group_index", "spec", "source_OPEN_index", "source_closed_OPEN_box", "nodes")}
                   for row in discovery["forests"] if row["group_index"] in args.groups]
    args.output.mkdir(parents=True)
    copies = [(args.source / name, name) for name in accepted["files"] if name.endswith(".py")]
    copies.extend([(args.source / "VERIFIED.json", "SOURCE-ACCEPTANCE.json"),
                   (args.source / "KERNELS.json", "KERNELS.json"), (args.discovery, "DISCOVERY.json"),
                   (Path(forest.__file__), "n26_quadratic_box_forest.py"),
                   (Path(__file__), "verify_quadratic_residual_overlay.py"),
                   (Path(__file__).with_name("n26-quadratic-residual-forest-proof.md"), "PROOF.md")])
    for original, name in copies:
        (args.output / name).write_bytes(original.read_bytes())
    (args.output / "FORESTS.json").write_text(json.dumps(certificate, separators=(",", ":")) + "\n", encoding="utf-8")
    manifest = {
        "schema": "N26-quadratic-residual-overlay-bindings-v1",
        "source_overlay": linux(args.source.resolve()), "source_overlay_replay": linux(args.source_replay.resolve()),
        "source_acceptance_sha256": sha(args.source / "VERIFIED.json"), "selected_groups": args.groups,
        "copied_files": {name: sha(args.output / name) for _, name in copies}}
    manifest["copied_files"]["FORESTS.json"] = sha(args.output / "FORESTS.json")
    (args.output / "MANIFEST.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    subprocess.run([sys.executable, str(args.output / "verify_quadratic_residual_overlay.py"),
                    "--input", str(args.output), "--report", str(args.output / "VERIFIED.json")], check=True)


def main():
    parser = argparse.ArgumentParser()
    for key in ("input", "report", "source", "source-replay", "discovery", "output"):
        parser.add_argument("--" + key, type=Path)
    parser.add_argument("--groups", nargs="+", type=int)
    args = parser.parse_args()
    if args.input and args.report:
        verify(args.input.resolve(), args.report.resolve())
    elif all((args.source, args.source_replay, args.discovery, args.output, args.groups)):
        build(args)
    else:
        parser.error("provide replay or all selected forest build inputs")


if __name__ == "__main__":
    main()
