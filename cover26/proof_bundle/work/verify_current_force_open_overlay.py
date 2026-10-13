"""Exact additive whole-OPEN force payments, preserving all sealed current layers."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path
import subprocess
import sys

from audit_prefix_partition import linux
import expanded_type_registry as registry
import n26_correlated_arc_force as force
import verify_last_hard_hybrid_overlay as previous
import verify_quadratic_type_overlay as quadratic
import verify_selected_type_trees as typed
import verify_terminal_catalog as catalog


read, sha = typed.read, catalog.sha


def proposal_gate(discovery, old_hash, registry_hash, radius, classes, pending, old_classes, old_pending):
    if (discovery["schema"] != "N26-unaccepted-whole-current-OPEN-correlated-force-payments-v1"
            or discovery["verified"] is not False or discovery["global_optimality_proved"] is not False
            or discovery["radius_scope"] != typed.SCOPE or F(discovery["radius_upper"]) != radius
            or discovery["source_acceptance_sha256"] != old_hash
            or discovery["source_registry_acceptance_sha256"] != registry_hash):
        raise ValueError("whole-OPEN discovery changed explicit older source, root or conditional scope")
    groups = discovery["groups"]
    if (not isinstance(groups, list) or not groups or any(type(i) is not int for i in groups)
            or len(set(groups)) != len(groups)):
        raise ValueError("whole-OPEN discovery has invalid selected group ownership")
    current = {row["group_index"]: row for row in classes}
    old = {row["group_index"]: row for row in old_classes}
    boxes = {row["group_index"]: row for row in pending}
    old_boxes = {row["group_index"]: row for row in old_pending}
    for i in groups:
        if (i not in current or i not in old or current[i] != old[i] or boxes[i] != old_boxes[i]
                or not boxes[i]["closed_OPEN_boxes"]):
            raise ValueError("discovery full type or complete OPEN record changed along current source lineage")
    expected = {(i, row["index"]) for i in groups for row in boxes[i]["closed_OPEN_boxes"]}
    seen = set()
    for row in discovery["proposals"]:
        i, parent = row["group_index"], row["source_OPEN_index"]
        key = i, parent
        if type(i) is not int or type(parent) is not int or key not in expected or key in seen:
            raise ValueError("discovery contains duplicate, missing or noncurrent whole-OPEN ownership")
        box = next(item for item in boxes[i]["closed_OPEN_boxes"] if item["index"] == parent)
        if row["spec"] != current[i]["spec"] or row["source_closed_OPEN_box"] != box:
            raise ValueError("discovery substituted its full graph or entire closed parent")
        seen.add(key)
    if seen != expected:
        raise ValueError("discovery omitted an unpaid or unvisited current source OPEN")
    return groups


def source_gate(folder):
    manifest = read(folder / "MANIFEST.json")
    if manifest["schema"] != "N26-current-whole-OPEN-force-overlay-bindings-v1":
        raise ValueError("wrong whole-OPEN force bindings")
    for name, digest in manifest["copied_files"].items():
        if sha(folder / name) != digest:
            raise ValueError("whole-OPEN sealed input changed: " + name)
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
            or not audit["actual_current_hybrid_standalone_replay_matched_and_bound"]
            or audit["global_optimality_proved"] is not False
            or audit["radius_scope"] != accepted["radius_scope"]
            or audit["r_strict_interval"] != accepted["r_strict_interval"]
            or audit["files"].get(linux(source / "VERIFIED.json")) != sha(source / "VERIFIED.json")
            or audit["unresolved_current_competitor_closed_boxes"]
            != accepted["unresolved_current_competitor_closed_boxes"]):
        raise ValueError("whole-OPEN source lacks actual matching current acceptance, replay or audit")
    for text, digest in audit["files"].items():
        path = catalog.local_path(text)
        if sha(path) != digest:
            raise ValueError("whole-OPEN prior complete current inventory changed")
        inventory.append(path)
    inventory.extend([replay, audit_path])
    for module in (previous, quadratic, registry, typed, force):
        if sha(module.__file__) != accepted["files"][Path(module.__file__).name]:
            raise ValueError("whole-OPEN executed different previously sealed arithmetic")
    print("Reconstructing all previously selected current force, energy and residual layers.", flush=True)
    v = previous.source_gate(source)
    inventory.extend(v["inventory"])
    classes, pending, results, ledgers = previous.derive(
        v["classes"], v["pending"], v["domains"], v["certificate"], v["checked"], v["radius"], v["arcs"])
    frontier, removal = quadratic.frontier(v["cv"][3], v["table"], classes, pending, v["cv"][5], v["radius"])
    previous.match(source, (("CLASSIFICATION.json", classes), ("PENDING-TYPES.json", pending),
                           ("FOREST-RESULTS.json", results), ("LOWER-LEDGER.json", ledgers),
                           ("RSTAR-COMPETITOR-FRONTIER.json", frontier),
                           ("CONDITIONAL-REMOVAL-LEDGER.json", removal)))
    if results != accepted["selected_hybrid_forests"]:
        raise ValueError("whole-OPEN current hybrid acceptance did not reconstruct")
    source_manifest = read(source / "MANIFEST.json")
    residual_source = catalog.local_path(source_manifest["source_overlay"])
    residual_manifest = read(residual_source / "MANIFEST.json")
    older = catalog.local_path(residual_manifest["source_overlay"])
    older_accepted, paths = typed.bound(older)
    inventory.extend(paths)
    old_hash = sha(older / "VERIFIED.json")
    if (old_hash != residual_manifest["source_acceptance_sha256"]
            or read(catalog.local_path(residual_manifest["source_overlay_replay"])) != older_accepted):
        raise ValueError("whole-OPEN older discovery source is not the actual bound current ancestor")
    older_manifest = read(older / "MANIFEST.json")
    base = catalog.local_path(older_manifest["source_registry"])
    base_accepted, paths = typed.bound(base)
    inventory.extend(paths)
    registry_hash = sha(base / "VERIFIED.json")
    if (registry_hash != older_accepted["source_acceptance_sha256"]
            or read(catalog.local_path(older_manifest["source_registry_replay"])) != base_accepted):
        raise ValueError("whole-OPEN registry is not the exact older-source base")
    discovery = read(folder / "DISCOVERY.json")
    old_classes, old_pending = read(older / "CLASSIFICATION.json"), read(older / "PENDING-TYPES.json")
    groups = proposal_gate(discovery, old_hash, registry_hash, v["radius"],
                           classes, pending, old_classes, old_pending)
    certificate = read(folder / "CERTIFICATE.json")
    expected = {"schema": "N26-current-whole-OPEN-correlated-force-certificates-v1",
                "radius_scope": typed.SCOPE, "radius_upper": str(v["radius"]),
                "source_acceptance_sha256": manifest["source_acceptance_sha256"],
                "discovery_older_acceptance_sha256": old_hash,
                "rows": [{key: row[key] for key in
                          ("group_index", "spec", "source_OPEN_index", "source_closed_OPEN_box", "certificate")}
                         for row in discovery["proposals"]]}
    if certificate != expected:
        raise ValueError("whole-OPEN certificate changed or promoted a discovery diagnostic")
    print("Freshly replaying the twelve newly selected complete source force trees.", flush=True)
    base_values = registry.input_gate(base)
    (base_manifest, pool_report, paths, cv, table, pool_rows, pool_pending, pool_domains,
     pool_certificate, radius, caps, arcs, base_certificate, positive) = base_values
    inventory.extend(paths)
    if radius != v["radius"] or table != v["table"] or cv[3] != v["cv"][3]:
        raise ValueError("whole-OPEN newly selected trees changed radius, catalogue or original frontier")
    base_classes = {row["group_index"]: row for row in read(base / "CLASSIFICATION.json")}
    base_pending = {row["group_index"]: row for row in read(base / "PENDING-TYPES.json")}
    base_domains = {row["group_index"]: row for row in read(base / "DOMAINS.json")}
    base_ledgers = {row["group_index"]: row for row in read(base / "LOWER-LEDGER.json")}
    current = {row["group_index"]: row for row in classes}
    current_pending = {row["group_index"]: row for row in pending}
    current_domains = {row["group_index"]: row for row in v["domains"]}
    source_types = {row["group_index"]: row for row in base_certificate["types"]}
    pool_types = {row["group_index"]: row for row in pool_certificate["types"]}
    pool_folder = catalog.local_path(base_manifest["source_pool"])
    pool_ledgers = {row["group_index"]: row for row in read(pool_folder / "LOWER-LEDGER.json")}
    replayed = []
    for i in groups:
        source_row = source_types[i]
        if source_row["kind"] == "REUSE":
            original = pool_types[source_row["pool_type_index"]]
        elif source_row["kind"] == "TREE":
            original = source_row
        else:
            raise ValueError("unknown newly selected complete proof-tree source")
        if original["spec"] != current[i]["spec"] or base_classes[i] != current[i]:
            raise ValueError("newly selected type is not the identical unmodified base type")
        bare = {"group_index": i, "spec": original["spec"], "nodes": original["nodes"]}
        a, b, c, d = typed.derive(table, {"types": [bare]}, radius, caps, arcs)
        if (any(current[i][key] != value for key, value in a[0].items())
                or b[0] != current_pending[i] or b[0] != base_pending[i]
                or d[0]["matrix"] != current_domains[i]["matrix"]
                or d[0]["matrix"] != base_domains[i]["matrix"]):
            raise ValueError("complete chosen source tree, closed OPEN or exact matrix did not reconstruct")
        if source_row["kind"] == "TREE":
            if c[0] != base_ledgers[i] or d[0] != base_domains[i]:
                raise ValueError("newly chosen complete original paid force ledger changed")
        elif c[0]["strict_radius_conditional_leaves"] != pool_ledgers[
                source_row["pool_type_index"]]["strict_radius_conditional_leaves"]:
            raise ValueError("reused original full paid force ledger changed")
        replayed.append({"group_index": i, "nodes": a[0]["nodes"], "OPEN": len(b[0]["closed_OPEN_boxes"]),
                         "every_original_paid_leaf_and_independent_BFS_DFS_partition_replayed": True})
    lineage = {"older_discovery_acceptance_sha256": old_hash,
               "current_source_acceptance_sha256": manifest["source_acceptance_sha256"],
               "same_registry_acceptance_sha256": registry_hash, "groups": groups,
               "all_selected_full_classifications_pending_records_and_OPEN_dictionaries_identical": True,
               "all_selected_exact_matrices_recomputed_from_same_bound_registry": True,
               "older_source_not_silently_relabelled": True}
    return {"manifest": manifest, "accepted": accepted, "inventory": inventory,
            "classes": classes, "pending": pending, "domains": v["domains"], "radius": radius,
            "arcs": arcs, "cv": cv, "table": table, "certificate": certificate,
            "frontier": frontier, "removal": removal, "replayed": replayed, "lineage": lineage,
            "discovery": discovery, "prior_digests": audit["files"],
            "proposal_gate_inputs": (old_hash, registry_hash, radius, classes, pending, old_classes, old_pending)}


def derive(classes, source_pending, domains, certificate, radius, arcs):
    by_group = {row["group_index"]: row for row in classes}
    boxes = {row["group_index"]: {box["index"]: box for box in row["closed_OPEN_boxes"]}
             for row in source_pending}
    matrices = {row["group_index"]: row["matrix"] for row in domains}
    if (len(by_group) != len(classes) or len(boxes) != len(source_pending)
            or len(matrices) != len(domains) or len(classes) != len(source_pending)):
        raise ValueError("whole-OPEN source has duplicate or mismatched type ownership")
    seen, payments, unpaid = set(), [], []
    for row in certificate["rows"]:
        i, parent = row["group_index"], row["source_OPEN_index"]
        key = i, parent
        if (set(row) != {"group_index", "spec", "source_OPEN_index", "source_closed_OPEN_box", "certificate"}
                or type(i) is not int or type(parent) is not int or key in seen
                or i not in boxes or parent not in boxes[i]
                or row["spec"] != by_group[i]["spec"]
                or row["spec"]["N"] != 26 or row["spec"]["next"] != 26
                or row["source_closed_OPEN_box"] != boxes[i][parent]):
            raise ValueError("duplicate, changed, partial or already paid whole-OPEN source")
        seen.add(key)
    for row in certificate["rows"]:
        i, parent = row["group_index"], row["source_OPEN_index"]
        if row["certificate"] is None:
            unpaid.append({"group_index": i, "source_OPEN_index": parent, "no_certificate": True})
            continue
        box = boxes[i][parent]
        result = force.force_check(row["spec"], box["lower"], box["upper"], matrices[i], row["certificate"], arcs)
        margin = F(result["required_radius_lower"]) - radius
        if margin > 0:
            payments.append({**row, **result, "minimum_strict_radius_margin": str(margin)})
        else:
            unpaid.append({"group_index": i, "source_OPEN_index": parent,
                           "required_radius_lower": result["required_radius_lower"],
                           "nonstrict_radius_margin": str(margin)})
    paid_by_group = {}
    for row in payments:
        paid_by_group.setdefault(row["group_index"], {})[row["source_OPEN_index"]] = row
    new_classes, pending = deepcopy(classes), deepcopy(source_pending)
    for row, unresolved in zip(new_classes, pending):
        i = row["group_index"]
        if unresolved["group_index"] != i or unresolved["spec"] != row["spec"]:
            raise ValueError("whole-OPEN source type and pending order differs")
        paid = paid_by_group.get(i, {})
        original_count = len(unresolved["closed_OPEN_boxes"])
        unresolved["closed_OPEN_boxes"] = [box for box in unresolved["closed_OPEN_boxes"] if box["index"] not in paid]
        if original_count != len(unresolved["closed_OPEN_boxes"]) + len(paid):
            raise ValueError("whole-OPEN layer lost an unpaid or unvisited source domain")
        if paid:
            row["counts"]["OPEN"] -= len(paid)
            row["counts"]["CORRELATED_FORCE"] = row["counts"].get("CORRELATED_FORCE", 0) + len(paid)
            row["unresolved_closed_boxes"] = len(unresolved["closed_OPEN_boxes"])
            row["radius_at_most_Rstar_type_excluded"] = not unresolved["closed_OPEN_boxes"]
            margins = [F(item["minimum_strict_radius_margin"]) for item in paid.values()]
            if row["minimum_strict_margin"] is not None:
                margins.append(F(row["minimum_strict_margin"]))
            row["minimum_strict_margin"] = str(min(margins))
            row["proof_source"] = "all-prior-sealed-layers-plus-exact-whole-current-OPEN-force-payments"
    return new_classes, pending, payments, unpaid


def transfer(v, classes, pending):
    frontier, removals = quadratic.frontier(v["cv"][3], v["table"], classes, pending, v["cv"][5], v["radius"])
    key = lambda row: (row["B"], tuple(row["prefix"]))
    old_states, new_states = {key(x): x for x in v["frontier"]["pending_states"]}, {
        key(x): x for x in frontier["pending_states"]}
    old_paid, new_paid = {key(x): x for x in v["removal"]}, {key(x): x for x in removals}
    closed = sorted({x["group_index"] for x in classes if x["radius_at_most_Rstar_type_excluded"]}
                    - {x["group_index"] for x in v["classes"] if x["radius_at_most_Rstar_type_excluded"]})
    members = {key(member) for x in v["classes"] if x["group_index"] in closed for member in x["members"]}
    if (not set(new_states) <= set(old_states) or not set(old_paid) <= set(new_paid)
            or set(old_states) - set(new_states) != set(new_paid) - set(old_paid)
            or set(old_states) - set(new_states) != members
            or any(new_states[k] != old_states[k] for k in new_states)
            or any(new_paid[k] != old_paid[k] for k in old_paid)):
        raise ValueError("whole-OPEN terminal filter lost prior proofs, siblings or actual member ownership")
    for row in v["table"]["rows"]:
        if row["same_canonical_type_as_known_candidate"] and key(row) not in new_states:
            raise ValueError("whole-OPEN terminal filter lost an isomorphic candidate path")
    return frontier, removals, closed, len(members)


def controls(v, payments):
    negative, positive = [], {"feasible_radius_one_force_controls": 0, "equality_retained_as_OPEN": 0}
    matrices = {row["group_index"]: row["matrix"] for row in v["domains"]}
    for row in payments:
        box, matrix = row["source_closed_OPEN_box"], matrices[row["group_index"]]
        reference = [F(0), *map(F, box["lower"])]
        if any(reference[j] - reference[i] > F(matrix[i][j], typed.constraints.SCALE)
               for i in range(len(reference)) for j in range(len(reference))):
            raise AssertionError("positive force control reference is outside necessary closed domain")
        result = force.force_check(row["spec"], box["lower"], box["lower"], matrix, row["certificate"], v["arcs"])
        if F(result["required_radius_lower"]) > 1:
            raise AssertionError("whole-OPEN force falsely excludes feasible radius-one rods")
        positive["feasible_radius_one_force_controls"] += 1
    example = payments[0]
    one = {**v["certificate"], "rows": [{key: example[key] for key in
           ("group_index", "spec", "source_OPEN_index", "source_closed_OPEN_box", "certificate")}]}
    _, retained, paid, unpaid = derive(v["classes"], v["pending"], v["domains"], one,
                                       F(example["required_radius_lower"]), v["arcs"])
    if paid or len(unpaid) != 1 or retained != v["pending"]:
        raise AssertionError("nonstrict whole-OPEN radius equality was paid")
    positive["equality_retained_as_OPEN"] = 1

    def reject(label, call):
        try:
            call()
        except (ValueError, KeyError, TypeError, IndexError, StopIteration):
            negative.append(label)
        else:
            raise AssertionError("invalid whole-OPEN force accepted: " + label)

    matrix, box = matrices[example["group_index"]], example["source_closed_OPEN_box"]
    bad = deepcopy(example["certificate"])
    bad["mu"] = [[0, 1, "-1"]]
    reject("negative-difference-dual", lambda: force.force_check(
        example["spec"], box["lower"], box["upper"], matrix, bad, v["arcs"]))
    bad = deepcopy(example["certificate"])
    bad["g"], bad["f"] = [0] * len(bad["g"]), [0] * len(bad["f"])
    reject("zero-flow-as-strict-force", lambda: force.force_check(
        example["spec"], box["lower"], box["upper"], matrix, bad, v["arcs"]))
    bad = deepcopy(example["certificate"])
    bad["f"].pop()
    reject("incomplete-full-graph-cycle-flow", lambda: force.force_check(
        example["spec"], box["lower"], box["upper"], matrix, bad, v["arcs"]))
    bad_rows = deepcopy(one)
    bad_rows["rows"] *= 2
    reject("duplicate-current-OPEN-ownership", lambda: derive(
        v["classes"], v["pending"], v["domains"], bad_rows, v["radius"], v["arcs"]))
    bad_rows = deepcopy(one)
    bad_rows["rows"][0]["source_OPEN_index"] = -1
    reject("noncurrent-or-already-paid-parent", lambda: derive(
        v["classes"], v["pending"], v["domains"], bad_rows, v["radius"], v["arcs"]))
    bad_rows = deepcopy(one)
    bad_rows["rows"][0]["source_closed_OPEN_box"]["lower"][0] = str(F(box["lower"][0]) + F(1, 10**20))
    reject("changed-closed-parent-box", lambda: derive(
        v["classes"], v["pending"], v["domains"], bad_rows, v["radius"], v["arcs"]))
    bad_rows = deepcopy(one)
    bad_rows["rows"][0]["spec"]["next"] = 25
    reject("partial-graph-substituted-for-full-type", lambda: derive(
        v["classes"], v["pending"], v["domains"], bad_rows, v["radius"], v["arcs"]))
    discovery = v["discovery"]
    for label, key, value in (("conditional-proof-promoted-to-U", "radius_scope", "unconditional-U"),
                              ("older-source-silently-relabelled", "source_acceptance_sha256", "0" * 64)):
        bad_discovery = deepcopy(discovery)
        bad_discovery[key] = value
        reject(label, lambda: proposal_gate(bad_discovery, *v["proposal_gate_inputs"]))
    bad_discovery = deepcopy(discovery)
    bad_discovery["proposals"].pop()
    reject("unpaid-or-unvisited-source-OPEN-omitted",
           lambda: proposal_gate(bad_discovery, *v["proposal_gate_inputs"]))
    return positive, negative


def verify(folder, report_path):
    if report_path.exists():
        raise FileExistsError(report_path)
    v = source_gate(folder)
    hashes = {linux(path): sha(path) for path in v["inventory"]}
    for text, digest in v["prior_digests"].items():
        if hashes.get(text) != digest:
            raise ValueError("whole-OPEN current audit bytes changed during source reconstruction")
    if hashes[linux(catalog.local_path(v["manifest"]["source_current_audit"]))] != v["manifest"]["source_current_audit_sha256"]:
        raise ValueError("whole-OPEN current audit changed during source reconstruction")
    print("Recomputing all whole-current-OPEN force payments; numerical claims ignored.", flush=True)
    classes, pending, payments, unpaid = derive(
        v["classes"], v["pending"], v["domains"], v["certificate"], v["radius"], v["arcs"])
    if not payments:
        raise ValueError("whole-OPEN overlay has no strict new payment")
    frontier, removals, newly_closed, members = transfer(v, classes, pending)
    positive, negatives = controls(v, payments)
    for name, value in (("SOURCE-LINEAGE.json", v["lineage"]), ("SOURCE-TREE-REPLAYS.json", v["replayed"]),
                        ("CLASSIFICATION.json", classes), ("PENDING-TYPES.json", pending),
                        ("LOWER-LEDGER.json", payments), ("UNPAID-CHECKS.json", unpaid),
                        ("RSTAR-COMPETITOR-FRONTIER.json", frontier),
                        ("CONDITIONAL-REMOVAL-LEDGER.json", removals), ("POSITIVE-CONTROLS.json", positive)):
        typed.publish_or_match(folder / name, value)
    manifest, accepted = v["manifest"], v["accepted"]
    report = {
        "schema": "N26-accepted-current-whole-OPEN-correlated-force-overlay-v1",
        "verified": True, "radius_scope": typed.SCOPE, "radius_upper": str(v["radius"]),
        "r_strict_interval": accepted["r_strict_interval"],
        "source_acceptance_sha256": manifest["source_acceptance_sha256"],
        "source_current_audit_sha256": manifest["source_current_audit_sha256"],
        "all_previously_selected_force_energy_and_residual_layers_semantically_reconstructed": True,
        "newly_selected_complete_force_source_trees_and_every_old_paid_leaf_replayed": v["replayed"],
        "explicit_older_discovery_current_full_type_OPEN_and_matrix_lineage_checked": True,
        "new_strict_whole_current_OPEN_force_payments": len(payments),
        "unpaid_whole_source_OPEN_checks_retained": len(unpaid),
        "minimum_strict_radius_margin": str(min(F(x["minimum_strict_radius_margin"]) for x in payments)),
        "new_complete_type_exclusions": newly_closed,
        "new_current_terminal_paths_removed": members,
        "unresolved_current_competitor_types": sum(not x["radius_at_most_Rstar_type_excluded"] for x in classes),
        "unresolved_current_competitor_closed_boxes": sum(len(x["closed_OPEN_boxes"]) for x in pending),
        "conditional_frontier_pending_subtrees": len(frontier["pending_states"]),
        "conditional_frontier_families": frontier["families"],
        "all_prior_paid_layers_unvisited_unpaid_boxes_closed_boundaries_and_candidate_paths_preserved": True,
        "no_float_symbolic_or_optimization_library_used_by_standalone_checker": True,
        "positive_controls": positive, "negative_controls_rejected": negatives,
        "unrestricted_reduction_final_joint_acceptance": False,
        "full_catalog_complete": False, "global_lower_bound_proved": False,
        "global_optimality_proved": False, "n27_started": False,
        "files": {name: sha(folder / name) for name in [
            "MANIFEST.json", *manifest["copied_files"], "SOURCE-LINEAGE.json", "SOURCE-TREE-REPLAYS.json",
            "CLASSIFICATION.json", "PENDING-TYPES.json", "LOWER-LEDGER.json", "UNPAID-CHECKS.json",
            "RSTAR-COMPETITOR-FRONTIER.json", "CONDITIONAL-REMOVAL-LEDGER.json", "POSITIVE-CONTROLS.json"]},
        "source_files": hashes, "executed_checker_sha256": sha(__file__),
    }
    if report["executed_checker_sha256"] != report["files"]["verify_current_force_open_overlay.py"]:
        raise ValueError("whole-OPEN executed a different sealed checker")
    for text, digest in hashes.items():
        if sha(catalog.local_path(text)) != digest:
            raise ValueError("whole-OPEN source bytes changed during verification")
    for name, digest in manifest["copied_files"].items():
        if sha(folder / name) != digest:
            raise ValueError("whole-OPEN sealed input changed during verification")
    report_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k: value for k, value in report.items() if k not in ("files", "source_files")}, indent=2),
          flush=True)


def build(args):
    if args.output.exists():
        raise FileExistsError(args.output)
    accepted, _ = typed.bound(args.source)
    discovery = read(args.discovery)
    args.output.mkdir(parents=True)
    copies = [(args.source / name, name) for name in accepted["files"] if name.endswith(".py")]
    copies.extend([(args.source / "VERIFIED.json", "SOURCE-ACCEPTANCE.json"),
                   (args.current_audit, "SOURCE-CURRENT-AUDIT.json"), (args.discovery, "DISCOVERY.json"),
                   (Path(__file__), "verify_current_force_open_overlay.py"),
                   (Path(__file__).with_name("n26-current-whole-OPEN-force-proof.md"), "PROOF.md")])
    for original, name in copies:
        (args.output / name).write_bytes(original.read_bytes())
    certificate = {
        "schema": "N26-current-whole-OPEN-correlated-force-certificates-v1",
        "radius_scope": typed.SCOPE, "radius_upper": accepted["radius_upper"],
        "source_acceptance_sha256": sha(args.source / "VERIFIED.json"),
        "discovery_older_acceptance_sha256": discovery["source_acceptance_sha256"],
        "rows": [{key: row[key] for key in
                  ("group_index", "spec", "source_OPEN_index", "source_closed_OPEN_box", "certificate")}
                 for row in discovery["proposals"]],
    }
    (args.output / "CERTIFICATE.json").write_text(json.dumps(certificate, separators=(",", ":")) + "\n", encoding="utf-8")
    manifest = {
        "schema": "N26-current-whole-OPEN-force-overlay-bindings-v1",
        "source_overlay": linux(args.source.resolve()),
        "source_overlay_replay": linux(args.source_replay.resolve()),
        "source_acceptance_sha256": sha(args.source / "VERIFIED.json"),
        "source_current_audit": linux(args.current_audit.resolve()),
        "source_current_audit_sha256": sha(args.current_audit),
        "copied_files": {name: sha(args.output / name) for _, name in copies},
    }
    manifest["copied_files"]["CERTIFICATE.json"] = sha(args.output / "CERTIFICATE.json")
    (args.output / "MANIFEST.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    subprocess.run([sys.executable, str(args.output / "verify_current_force_open_overlay.py"),
                    "--input", str(args.output), "--report", str(args.output / "VERIFIED.json")], check=True)


def main():
    parser = argparse.ArgumentParser()
    for key in ("input", "report", "source", "source-replay", "current-audit", "discovery", "output"):
        parser.add_argument("--" + key, type=Path)
    args = parser.parse_args()
    if args.input and args.report:
        verify(args.input.resolve(), args.report.resolve())
    elif all((args.source, args.source_replay, args.current_audit, args.discovery, args.output)):
        build(args)
    else:
        parser.error("provide standalone replay or all whole-OPEN force build inputs")


if __name__ == "__main__":
    main()
