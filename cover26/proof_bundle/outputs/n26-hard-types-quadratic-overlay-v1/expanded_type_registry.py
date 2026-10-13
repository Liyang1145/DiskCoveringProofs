"""Exact current catalogue registry with transparent reuse of full type proofs."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path
import subprocess
import sys

from audit_prefix_partition import linux
import verify_selected_Rstar_frontier as partition
import verify_selected_type_trees as typed
import verify_terminal_catalog as catalog


def sources(catalog_folder, catalog_replay, pool_folder, pool_replay):
    cat_report, inventory = typed.bound(catalog_folder)
    pool_report, paths = typed.bound(pool_folder)
    inventory.extend(paths)
    if typed.read(catalog_replay) != cat_report or typed.read(pool_replay) != pool_report:
        raise ValueError("expanded registry requires actual matching catalogue and pool replays")
    inventory.extend([catalog_replay, pool_replay])
    values = catalog.input_gate(catalog_folder)
    table = catalog.reconstruct(catalog_folder, *values[1:])
    if table != typed.read(catalog_folder / "CATALOG.json"):
        raise ValueError("expanded current catalogue did not reconstruct")
    stage_folder, accepted_stage, frontier = values[1:4]
    if (accepted_stage["radius_scope"] != typed.SCOPE
            or pool_report["radius_scope"] != typed.SCOPE
            or F(accepted_stage["radius_upper"]) != F(pool_report["radius_upper"])):
        raise ValueError("expanded registry changed its Rstar conditional source")
    stage_manifest = typed.read(stage_folder / "MANIFEST.json")
    basis_folder = catalog.local_path(stage_manifest["radius_basis"])
    basis, paths = typed.bound(basis_folder)
    inventory.extend(paths)
    if (pool_report["source_acceptance_sha256"] != basis["source_acceptance_sha256"]
            or pool_report["r_strict_interval"] != basis["r_strict_interval"]
            or catalog.sha(basis_folder / "VERIFIED.json") != accepted_stage["radius_basis_acceptance_sha256"]):
        raise ValueError("expanded registry proof pool is not the same covering root as the new stage")
    inventory.append(stage_folder / "VERIFIED.json")
    inventory.extend(stage_folder / name for name in accepted_stage["files"])
    pool_classification = typed.read(pool_folder / "CLASSIFICATION.json")
    pool_pending = typed.read(pool_folder / "PENDING-TYPES.json")
    pool_domains = typed.read(pool_folder / "DOMAINS.json")
    pool_certificate = typed.read(pool_folder / "CERTIFICATE.json")
    return (cat_report, pool_report, inventory, values, table, pool_classification,
            pool_pending, pool_domains, pool_certificate)


def input_gate(folder):
    manifest = typed.read(folder / "MANIFEST.json")
    if manifest["schema"] != "N26-expanded-current-canonical-type-registry-bindings-v1":
        raise ValueError("wrong expanded registry manifest")
    for name, digest in manifest["copied_files"].items():
        if catalog.sha(folder / name) != digest:
            raise ValueError("expanded registry sealed input changed: " + name)
    values = sources(*[catalog.local_path(manifest[key]) for key in
                       ("source_catalog", "source_catalog_replay", "source_pool", "source_pool_replay")])
    cat_report, pool_report, inventory, catalog_values, table, pool_rows, pool_pending, pool_domains, pool_certificate = values
    if (catalog.sha(catalog.local_path(manifest["source_catalog"]) / "VERIFIED.json") != manifest["catalog_acceptance_sha256"]
            or catalog.sha(catalog.local_path(manifest["source_pool"]) / "VERIFIED.json") != manifest["pool_acceptance_sha256"]
            or typed.read(folder / "SOURCE-CATALOG.json") != table
            or typed.read(folder / "SOURCE-CONDITIONAL-FRONTIER.json") != catalog_values[3]):
        raise ValueError("expanded registry substituted a current graph or proof pool")
    for module in (typed, catalog, typed.canonical, typed.constraints, typed.direct,
                   typed.force, typed.pin, typed.stress, typed.exact, typed.geometry, typed.tree, typed.correlated):
        name = Path(module.__file__).name
        if catalog.sha(module.__file__) != pool_report["files"][name]:
            raise ValueError("expanded registry imported different accepted exact arithmetic")
    base = typed.read(folder / "BASE-PARTITION-ACCEPTANCE.json")
    if (not base["verified"] or base["radius_scope"] != typed.SCOPE
            or catalog.sha(partition.__file__) != base["files"]["verify_selected_Rstar_frontier.py"]):
        raise ValueError("expanded registry partition arithmetic changed")
    pool_folder = catalog.local_path(manifest["source_pool"])
    stress_report = typed.read(pool_folder / "STRESS-SOURCE/VERIFIED.json")
    root_values = typed.replay_same_root(pool_folder / "STRESS-SOURCE", stress_report)
    radius = root_values[3]
    cap = typed.read(pool_folder / "CAP-SOURCE/CERTIFICATE.json")
    arcs = typed.force.load_trig(folder)[0]
    caps, margins = typed.constraints.cap_gate(radius, cap, arcs)
    if str(radius) != pool_report["radius_upper"]:
        raise ValueError("expanded registry radius endpoint did not exactly replay")
    certificate = typed.read(folder / "CERTIFICATE.json")
    if (certificate["schema"] != "N26-expanded-current-canonical-type-registry-certificate-v1"
            or certificate["radius_scope"] != typed.SCOPE or F(certificate["radius_upper"]) != radius
            or certificate["catalog_acceptance_sha256"] != manifest["catalog_acceptance_sha256"]
            or certificate["pool_acceptance_sha256"] != manifest["pool_acceptance_sha256"]):
        raise ValueError("expanded registry changed its exact graph, root or radius scope")
    candidate_group = typed.coverage_gate(certificate["types"], table)
    positive = typed.candidate_control(*root_values[:3], catalog_values[5], table,
                                      candidate_group, cap, caps, arcs)
    return (manifest, pool_report, inventory, catalog_values, table, pool_rows,
            pool_pending, pool_domains, pool_certificate, radius, caps, arcs, certificate, positive)


def derive(table, pool_report, pool_rows, pool_pending, pool_domains, pool_certificate,
           certificate, radius, caps, arcs, source, candidate):
    typed.coverage_gate(certificate["types"], table)
    by_pool = {row["group_index"]: row for row in pool_rows}
    pending_by_pool = {row["group_index"]: row for row in pool_pending}
    domains_by_pool = {row["group_index"]: row for row in pool_domains}
    cert_by_pool = {row["group_index"]: row for row in pool_certificate["types"]}
    classifications, pending, ledgers, domains, reused = [], [], [], [], []
    for row in certificate["types"]:
        index, spec = row["group_index"], row["spec"]
        if row["kind"] == "TREE":
            bare = {key: row[key] for key in ("group_index", "spec")}
            if row.get("sharp_domain_empty"):
                if set(row) != {"group_index", "spec", "kind", "sharp_domain_empty"}:
                    raise ValueError("expanded empty root has unverified fields")
                bare["sharp_domain_empty"] = True
            else:
                if set(row) != {"group_index", "spec", "kind", "nodes"}:
                    raise ValueError("expanded new tree has unverified fields")
                bare["nodes"] = row["nodes"]
            a, b, c, d = typed.derive(table, {"types": [bare]}, radius, caps, arcs)
            classifications.extend(a)
            pending.extend(b)
            ledgers.extend(c)
            domains.extend(d)
        elif row["kind"] == "REUSE":
            if set(row) != {"group_index", "spec", "kind", "pool_type_index"}:
                raise ValueError("reused type has unverified status overrides")
            old_index = row["pool_type_index"]
            if type(old_index) is not int or old_index not in by_pool:
                raise ValueError("unknown or invalid reused full type")
            old = by_pool[old_index]
            old_pending = pending_by_pool[old_index]
            if (old["spec"] != spec or cert_by_pool[old_index]["spec"] != spec
                    or old_pending["spec"] != spec or old["radius_scope"] != typed.SCOPE
                    or old["unresolved_closed_boxes"] != len(old_pending["closed_OPEN_boxes"])
                    or old["radius_at_most_Rstar_type_excluded"] != (not old_pending["closed_OPEN_boxes"])):
                raise ValueError("reused full canonical type or its OPEN boxes changed")
            matrix, derivation = typed.constraints.constraint_matrix(spec, caps)
            independent, alternative = typed.independent_matrix(spec, caps)
            if matrix != independent or matrix != domains_by_pool[old_index]["matrix"]:
                raise ValueError("reused type's exact full root domain changed")
            group = table["groups"][index]
            members = [{"catalog_member_index": member, "B": table["rows"][member]["B"],
                        "prefix": table["rows"][member]["prefix"],
                        "canonical_bijections": table["rows"][member]["canonical"]["canonical_bijections"]}
                       for member in group["member_indices"]]
            classifications.append({**old, "group_index": index, "members": members,
                                    "proof_source": "bound-actual-published-complete-type-tree",
                                    "pool_type_index": old_index})
            pending.append({**old_pending, "group_index": index})
            ledgers.append({"group_index": index, "reused_pool_type_index": old_index,
                            "reused_pool_acceptance_sha256": certificate["pool_acceptance_sha256"],
                            "reused_full_lower_ledger_sha256": pool_report["files"]["LOWER-LEDGER.json"],
                            "all_original_closed_and_OPEN_leaves_preserved": True})
            domains.append({"group_index": index, "matrix": matrix,
                            "all_pairs_Bellman_Ford_derivation": derivation,
                            "independent_BFS_Floyd_derivation": alternative,
                            "same_complete_domain_as_pool_type_index": old_index})
            reused.append({"current_group_index": index, "pool_type_index": old_index,
                           "identical_full_spec_radius_and_sharp_matrix": True,
                           "prior_actual_published_replay_bound_not_claimed_rerun_here": True})
        else:
            raise ValueError("unknown expanded type proof source")
    frontier, removal = partition.derive(source, table, classifications, pending, candidate)
    frontier["schema"] = "N26-expanded-canonical-type-Rstar-conditional-frontier-v1"
    frontier["source_radius_conditional_pending_subtrees"] = frontier.pop("source_original_U_pending_subtrees")
    frontier["all_nonremoved_source_conditional_states_preserved_byte_semantically"] = frontier.pop(
        "all_nonremoved_original_U_states_preserved_byte_semantically")
    frontier["radius_upper"] = str(radius)
    for item in removal:
        item["unchanged_source_radius_conditional_state"] = item.pop("unchanged_original_U_state")
    return classifications, pending, ledgers, domains, reused, frontier, removal


def verify(folder, report_path):
    if report_path.exists():
        raise FileExistsError(report_path)
    values = input_gate(folder)
    manifest, pool_report, inventory, cv, table, pool_rows, pool_pending, pool_domains, pool_cert, radius, caps, arcs, certificate, positive = values
    digests = {linux(path): catalog.sha(path) for path in inventory}
    result = derive(table, pool_report, pool_rows, pool_pending, pool_domains, pool_cert,
                    certificate, radius, caps, arcs, cv[3], cv[5])
    classification, pending, ledgers, domains, reused, frontier, removal = result
    negatives = []

    def reject(label, call):
        try:
            call()
        except (ValueError, KeyError, TypeError, IndexError):
            negatives.append(label)
        else:
            raise AssertionError("invalid expanded registry accepted: " + label)

    reject("missing-current-competitor-type", lambda: typed.coverage_gate(certificate["types"][:-1], table))
    reject("duplicated-current-competitor-type", lambda: typed.coverage_gate(
        certificate["types"] + certificate["types"][:1], table))
    one = next(row for row in certificate["types"] if row["kind"] == "REUSE")
    bad = deepcopy(one)
    bad["pool_type_index"] = -1
    bad_certificate = {**certificate, "types": [bad if row is one else row for row in certificate["types"]]}
    reject("invalid-reused-full-type-index", lambda: derive(
        table, pool_report, pool_rows, pool_pending, pool_domains, pool_cert,
        bad_certificate, radius, caps, arcs, cv[3], cv[5]))
    bad = deepcopy(one)
    bad["radius_at_most_Rstar_type_excluded"] = True
    bad_certificate = {**certificate, "types": [bad if row is one else row for row in certificate["types"]]}
    reject("pending-reused-type-status-overridden-to-closed", lambda: derive(
        table, pool_report, pool_rows, pool_pending, pool_domains, pool_cert,
        bad_certificate, radius, caps, arcs, cv[3], cv[5]))
    tree_row = next(row for row in certificate["types"] if row["kind"] == "TREE" and "nodes" in row)
    matrix = next(row["matrix"] for row in domains if row["group_index"] == tree_row["group_index"])
    bad_nodes = deepcopy(tree_row["nodes"])
    split = next(node for node in bad_nodes if node["kind"] == "SPLIT")
    split["children"][1] = split["children"][0]
    reject("new-type-closed-half-lost",
           lambda: typed.tree.replay(tree_row["spec"], matrix, radius, bad_nodes, arcs))
    reject("new-nonempty-type-falsely-empty", lambda: typed.tree.replay(
        tree_row["spec"], matrix, radius, [{"kind": "EMPTY"}], arcs))
    bad_nodes = deepcopy(tree_row["nodes"])
    bad_nodes.append({"kind": "OPEN"})
    reject("new-type-hidden-OPEN", lambda: typed.tree.replay(tree_row["spec"], matrix, radius, bad_nodes, arcs))
    bad_nodes = deepcopy(tree_row["nodes"])
    node = next(node for node in bad_nodes if node["kind"] == "CORRELATED_FORCE")
    node["cert"]["mu"] = [[0, 1, "-1"]]
    reject("new-type-negative-difference-dual",
           lambda: typed.tree.replay(tree_row["spec"], matrix, radius, bad_nodes, arcs))
    reject("new-type-nonstrict-radius-payment", lambda: typed.strict_margin(radius, radius))
    bad_source = deepcopy(cv[3])
    bad_source["pending_states"] = [row for row in bad_source["pending_states"] if row["prefix"] != cv[5]["prefix"]]
    reject("candidate-lost-from-expanded-conditional-partition",
           lambda: partition.derive(bad_source, table, classification, pending, cv[5]))
    bad_classification = deepcopy(classification)
    bad_classification[0]["radius_scope"] = "unconditional-original-U"
    reject("expanded-conditional-exclusion-promoted-to-U",
           lambda: partition.derive(cv[3], table, bad_classification, pending, cv[5]))
    controls = typed.correlated.controls(arcs)
    for name, data in (("CLASSIFICATION.json", classification), ("PENDING-TYPES.json", pending),
                       ("LOWER-LEDGER.json", ledgers), ("DOMAINS.json", domains), ("REUSED-TYPES.json", reused),
                       ("RSTAR-COMPETITOR-FRONTIER.json", frontier), ("CONDITIONAL-REMOVAL-LEDGER.json", removal),
                       ("CANDIDATE-POSITIVE-CONTROL.json", positive)):
        typed.publish_or_match(folder / name, data)
    excluded = [row["group_index"] for row in classification if row["radius_at_most_Rstar_type_excluded"]]
    report = {
        "schema": "N26-accepted-expanded-current-canonical-type-registry-v1", "verified": True,
        "radius_scope": typed.SCOPE, "radius_upper": str(radius),
        "r_strict_interval": pool_report["r_strict_interval"],
        "catalog_acceptance_sha256": manifest["catalog_acceptance_sha256"],
        "pool_acceptance_sha256": manifest["pool_acceptance_sha256"],
        "current_selected_terminal_paths": table["selected_terminal_paths"],
        "current_distinct_selected_canonical_types": table["distinct_selected_canonical_types"],
        "all_current_noncandidate_types_explicitly_accounted_for": True,
        "new_full_type_trees_exactly_replayed_here": sum(row["kind"] == "TREE" for row in certificate["types"]),
        "identical_full_type_trees_reused_with_bound_prior_actual_replay": len(reused),
        "strict_radius_conditional_current_type_exclusions": excluded,
        "newly_removed_current_full_terminal_paths": len(removal),
        "unresolved_current_competitor_types": len(classification) - len(excluded),
        "unresolved_current_competitor_closed_boxes": sum(len(row["closed_OPEN_boxes"]) for row in pending),
        "source_conditional_pending_subtrees": len(cv[3]["pending_states"]),
        "conditional_frontier_pending_subtrees": len(frontier["pending_states"]),
        "conditional_frontier_families": frontier["families"],
        "known_candidate_unique_complete_34_face_terminal": cv[5]["prefix"],
        "same_root_cover_and_exact_candidate_positive_control_replayed": True,
        "all_full_bijections_boundary_cycles_and_face_images_rechecked": True,
        "all_siblings_unclosed_types_OPEN_boxes_and_old_proofs_retained": True,
        "original_U_frontier_nodes_removed": 0,
        "force_positive_controls": controls, "negative_controls_rejected": negatives,
        "unrestricted_reduction_final_joint_acceptance": False,
        "full_catalog_complete": False, "global_lower_bound_proved": False,
        "global_optimality_proved": False, "n27_started": False,
        "files": {name: catalog.sha(folder / name) for name in [
            "MANIFEST.json", *manifest["copied_files"], "CLASSIFICATION.json", "PENDING-TYPES.json",
            "LOWER-LEDGER.json", "DOMAINS.json", "REUSED-TYPES.json", "RSTAR-COMPETITOR-FRONTIER.json",
            "CONDITIONAL-REMOVAL-LEDGER.json", "CANDIDATE-POSITIVE-CONTROL.json"]},
        "source_files": digests, "executed_checker_sha256": catalog.sha(__file__)}
    if report["executed_checker_sha256"] != report["files"]["expanded_type_registry.py"]:
        raise ValueError("expanded registry executed a different sealed checker")
    for text, digest in digests.items():
        if catalog.sha(text) != digest:
            raise ValueError("expanded registry historical bytes changed during replay")
    for name, digest in manifest["copied_files"].items():
        if catalog.sha(folder / name) != digest:
            raise ValueError("expanded registry sealed inputs changed during replay")
    report_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in report.items() if key not in ("files", "source_files")}, indent=2), flush=True)


def build(args):
    if args.output.exists():
        raise FileExistsError(args.output)
    values = sources(args.catalog, args.catalog_replay, args.pool, args.pool_replay)
    cat_report, pool_report, inventory, cv, table, pool_rows, pool_pending, pool_domains, pool_certificate = values
    proposal = typed.read(args.proposal)
    if (proposal["schema"] != "N26-unaccepted-selected-canonical-type-sharp-trees-v1"
            or proposal["verified"] is not False or proposal["radius_scope"] != typed.SCOPE
            or proposal["catalog_acceptance_sha256"] != catalog.sha(args.catalog / "VERIFIED.json")
            or proposal["cap_acceptance_sha256"] != pool_report["source_acceptance_sha256"]["caps"]):
        raise ValueError("expanded discovery changed the current catalogue or certified radius")
    typed.coverage_gate(proposal["proposals"], table)
    pool_by_code = {(row["spec"]["B"], tuple(row["spec"]["faces"])): row for row in pool_rows}
    types = []
    for row in proposal["proposals"]:
        old = pool_by_code.get((row["spec"]["B"], tuple(row["spec"]["faces"])))
        item = {"group_index": row["group_index"], "spec": row["spec"]}
        newly_closed = row.get("replayed_discovery_counts", {}).get("radius_at_most_Rstar_type_excluded", False)
        if old is not None and not (newly_closed and not old["radius_at_most_Rstar_type_excluded"]):
            item.update({"kind": "REUSE", "pool_type_index": old["group_index"]})
        else:
            item["kind"] = "TREE"
            item.update({"sharp_domain_empty": True} if row.get("sharp_domain_empty") else {"nodes": row["nodes"]})
        types.append(item)
    certificate = {"schema": "N26-expanded-current-canonical-type-registry-certificate-v1",
                   "radius_scope": typed.SCOPE, "radius_upper": pool_report["radius_upper"],
                   "catalog_acceptance_sha256": catalog.sha(args.catalog / "VERIFIED.json"),
                   "pool_acceptance_sha256": catalog.sha(args.pool / "VERIFIED.json"), "types": types}
    args.output.mkdir(parents=True)
    base_folder = args.pool.parent / "n26-selected-Rstar-competitor-frontier-v2"
    base_report = typed.bound(base_folder)[0]
    if base_report["files"]["verify_selected_type_trees.py"] != pool_report["files"]["verify_selected_type_trees.py"]:
        raise ValueError("expanded registry base partition uses different type arithmetic")
    copies = [(args.pool / name, name) for name in pool_report["files"] if "/" not in name and name.endswith(".py")]
    copies.extend([
        (args.pool / "exact_arcs.py", "exact_arcs.py"),
        (base_folder / "verify_selected_Rstar_frontier.py", "verify_selected_Rstar_frontier.py"),
        (base_folder / "VERIFIED.json", "BASE-PARTITION-ACCEPTANCE.json"),
        (args.catalog / "CATALOG.json", "SOURCE-CATALOG.json"),
        (args.catalog / "SOURCE-FRONTIER.json", "SOURCE-CONDITIONAL-FRONTIER.json"),
        (args.proposal, "PROPOSAL.json"), (Path(__file__), "expanded_type_registry.py")])
    proof = Path(__file__).with_name("n26-expanded-type-registry-proof.md")
    if not proof.exists():
        proof = Path(__file__).with_name("PROOF.md")
    copies.append((proof, "PROOF.md"))
    for original, name in copies:
        (args.output / name).write_bytes(original.read_bytes())
    (args.output / "CERTIFICATE.json").write_text(json.dumps(certificate, separators=(",", ":")) + "\n", encoding="utf-8")
    manifest = {
        "schema": "N26-expanded-current-canonical-type-registry-bindings-v1",
        "source_catalog": linux(args.catalog), "source_catalog_replay": linux(args.catalog_replay),
        "source_pool": linux(args.pool), "source_pool_replay": linux(args.pool_replay),
        "catalog_acceptance_sha256": catalog.sha(args.catalog / "VERIFIED.json"),
        "pool_acceptance_sha256": catalog.sha(args.pool / "VERIFIED.json"),
        "copied_files": {name: catalog.sha(args.output / name) for _, name in copies}}
    manifest["copied_files"]["CERTIFICATE.json"] = catalog.sha(args.output / "CERTIFICATE.json")
    (args.output / "MANIFEST.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    run = subprocess.run([sys.executable, str(args.output / "expanded_type_registry.py"),
                          "--input", str(args.output), "--report", str(args.output / "VERIFIED.json")], check=False)
    if run.returncode:
        raise ValueError("expanded registry exact acceptance failed; incomplete bundle preserved")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path)
    parser.add_argument("--report", type=Path)
    parser.add_argument("--catalog", type=Path)
    parser.add_argument("--catalog-replay", type=Path)
    parser.add_argument("--pool", type=Path)
    parser.add_argument("--pool-replay", type=Path)
    parser.add_argument("--proposal", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.input and args.report:
        verify(args.input, args.report)
    elif all((args.catalog, args.catalog_replay, args.pool, args.pool_replay, args.proposal, args.output)):
        build(args)
    else:
        parser.error("provide --input/--report, or all six build inputs")


if __name__ == "__main__":
    main()
