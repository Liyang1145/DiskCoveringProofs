"""Compose a new stage with its complete catalogue and historical full-type pool.

Matches are explicitly AVAILABLE but UNAPPLIED: this audit removes no terminal.
Fresh full-type root domains are preserved for subsequent exact acceptance.
"""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import audit_closed_pool_enumeration_current as archive
import new_upper_scope as family_scope
import verify_conditional_force_stage as stage
import verify_terminal_catalog as catalog


def retained_pool_gate(pool, parent, radius):
    receipts = archive.pool_gate(pool, parent, radius)
    if (len(pool) != parent["joined_closed_full_type_codes_in_these_two_catalogues"]
            or len(receipts) != parent[
                "all_closed_type_proof_receipts_and_identical_full_graph_radius_classifications_rechecked"]):
        raise ValueError("historical closed types or their accepted proof receipts were lost")
    return receipts


def frontier_conservation_gate(source, trace, frontier, table):
    families = []
    for b in (14, 15, 16, 17):
        incoming = sum(row["B"] == b for row in source["pending_states"])
        outgoing = sum(row["B"] == b for row in frontier["pending_states"])
        events = [row for row in trace["events"] if row["B"] == b]
        splits = [row for row in events if row["kind"] == "split"]
        children = sum(row["all_child_count"] for row in splits)
        strict = sum(row["kind"] in ("force", "force_tree", "area") for row in events)
        empty = sum(row["kind"] == "empty" for row in events)
        if incoming + children - len(splits) - strict - empty != outgoing:
            raise ValueError("complete child expansion and removals do not conserve the actual frontier")
        accepted = next(row for row in frontier["families"] if row["B"] == b)
        terminals = sum(row["B"] == b and row["terminal"] for row in frontier["pending_states"])
        if (accepted["pending_subtrees"] != outgoing
                or accepted["unresolved_terminal_subtrees"] != terminals):
            raise ValueError("a raw complete terminal is absent from the accepted explicit terminal counts")
        families.append({"B": b, "source_subtrees": incoming, "split_events": len(splits),
                         "complete_immediate_children": children,
                         "strict_whole_subtrees_excluded": strict,
                         "combinatorially_empty_subtrees": empty,
                         "current_subtrees": outgoing, "retained_complete_terminals": terminals})
    key = lambda row: (row["B"], tuple(row["prefix"]))
    raw_terminals = {key(row) for row in frontier["pending_states"] if row["terminal"]}
    catalogue_members = [key(row) for row in table["rows"]]
    if (len(set(catalogue_members)) != len(catalogue_members)
            or set(catalogue_members) != raw_terminals):
        raise ValueError("the catalogue does not cover every actual raw complete terminal exactly once")
    return families


def terminal_obligations(table, pool):
    by_code = {(row["spec"]["B"], tuple(row["spec"]["faces"])): (i, row) for i, row in enumerate(pool)}
    obligations, available, fresh = [], [], []
    for i, group in enumerate(table["groups"]):
        members = [table["rows"][j] for j in group["member_indices"]]
        if any(row["same_canonical_type_as_known_candidate"] for row in members):
            if not all(row["same_canonical_type_as_known_candidate"] for row in members):
                raise ValueError("candidate and competitor share inconsistent canonical ownership")
            continue
        spec = {"N": 26, "B": group["B"], "next": 26, "faces": group["canonical_faces"]}
        prior = by_code.get((spec["B"], tuple(spec["faces"])))
        if prior is not None and prior[1]["spec"] != spec:
            raise ValueError("historical code matches but the full source graph differs")
        domain = stage.force.angular_domain(spec)
        box = None
        if domain is not None:
            lower, upper = stage.force.rootbox(domain)
            box = {"index": 0, "kind": "OPEN", "lower": list(map(str, lower)), "upper": list(map(str, upper)),
                   "domain_scope": "conservative-original-U-necessary-angle-domain"}
        row = {"current_group_index": i, "spec": spec,
               "member_indices": list(group["member_indices"]),
               "member_paths": [{"B": member["B"], "prefix": member["prefix"]} for member in members],
               "source_full_terminal_paths_retained": True,
               "full_type_radius_proof_applied_to_current_transport": False,
               "historical_closed_proof_available": prior is not None,
               "historical_pool_type_index": prior[0] if prior is not None else None,
               "conservative_U_matrix": domain, "retained_full_type_root_box": box,
               "exact_empty_U_domain_still_requires_explicit_current_terminal_transfer": domain is None}
        obligations.append(row)
        (available if prior is not None else fresh).append(i)
    return obligations, available, fresh


def main():
    parser = argparse.ArgumentParser()
    for name in ("parent-audit", "stage", "stage-replay", "catalog", "catalog-replay", "narrative", "output"):
        parser.add_argument("--" + name, type=Path, required=True)
    parser.add_argument("--dependency-note", type=Path)
    parser.add_argument("--family-scope", type=Path)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    parent = stage.read(args.parent_audit)
    if (not parent["current_bound_bytes_rechecked"]
            or not parent["prior_completed_full_chain_semantic_replay_still_bound"]
            or parent["radius_scope"] != stage.SCOPE or parent["global_optimality_proved"] is not False
            or parent["original_U_current_pending_subtrees_unchanged"] != 3922
            or parent["original_52_coordinate_local_allowance_unchanged"] != "7/800000"):
        raise ValueError("new enumeration audit lacks the accepted unchanged full current chain")
    inventory = dict(parent["files"])
    print("Rehashing the complete parent inventory.", flush=True)
    for text, digest in inventory.items():
        if stage.sha(text) != digest:
            raise ValueError("parent current dependency changed: " + text)
    accepted, paths = stage.bound(args.stage)
    if (stage.read(args.stage_replay) != accepted
            or stage.sha(stage.__file__) != accepted["files"]["verify_conditional_force_stage.py"]):
        raise ValueError("new stage lacks its actual identical sealed published replay")
    values = stage.input_gate(args.stage, args.stage.parent / "n26-multislope-area-lower-v1")
    manifest, source, old_acceptance, basis, old, multi, native, trace, files = values
    paths.extend(files)
    for field, hash_field in (("source_acceptance_original_path", "source_acceptance_sha256"),
                              ("source_frontier_original_path", "source_frontier_sha256")):
        path = stage.local_path(manifest[field])
        if inventory.get(linux(path)) != manifest[hash_field]:
            raise ValueError("new source is not the parent's actual still-bound current partition")
    if (len(source["pending_states"]) != parent["Rstar_conditional_frontier_pending_subtrees"]
            or basis["r_strict_interval"] != parent["r_strict_interval"]
            or accepted["source_conditional_pending_subtrees"] != len(source["pending_states"])):
        raise ValueError("new enumeration substituted the actual source frontier or same root")
    print("Freshly replaying every native event, complete sibling set and strict bound.", flush=True)
    candidate = stage.read(args.stage / "CANDIDATE-PATH.json")
    frontier, ledger, margins = stage.replay(
        args.stage, source, old, multi, native, trace, stage.force.load_trig(args.stage)[0],
        F(manifest["radius_upper"]), candidate)
    if (frontier != stage.read(args.stage / "FRONTIER.json")
            or ledger != stage.read(args.stage / "LOWER-LEDGER.json")
            or frontier["families"] != accepted["families"]):
        raise ValueError("new exact transport partition or payment ledger did not reconstruct")
    for name, digest in native["files"].items():
        path = args.stage / name
        if stage.sha(path) != digest:
            raise ValueError("new native event evidence changed")
        paths.append(path)
    cat_accepted, files = stage.bound(args.catalog)
    paths.extend(files)
    if (stage.read(args.catalog_replay) != cat_accepted
            or stage.sha(catalog.__file__) != cat_accepted["files"]["verify_terminal_catalog.py"]):
        raise ValueError("new catalogue lacks actual identical sealed published replay")
    cv = catalog.input_gate(args.catalog)
    table = catalog.reconstruct(args.catalog, *cv[1:])
    if (cv[1].resolve() != args.stage.resolve() or cv[2] != accepted or cv[3] != frontier
            or table != stage.read(args.catalog / "CATALOG.json")
            or len(table["rows"]) != sum(row["unresolved_terminal_subtrees"] for row in accepted["families"])):
        raise ValueError("new catalogue is not the complete actual current terminal list")
    conservation = frontier_conservation_gate(source, trace, frontier, table)
    key = lambda row: (row["B"], tuple(row["prefix"]))
    states = {key(row): row for row in frontier["pending_states"]}
    old_terminal = [row for row in source["pending_states"] if row["terminal"]]
    if any(states.get(key(row)) != row for row in old_terminal):
        raise ValueError("a source complete terminal was altered or discarded")
    candidates = [row for row in table["rows"] if row["same_canonical_type_as_known_candidate"]]
    if (len(candidates) < parent["current_candidate_type_paths"]
            or not any(row["prefix"] == candidate["prefix"] and row["B"] == 16 for row in candidates)):
        raise ValueError("a previous isomorphic candidate path disappeared")
    pool_path = args.parent_audit.with_name(args.parent_audit.stem + "-closed-type-pool.json")
    if inventory.get(linux(pool_path)) != stage.sha(pool_path):
        raise ValueError("historical full-type pool is not the actual bound current pool")
    pool = stage.read(pool_path)
    print("Checking all historical proof receipts and exact current canonical matches.", flush=True)
    receipts = retained_pool_gate(pool, parent, F(accepted["radius_upper"]))
    obligations, available, fresh = terminal_obligations(table, pool)
    covered = {j for group in table["groups"] for j in group["member_indices"]}
    if covered != set(range(len(table["rows"]))):
        raise ValueError("terminal canonical groups have incomplete member ownership")
    if any(not row["source_full_terminal_paths_retained"]
           or row["full_type_radius_proof_applied_to_current_transport"] for row in obligations):
        raise ValueError("an available proof was silently applied without terminal transfer")
    candidate_codes = {(row["B"], tuple(row["canonical"]["faces"])) for row in candidates}
    if any((item["spec"]["B"], tuple(item["spec"]["faces"])) in candidate_codes for item in pool):
        raise ValueError("known feasible candidate appears in the historical excluded-code pool")
    negatives = []

    def reject(label, changed):
        try:
            retained_pool_gate(changed, parent, F(accepted["radius_upper"]))
        except (ValueError, KeyError, TypeError):
            negatives.append(label)
        else:
            raise AssertionError("invalid historical type receipt accepted: " + label)

    bad = deepcopy(pool)
    bad[0]["proof_sources"][0]["group_index"] = -1
    reject("wrong-historical-classification-owner", bad)
    bad = deepcopy(pool)
    bad[0]["spec"]["faces"][0] ^= 1 << 25
    reject("different-full-graph-under-historical-proof", bad)
    bad = deepcopy(pool)
    bad[0]["radius_scope"] = "unconditional-original-U"
    reject("conditional-proof-promoted-to-U", bad)
    bad = deepcopy(pool)
    bad[0]["proof_sources"][0]["acceptance_sha256"] = "0" * 64
    reject("unbound-historical-proof-acceptance", bad)
    reject("duplicate-historical-full-type-code", pool + pool[:1])
    reject("missing-historical-closed-type", pool[1:])
    bad = deepcopy(pool)
    multiple = next(row for row in bad if len(row["proof_sources"]) > 1)
    multiple["proof_sources"].pop()
    reject("missing-historical-proof-receipt", bad)
    transport_negatives = []

    def reject_transport(label, changed_trace, changed_frontier, changed_table):
        try:
            frontier_conservation_gate(source, changed_trace, changed_frontier, changed_table)
        except (ValueError, KeyError, TypeError, StopIteration):
            transport_negatives.append(label)
        else:
            raise AssertionError("invalid frontier conservation or terminal coverage accepted: " + label)

    bad = deepcopy(trace)
    next(row for row in bad["events"] if row["kind"] == "split")["all_child_count"] += 1
    reject_transport("invented-immediate-child-count", bad, frontier, table)
    bad = deepcopy(table)
    bad["rows"].pop()
    reject_transport("raw-complete-terminal-omitted-from-catalogue", trace, frontier, bad)
    bad = deepcopy(frontier)
    next(row for row in bad["pending_states"] if row["terminal"])["terminal"] = False
    reject_transport("raw-complete-terminal-marked-nonterminal", trace, bad, table)
    pool_target = args.output.with_name(args.output.stem + "-closed-type-pool.json")
    receipt_target = args.output.with_name(args.output.stem + "-closed-receipt-checks.json")
    obligation_target = args.output.with_name(args.output.stem + "-terminal-obligations.json")
    if any(path.exists() for path in (pool_target, receipt_target, obligation_target)):
        raise FileExistsError("fresh enumeration audit sidecars required")
    pool_target.write_bytes(pool_path.read_bytes())
    for path, data in ((receipt_target, receipts), (obligation_target, obligations)):
        path.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    paths.extend([args.parent_audit, args.stage_replay, args.catalog_replay, args.narrative,
                  pool_target, receipt_target, obligation_target, Path(__file__),
                  Path(archive.__file__), Path(stage.__file__), Path(catalog.__file__),
                  Path(__file__).with_name("recheck_current_stage_catalogue_inventory.py")])
    if args.dependency_note:
        paths.append(args.dependency_note)
    family_checked = False
    if args.family_scope:
        scope_report = stage.read(args.family_scope / "VERIFIED.json")
        constants = stage.read(args.family_scope / "CONSTANTS.json")
        if (not scope_report["arithmetic_verified"]
                or not scope_report["family_scope_valid_assuming_cited_n8_theorem"]
                or scope_report["N8_lower_bound_reproved_here"] is not False):
            raise ValueError("external theorem family scope is not the honest accepted arithmetic dependency")
        for text, digest in scope_report["files"].items():
            if family_scope.sha(text) != digest:
                raise ValueError("original family scope dependency changed")
            paths.append(family_scope.local_path(text))
        upper_path = args.family_scope.parent / "n26-rational-upper-v1/VERIFIED.json"
        upper = stage.read(upper_path)
        for text, digest in upper["files"].items():
            if family_scope.sha(text) != digest:
                raise ValueError("conservative continuous upper dependency changed")
            paths.append(family_scope.local_path(text))
        checked = family_scope.gate(constants, upper, family_scope.load_arcs())
        if (any(constants[key] != value for key, value in checked.items())
                or F(accepted["radius_upper"]) >= F(constants["radius_upper"])
                or F(constants["radius_upper"]) != stage.force.U):
            raise ValueError("four-family arithmetic changed or does not cover the sharp same-root radius")
        paths.extend([args.family_scope / "VERIFIED.json", args.family_scope / "CONSTANTS.json",
                      args.family_scope / "DEPENDENCIES.json", upper_path, Path(family_scope.__file__)])
        family_checked = True
    for path in paths:
        text, digest = linux(path), stage.sha(path)
        if text in inventory and inventory[text] != digest:
            raise ValueError("old and new current inventories disagree")
        inventory[text] = digest
    print("Rehashing every final current dependency.", flush=True)
    for text, digest in inventory.items():
        if stage.sha(text) != digest:
            raise ValueError("new current bytes changed during final binding")
    report = {
        "schema": "N26-current-stage-catalogue-and-complete-historical-proof-pool-audit-v1",
        "current_bound_bytes_rechecked": True,
        "prior_completed_full_chain_semantic_replay_still_bound": True,
        "prior_current_audit_sha256": stage.sha(args.parent_audit),
        "prior_current_file_digests_rechecked": len(parent["files"]),
        "new_conditional_stage_actual_published_replay_matched_and_semantics_replayed_here": True,
        "new_native_events_and_all_immediate_siblings_rechecked": native["native_events_checked"],
        "source_conditional_pending_subtrees": len(source["pending_states"]),
        "new_stage_event_counts": accepted["event_counts"],
        "new_strict_radius_conditional_whole_subtrees_excluded":
            accepted["new_strict_radius_conditional_whole_transport_subtrees_excluded"],
        "Rstar_conditional_frontier_pending_subtrees": len(frontier["pending_states"]),
        "Rstar_conditional_frontier_families": frontier["families"],
        "frontier_conservation_per_family_independently_checked": conservation,
        "catalogue_covers_every_actual_raw_complete_terminal_exactly_once": True,
        "all_current_unresolved_terminal_paths_reconstructed": len(table["rows"]),
        "current_distinct_selected_terminal_types": len(table["groups"]),
        "current_candidate_type_paths": len(candidates),
        "all_isomorphic_candidate_terminal_paths_retained": True,
        "all_source_complete_terminal_raw_states_retained_identically": True,
        "joined_closed_full_type_codes_in_these_two_catalogues": len(pool),
        "all_closed_type_proof_receipts_and_identical_full_graph_radius_classifications_rechecked": len(receipts),
        "current_competitor_groups_with_checked_historical_proofs_available_but_not_applied": available,
        "current_fresh_competitor_groups_without_historical_proofs": fresh,
        "all_current_competitor_terminal_obligations_explicitly_retained": obligations,
        "unresolved_current_competitor_types": len(obligations),
        "unresolved_current_competitor_closed_boxes": sum(
            row["retained_full_type_root_box"] is not None for row in obligations),
        "no_full_type_transport_exclusion_silently_applied_by_this_audit": True,
        "new_current_catalogue_actual_published_replay_and_every_bijection_reconstructed": True,
        "known_candidate_unique_complete_34_face_terminal": candidate["prefix"],
        "all_siblings_unresolved_terminals_OPEN_boundaries_and_old_proofs_retained": True,
        "original_U_current_pending_subtrees_unchanged": parent["original_U_current_pending_subtrees_unchanged"],
        "original_U_frontier_nodes_removed_by_conditional_bundle": 0,
        "r_strict_interval": accepted["r_strict_interval"],
        "original_52_coordinate_local_allowance_unchanged": "7/800000",
        "candidate_angle_unresolved_closed_boxes": parent["candidate_angle_unresolved_closed_boxes"],
        "radius_scope": stage.SCOPE, "screen_radius_threshold": str(stage.force.U),
        "inherited_source_is_unconditional_at_U": False,
        "Fejes_Toth_eight_disk_lower_bound_remains_external_dependency": True,
        "external_dependency_source_review_bound_not_a_new_theorem_reproof": args.dependency_note is not None,
        "original_four_family_arithmetic_and_external_PDF_dependency_freshly_checked_and_bound": family_checked,
        "unrestricted_reduction_final_joint_acceptance": False,
        "full_catalog_complete": False, "global_lower_bound_proved": False,
        "global_optimality_proved": False, "n27_started": False,
        "closed_pool_negative_controls_rejected": negatives,
        "frontier_conservation_and_terminal_negative_controls_rejected": transport_negatives,
        "files": inventory}
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in report.items() if key != "files"}, indent=2), flush=True)


if __name__ == "__main__":
    main()
