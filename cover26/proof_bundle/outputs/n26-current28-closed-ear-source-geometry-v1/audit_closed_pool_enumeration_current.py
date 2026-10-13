"""Retain the entire closed-type proof pool across a new enumeration catalogue."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import verify_conditional_force_stage as binding
import verify_terminal_catalog as catalog


def pool_gate(pool, parent, radius):
    folders = {}
    for text, digest in parent["files"].items():
        path = binding.local_path(text)
        if path.name == "VERIFIED.json":
            folders.setdefault(digest, []).append(path.parent)
    codes, receipts, cache = set(), [], {}
    for index, item in enumerate(pool):
        spec = item["spec"]
        code = spec["B"], tuple(spec["faces"])
        if (item["radius_scope"] != binding.SCOPE or spec["N"] != 26 or spec["next"] != 26
                or code in codes or not item["proof_sources"]):
            raise ValueError("closed pool lost its full type, conditional scope or distinct proof ownership")
        codes.add(code)
        for j, receipt in enumerate(item["proof_sources"]):
            digest, group = receipt["acceptance_sha256"], receipt["group_index"]
            if digest not in folders or type(group) is not int:
                raise ValueError("closed pool receipt is not a bound actual acceptance")
            matches = []
            for folder in folders[digest]:
                if folder not in cache:
                    acceptance = binding.read(folder / "VERIFIED.json")
                    classification = folder / "CLASSIFICATION.json"
                    if (classification.exists()
                            and parent["files"].get(linux(classification)) == binding.sha(classification)):
                        cache[folder] = acceptance, {
                            row["group_index"]: row for row in binding.read(classification)}
                    else:
                        cache[folder] = acceptance, {}
                acceptance, classes = cache[folder]
                row = classes.get(group)
                if (row is not None and row["spec"] == spec and row["radius_at_most_Rstar_type_excluded"]
                        and acceptance["verified"] and acceptance["global_optimality_proved"] is False
                        and acceptance["radius_scope"] == binding.SCOPE
                        and F(acceptance["radius_upper"]) == radius):
                    matches.append(folder)
            if not matches:
                raise ValueError("closed receipt has no identical complete excluded type at the same root")
            receipts.append({"pool_type_index": index, "proof_receipt_index": j,
                             "source_acceptance_sha256": digest, "source_group_index": group,
                             "actual_source_folder": linux(matches[0]),
                             "identical_full_spec_radius_and_closed_classification_checked": True})
    return receipts


def main():
    parser = argparse.ArgumentParser()
    for key in ("parent-audit", "enumeration-audit", "stage", "catalog", "output"):
        parser.add_argument("--" + key, type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    parent, base = binding.read(args.parent_audit), binding.read(args.enumeration_audit)
    if (not base["current_bound_bytes_rechecked"]
            or not base["new_conditional_stage_actual_published_replay_matched_and_semantics_replayed_here"]
            or base["prior_current_audit_sha256"] != binding.sha(args.parent_audit)
            or base["r_strict_interval"] != parent["r_strict_interval"]
            or base["global_optimality_proved"] is not False):
        raise ValueError("closed-pool continuation lacks the actual current enumeration audit")
    inventory = dict(base["files"])
    for text, digest in inventory.items():
        if binding.sha(text) != digest:
            raise ValueError("enumeration current bytes changed before full-type retention")
    stage_report = binding.read(args.stage / "VERIFIED.json")
    manifest = binding.read(args.stage / "MANIFEST.json")
    if (inventory.get(linux(args.stage / "VERIFIED.json")) != binding.sha(args.stage / "VERIFIED.json")
            or inventory.get(linux(args.catalog / "VERIFIED.json")) != binding.sha(args.catalog / "VERIFIED.json")):
        raise ValueError("closed-pool continuation substituted its actual stage or catalogue")
    old = binding.read(binding.local_path(manifest["source_frontier_original_path"]))
    frontier = binding.read(args.stage / "FRONTIER.json")
    key = lambda row: (row["B"], tuple(row["prefix"]))
    new_states = {key(row): row for row in frontier["pending_states"]}
    prior_terminal = [row for row in old["pending_states"] if row["terminal"]]
    if (len(prior_terminal) != parent["current_candidate_type_paths"]
            or any(new_states.get(key(row)) != row for row in prior_terminal)):
        raise ValueError("an old complete candidate path disappeared or its raw state changed")
    table = binding.read(args.catalog / "CATALOG.json")
    if (table["selected_candidate_type_paths"] < len(prior_terminal)
            or any(not row["same_canonical_type_as_known_candidate"] for row in table["rows"])):
        raise ValueError("this candidate-only continuation has unaccounted new competitors or lost candidate paths")
    pool_path = args.parent_audit.with_name(args.parent_audit.stem + "-closed-type-pool.json")
    if parent["files"].get(linux(pool_path)) != binding.sha(pool_path):
        raise ValueError("closed-pool source is not the actual fully bound parent pool")
    pool = binding.read(pool_path)
    receipts = pool_gate(pool, parent, F(stage_report["radius_upper"]))
    negatives = []

    def reject(label, value):
        try:
            pool_gate(value, parent, F(stage_report["radius_upper"]))
        except (ValueError, KeyError, TypeError):
            negatives.append(label)
        else:
            raise AssertionError("invalid archived closed pool accepted: " + label)

    bad = deepcopy(pool)
    bad[0]["spec"]["faces"][0] ^= 1 << 25
    reject("different-full-graph-under-old-proof-receipt", bad)
    bad = deepcopy(pool)
    bad[0]["proof_sources"][0]["group_index"] = -1
    reject("wrong-source-classification-owner", bad)
    bad = deepcopy(pool)
    bad[0]["proof_sources"][0]["acceptance_sha256"] = "0" * 64
    reject("unbound-proof-acceptance", bad)
    bad = deepcopy(pool)
    bad[0]["radius_scope"] = "unconditional-original-U"
    reject("conditional-closed-type-promoted-to-U", bad)
    reject("duplicate-closed-type-code", pool + pool[:1])
    pool_target = args.output.with_name(args.output.stem + "-closed-type-pool.json")
    receipt_target = args.output.with_name(args.output.stem + "-closed-receipt-checks.json")
    if pool_target.exists() or receipt_target.exists():
        raise FileExistsError("fresh closed-pool continuation sidecars required")
    pool_target.write_bytes(pool_path.read_bytes())
    receipt_target.write_text(json.dumps(receipts, indent=2) + "\n", encoding="utf-8")
    for path in (args.parent_audit, args.enumeration_audit, Path(__file__), pool_target, receipt_target):
        text, digest = linux(path), binding.sha(path)
        if text in inventory and inventory[text] != digest:
            raise ValueError("closed-pool continuation disagrees with its current inventory")
        inventory[text] = digest
    for text, digest in inventory.items():
        if binding.sha(text) != digest:
            raise ValueError("closed-pool current bytes changed during final binding")
    report = {key: value for key, value in base.items() if key != "files"}
    report.update({
        "schema": "N26-current-successive-enumeration-and-complete-closed-pool-retention-audit-v1",
        "enumeration_current_audit_sha256": binding.sha(args.enumeration_audit),
        "parent_complete_type_audit_sha256": binding.sha(args.parent_audit),
        "all_prior_candidate_terminal_raw_states_retained_identically": True,
        "all_prior_closed_type_codes_retained_in_new_current_pool": True,
        "joined_closed_full_type_codes_in_these_two_catalogues": len(pool),
        "all_closed_type_proof_receipts_and_identical_full_graph_radius_classifications_rechecked": len(receipts),
        "current_catalogue_has_only_candidate_members": True,
        "current_candidate_type_paths": table["selected_candidate_type_paths"],
        "unresolved_current_competitor_types": 0,
        "unresolved_current_competitor_closed_boxes": 0,
        "archived_type_exclusions_not_misidentified_as_current_catalogue_indices": True,
        "closed_pool_negative_controls_rejected": negatives, "files": inventory})
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in report.items() if key != "files"}, indent=2), flush=True)


if __name__ == "__main__":
    main()
