"""Independent complete-current final for the new whole-prefix ear rule."""

import argparse
from fractions import Fraction as F
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import sys

from audit_prefix_origin import OriginReference
import n26_force as force
import n26_closed_ear_current_accounting as accounting
import n26_current_candidate_layer_identity as identity


def local_path(value):
    text = str(value).replace("\\", "/")
    if sys.platform == "win32" and text.startswith("/mnt/"):
        return Path(text[5].upper()+":"+text[6:])
    if sys.platform != "win32" and len(text) > 2 and text[1] == ":":
        return Path("/mnt/"+text[0].lower()+text[2:])
    return Path(text)


def sha(path):
    digest = hashlib.sha256()
    with local_path(path).open("rb") as source:
        for block in iter(lambda: source.read(1024*1024), b""):
            digest.update(block)
    return digest.hexdigest()


def read(path):
    return json.loads(local_path(path).read_text(encoding="utf-8"))


def main():
    parser = argparse.ArgumentParser()
    for name in ("current-audit", "geometry", "geometry-replay", "report"):
        parser.add_argument("--"+name, type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError("independent ear final never overwrites an existing report")
    initial = sha(args.current_audit)
    current = read(args.current_audit)
    if current["schema"] != accounting.CURRENT_SCHEMA:
        raise ValueError("ear final cannot substitute the old native-stage final checker")
    inventory = current["files"]
    normalized = {str(local_path(text).resolve()): digest for text, digest in inventory.items()}
    if len(normalized) != len(inventory):
        raise ValueError("ear final has duplicate normalized dependency identities")

    def bound_path(path):
        if normalized.get(str(local_path(path).resolve())) != sha(path):
            raise ValueError("independent ear final has an unbound or changed input: "+str(path))

    for number, (text, digest) in enumerate(inventory.items(), 1):
        if sha(text) != digest:
            raise ValueError("independent ear final current dependency changed: "+text)
        if number % 10000 == 0:
            print(json.dumps({"closed_ear_final_inventory_rehashed": number,
                              "total": len(inventory)}), flush=True)
    parent_path = local_path(current["closed_ear_parent_audit_file"])
    final_path = local_path(current["closed_ear_parent_final_file"])
    for path in (parent_path, final_path):
        bound_path(path)
    parent, parent_final = read(parent_path), read(final_path)
    parent_digest, final_digest = sha(parent_path), sha(final_path)
    if (
        parent_digest != current["prior_current_audit_sha256"]
        or final_digest != current["closed_ear_parent_final_sha256"]
        or parent_final["current_audit_sha256"] != parent_digest
        or parent_final["all_current_file_digests_rehashed"] is not True
        or parent_final["current_file_digests_rechecked"] != len(parent["files"])
        or parent["current_bound_bytes_rechecked"] is not True
        or parent["prior_completed_full_chain_semantic_replay_still_bound"] is not True
        or parent["Rstar_conditional_frontier_pending_subtrees"] != 11183
    ):
        raise ValueError("ear independent final lost the actual completed source/current pair")
    if (
        local_path(current["closed_ear_geometry_folder"]).resolve() != args.geometry.resolve()
        or local_path(current["closed_ear_geometry_publication_file"]).resolve() != args.geometry_replay.resolve()
        or local_path(current["current_frontier_actual_file"]).resolve() != (args.geometry/"FRONTIER.json").resolve()
    ):
        raise ValueError("ear final was passed a different actual geometry/frontier/publication")
    manifest_path = args.geometry/"MANIFEST.json"
    manifest = read(manifest_path)
    source_path = local_path(manifest["source_frontier"])
    if (
        manifest["parent_current_sha256"] != parent_digest
        or manifest["parent_final_sha256"] != final_digest
        or local_path(manifest["parent_current"]).resolve() != parent_path.resolve()
        or local_path(manifest["parent_final"]).resolve() != final_path.resolve()
        or sha(source_path) != manifest["source_frontier_sha256"]
        or read(source_path) != read(args.geometry/"SOURCE-FRONTIER.json")
    ):
        raise ValueError("ear final substituted the actual original source")
    source = read(source_path)
    frontier, ledger = read(args.geometry/"FRONTIER.json"), read(args.geometry/"LOWER-LEDGER.json")
    constants = read(args.geometry/"FAMILY-CONSTANTS.json")
    proofs = {key: sha(args.geometry/name) for key, name in {
        "cap": "UNIT-CAP-PROOF.md", "generic": "GENERIC-SLACK-PROOF.md",
        "bridge": "EMBEDDED-CORNER-SHADOW-BRIDGE-PROOF.md", "ear": "CLOSED-EAR-PROOF.md",
    }.items()}
    candidate_folder = local_path(manifest["actual_candidate_source"])
    layer = identity.gate(parent, parent_digest, candidate_folder, reader=read, hasher=sha)
    accepted = read(args.geometry/"VERIFIED.json")
    semantic_path = local_path(current["closed_ear_geometry_semantic_replay_file"])
    accounting.receipt_gate(
        parent, parent_digest, final_digest, accepted, read(args.geometry_replay),
        read(semantic_path), sha(args.geometry/accounting.CHECKER), layer)
    if (
        sha(args.geometry/"VERIFIED.json") != sha(args.geometry_replay)
        or sha(args.geometry/"VERIFIED.json") != sha(semantic_path)
        or accepted["actual_source_frontier_sha256"] != sha(source_path)
        or current["closed_ear_full_current_semantic_command"][1] != str(args.geometry/accounting.CHECKER)
    ):
        raise ValueError("ear final lacks the actual byte-identical full-main report triple")
    # Complete original-prefix reconstruction is performed here, rather than
    # trusting the producer's source-index list or its recorded counts.
    references = {b: OriginReference(26, b, "dfs", caps=force.CAPS, scale=force.D)
                  for b in (14, 15, 16, 17)}
    for reference in references.values():
        reference.children = lru_cache(None)(reference.children)
    for number, row in enumerate(source["pending_states"], 1):
        reference = references[row["B"]]
        prefix = tuple(row["prefix"])
        state = reference.resolve(prefix)
        if {"B": row["B"], **reference.entry(prefix, state, reference.children(state))} != row:
            raise ValueError("ear independent final original-prefix reconstruction differs")
        if number % 1000 == 0:
            print(json.dumps({"closed_ear_final_original_prefixes_reconstructed": number,
                              "total": len(source["pending_states"])}), flush=True)
    result = accounting.partition_gate(parent, source, frontier, ledger, constants, proofs)
    accounting.current_gate(current, parent, result, layer)
    if (
        current["Rstar_conditional_frontier_families"] != frontier["families"]
        or accepted["ENTIRE_actual_source_prefixes_geometry_and_case_partition_replayed_here"][
            "family_conservation"] != result["independent_family_conservation"]
    ):
        raise ValueError("independent ear final exact family conservation differs")
    for name, digest in {**accepted["source_files"],
                         **{str(args.geometry/name): value for name, value in accepted["files"].items()}}.items():
        if normalized.get(str(local_path(name).resolve())) != digest:
            raise ValueError("ear current omitted or changed a real geometry dependency")
    for name, digest in manifest["copied_files"].items():
        if sha(args.geometry/name) != digest:
            raise ValueError("ear final frozen code/proof/ledger changed")
    pool_path = args.current_audit.with_name(args.current_audit.stem+"-closed-type-pool.json")
    receipt_path = args.current_audit.with_name(args.current_audit.stem+"-closed-receipt-checks.json")
    terminal_path = args.current_audit.with_name(args.current_audit.stem+"-terminal-obligations.json")
    for suffix, path in (
        ("-closed-type-pool.json", pool_path), ("-closed-receipt-checks.json", receipt_path),
        ("-terminal-obligations.json", terminal_path),
    ):
        bound_path(path)
        old = parent_path.with_name(parent_path.stem+suffix)
        if sha(path) != sha(old):
            raise ValueError("ear final changed an old historical proof/terminal sidecar")
    if (
        len(read(pool_path)) != 87 or len(read(receipt_path)) != 215
        or read(terminal_path) != parent["all_current_competitor_terminal_obligations_explicitly_retained"]
        or current["all_current_competitor_terminal_obligations_explicitly_retained"] != read(terminal_path)
        or current["current_candidate_type_paths"] != parent["current_candidate_type_paths"]
    ):
        raise ValueError("ear final lost a historical proof receipt or raw terminal obligation")
    bound_path(__file__)
    for module in (accounting, identity, force, sys.modules[OriginReference.__module__],
                   sys.modules[accounting.independent_patch.__module__]):
        bound_path(module.__file__)
    for path in (
        manifest_path, source_path, args.geometry/"VERIFIED.json", args.geometry_replay,
        semantic_path, args.geometry/"FRONTIER.json", args.geometry/"LOWER-LEDGER.json",
        args.geometry/"FAMILY-CONSTANTS.json",
        candidate_folder/"VERIFIED.json", candidate_folder/"PENDING-ANGLES.json",
    ):
        bound_path(path)
    if sha(args.current_audit) != initial or sha(parent_path) != parent_digest or sha(final_path) != final_digest:
        raise ValueError("ear final current or actual parent changed during independent semantics")
    report = {
        "schema": "N26-independent-closed-ear-source-current-final-rehash-v1",
        "all_current_file_digests_rehashed": True,
        "current_file_digests_rechecked": len(inventory), "current_audit_sha256": initial,
        "actual_own_publication_and_complete_current_semantic_reports_byte_identical": True,
        "independent_complete_original_source_prefix_reconstruction": len(source["pending_states"]),
        "independent_exact_closed_ear_source_accounting": result,
        "Rstar_conditional_frontier_pending_subtrees": len(frontier["pending_states"]),
        "Rstar_conditional_frontier_families": frontier["families"],
        "new_strict_whole_prefixes": len(ledger), "candidate_whole_roots_removed": 0,
        "candidate_angle_unresolved_closed_boxes": 25,
        "all_actual_latest_owned8_candidate_histories_and_raw_terminal_obligations_retained": True,
        "retained_closed_full_type_codes": 87, "retained_checked_proof_receipts": 215,
        "radius_scope": accounting.SCOPE, "r_strict_interval": current["r_strict_interval"],
        "original_U_frontier_nodes_removed": 0,
        "unrestricted_reduction_final_joint_acceptance": False,
        "full_catalog_complete": False, "global_lower_bound_proved": False,
        "global_optimality_proved": False, "n27_started": False,
        "executed_checker_sha256": sha(__file__),
        "executed_independent_accounting_sha256": sha(accounting.__file__),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({key: value for key, value in report.items()
                      if key not in ("Rstar_conditional_frontier_families",
                                     "independent_exact_closed_ear_source_accounting")}), flush=True)


if __name__ == "__main__":
    main()
