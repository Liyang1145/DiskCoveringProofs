"""Independent real complete-current final for the six-target source supplement."""

import argparse
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import sys

from audit_prefix_origin import OriginReference
import n26_force as force
import n26_current_candidate_layer_identity as identity
import n26_six_target_current_accounting as accounting


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
        raise FileExistsError("independent six-target final never overwrites an existing report")
    initial = sha(args.current_audit)
    current = read(args.current_audit)
    if current["schema"] != accounting.CURRENT_SCHEMA:
        raise ValueError("six-target final cannot certify an old native-stage/643-only current")
    inventory = current["files"]
    normalized = {str(local_path(text).resolve()): digest for text, digest in inventory.items()}
    if len(normalized) != len(inventory):
        raise ValueError("six-target current inventory has duplicate normalized dependency identities")
    def bound(path):
        if normalized.get(str(local_path(path).resolve())) != sha(path):
            raise ValueError("six-target independent final has an unbound or changed input: "+str(path))
    for number, (text, digest) in enumerate(inventory.items(), 1):
        if sha(text) != digest:
            raise ValueError("six-target complete-current bound bytes changed: "+text)
        if number % 10000 == 0:
            print(json.dumps({"six_target_final_inventory_rehashed": number, "total": len(inventory)}), flush=True)
    parent_path = local_path(current["six_target_parent_audit_file"])
    final_path = local_path(current["six_target_parent_final_file"])
    bound(parent_path)
    bound(final_path)
    parent, parent_final = read(parent_path), read(final_path)
    parent_digest, final_digest = sha(parent_path), sha(final_path)
    if (
        parent_digest != current["prior_current_audit_sha256"]
        or final_digest != current["six_target_parent_final_sha256"]
        or parent_final["current_audit_sha256"] != parent_digest
        or parent_final["all_current_file_digests_rehashed"] is not True
        or parent_final["current_file_digests_rechecked"] != len(parent["files"])
    ):
        raise ValueError("six-target independent final lost the actual completed parent/current pair")
    if (
        local_path(current["six_target_geometry_folder"]).resolve() != args.geometry.resolve()
        or local_path(current["six_target_geometry_publication_file"]).resolve() != args.geometry_replay.resolve()
        or local_path(current["current_frontier_actual_file"]).resolve() != (args.geometry/"FRONTIER.json").resolve()
    ):
        raise ValueError("six-target final was given a different actual geometry/frontier/publication")
    manifest = read(args.geometry/"MANIFEST.json")
    source_path = local_path(manifest["source_frontier"])
    if (
        manifest["parent_current_sha256"] != parent_digest or manifest["parent_final_sha256"] != final_digest
        or local_path(manifest["parent_current"]).resolve() != parent_path.resolve()
        or local_path(manifest["parent_final"]).resolve() != final_path.resolve()
        or sha(source_path) != manifest["source_frontier_sha256"]
        or read(source_path) != read(args.geometry/"SOURCE-FRONTIER.json")
    ):
        raise ValueError("six-target independent final substituted original source or proof-time parent")
    source, frontier = read(source_path), read(args.geometry/"FRONTIER.json")
    ledger, constants = read(args.geometry/"LOWER-LEDGER.json"), read(args.geometry/"FAMILY-CONSTANTS.json")
    proofs = {key: sha(args.geometry/name) for key, name in {
        "cap": "UNIT-CAP-PROOF.md", "generic": "GENERIC-SLACK-PROOF.md",
        "bridge": "EMBEDDED-CORNER-SHADOW-BRIDGE-PROOF.md", "ear": "CLOSED-EAR-PROOF.md",
        "six": "SIX-CORE-TARGET-FILLED-EAR-PROOF.md",
    }.items()}
    candidate_folder = local_path(manifest["actual_candidate_source"])
    layer = identity.gate(parent, parent_digest, candidate_folder, reader=read, hasher=sha)
    accepted = read(args.geometry/"VERIFIED.json")
    semantic_path = local_path(current["six_target_geometry_semantic_replay_file"])
    accounting.receipt_gate(
        parent, parent_digest, final_digest, accepted, read(args.geometry_replay),
        read(semantic_path), sha(args.geometry/accounting.CHECKER), layer)
    expected_command = [
        sys.executable, str(args.geometry/accounting.CHECKER), "--input", str(args.geometry),
        "--report", str(semantic_path),
    ]
    actual_command = current["six_target_full_current_semantic_command"]
    if (
        sha(args.geometry/"VERIFIED.json") != sha(args.geometry_replay)
        or sha(args.geometry/"VERIFIED.json") != sha(semantic_path)
        or accepted["actual_source_frontier_sha256"] != sha(source_path)
        or len(actual_command) != len(expected_command)
        or [str(local_path(actual_command[i]).resolve()) for i in (0, 1, 3, 5)]
            != [str(local_path(expected_command[i]).resolve()) for i in (0, 1, 3, 5)]
        or actual_command[2] != "--input" or actual_command[4] != "--report"
    ):
        raise ValueError("six-target independent final lacks the actual identical report triple/full-main command")
    references = {b: OriginReference(26, b, "dfs", caps=force.CAPS, scale=force.D)
                  for b in (14, 15, 16, 17)}
    for reference in references.values():
        reference.children = lru_cache(None)(reference.children)
    for number, row in enumerate(source["pending_states"], 1):
        reference = references[row["B"]]
        prefix = tuple(row["prefix"])
        state = reference.resolve(prefix)
        if {"B": row["B"], **reference.entry(prefix, state, reference.children(state))} != row:
            raise ValueError("six-target independent final ENTIRE original-prefix reconstruction differs")
        if number % 1000 == 0:
            print(json.dumps({"six_target_final_original_prefixes_reconstructed": number,
                              "total": len(source["pending_states"])}), flush=True)
    result = accounting.partition_gate(parent, source, frontier, ledger, constants, proofs)
    accounting.current_gate(current, parent, result, layer)
    if accepted["ENTIRE_actual_source_prefixes_six_target_geometry_and_case_partition_replayed_here"][
        "family_conservation"] != result["independent_family_conservation"]:
        raise ValueError("independent six-target family conservation differs from actual geometry")
    for text, digest in accepted["source_files"].items():
        if normalized.get(str(local_path(text).resolve())) != digest:
            raise ValueError("six-target current omitted or changed a whole-geometry source dependency")
    for name, digest in accepted["files"].items():
        if normalized.get(str((args.geometry/name).resolve())) != digest:
            raise ValueError("six-target current omitted a real frozen code/proof/ledger input")
    for suffix in ("-closed-type-pool.json", "-closed-receipt-checks.json", "-terminal-obligations.json"):
        path = args.current_audit.with_name(args.current_audit.stem+suffix)
        original = parent_path.with_name(parent_path.stem+suffix)
        bound(path)
        if sha(path) != sha(original):
            raise ValueError("six-target final changed an original proof receipt or raw terminal sidecar")
    pool = read(args.current_audit.with_name(args.current_audit.stem+"-closed-type-pool.json"))
    receipts = read(args.current_audit.with_name(args.current_audit.stem+"-closed-receipt-checks.json"))
    obligations = read(args.current_audit.with_name(args.current_audit.stem+"-terminal-obligations.json"))
    if (
        len(pool) != 87 or len(receipts) != 215
        or obligations != parent["all_current_competitor_terminal_obligations_explicitly_retained"]
        or obligations != current["all_current_competitor_terminal_obligations_explicitly_retained"]
    ):
        raise ValueError("six-target final lost an original closed type, receipt or competitor obligation")
    bound(__file__)
    work = Path(__file__).resolve().parent
    for module in list(sys.modules.values()):
        text = getattr(module, "__file__", None)
        if text:
            path = Path(text).resolve()
            if path.suffix == ".py" and path.parent == work:
                bound(path)
    for name in accepted["files"]:
        bound(args.geometry/name)
    for path in (
        source_path, semantic_path, args.geometry/"VERIFIED.json", args.geometry_replay,
        candidate_folder/"VERIFIED.json", candidate_folder/"PENDING-ANGLES.json",
    ):
        bound(path)
    if sha(args.current_audit) != initial or sha(parent_path) != parent_digest or sha(final_path) != final_digest:
        raise ValueError("six-target independent final current/parent changed during exact semantics")
    report = {
        "schema": "N26-independent-six-target-source-current-final-rehash-v1",
        "all_current_file_digests_rehashed": True, "current_file_digests_rechecked": len(inventory),
        "current_audit_sha256": initial,
        "actual_own_publication_AND_complete_current_semantic_reports_byte_identical": True,
        "independent_complete_original_source_prefix_reconstruction": len(source["pending_states"]),
        "independent_exact_six_target_source_accounting": result,
        "Rstar_conditional_frontier_pending_subtrees": len(frontier["pending_states"]),
        "Rstar_conditional_frontier_families": frontier["families"],
        "new_strict_whole_prefixes": len(ledger), "candidate_whole_roots_removed": 0,
        "candidate_angle_unresolved_closed_boxes": 25,
        "all_actual_latest_owned8_histories_and_raw_terminal_obligations_retained": True,
        "retained_closed_full_type_codes": 87, "retained_checked_proof_receipts": 215,
        "radius_scope": accounting.SCOPE, "r_strict_interval": current["r_strict_interval"],
        "original_U_frontier_nodes_removed": 0, "unrestricted_reduction_final_joint_acceptance": False,
        "full_catalog_complete": False, "global_lower_bound_proved": False,
        "global_optimality_proved": False, "n27_started": False,
        "executed_checker_sha256": sha(__file__),
        "executed_independent_accounting_sha256": sha(accounting.__file__),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({key: value for key, value in report.items()
                      if key not in ("Rstar_conditional_frontier_families",
                                     "independent_exact_six_target_source_accounting")}), flush=True)


if __name__ == "__main__":
    main()
