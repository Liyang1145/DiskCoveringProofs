"""Distinct REAL complete-current admission of actual remaining680 midarc geometry."""

import argparse
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import subprocess
import sys

from audit_prefix_partition import linux
import audit_stage_catalogue_with_closed_pool as historical
import n26_force as force  # Explicitly bind the independent final's original-prefix runtime.
import n26_candidate_identity_after_midarc as identity
import n26_midarc_current_accounting as accounting
import verify_conditional_force_stage as binding


def main():
    parser = argparse.ArgumentParser()
    for name in ("parent-audit", "parent-final", "geometry", "geometry-replay",
                 "regression", "narrative", "output"):
        parser.add_argument("--" + name, type=Path, required=True)
    args = parser.parse_args()
    semantic_path = args.output.with_name(args.output.stem + "-geometry-semantic-replay.json")
    suffixes = ("-closed-type-pool.json", "-closed-receipt-checks.json", "-terminal-obligations.json")
    if any(path.exists() for path in [
        args.output, semantic_path, *(args.output.with_name(args.output.stem + suffix) for suffix in suffixes),
    ]):
        raise FileExistsError("midarc current never resets completed/final/partial targets")
    parent_digest, final_digest = binding.sha(args.parent_audit), binding.sha(args.parent_final)
    parent, final = binding.read(args.parent_audit), binding.read(args.parent_final)
    accounting.source.parent_gate(parent, final, parent_digest)
    final_executor = Path(__file__).with_name("recheck_mixed_curvature_candidate_after_six_current.py")
    if (
        final["executed_checker_sha256"] != binding.sha(final_executor)
        or parent["files"].get(linux(final_executor)) != binding.sha(final_executor)
    ):
        raise ValueError("midarc current lacks its actual bound completed mixed16-root final executor")
    manifest = binding.read(args.geometry / "MANIFEST.json")
    if (
        manifest["parent_current_sha256"] != parent_digest
        or manifest["parent_final_sha256"] != final_digest
        or binding.local_path(manifest["parent_current"]).resolve() != args.parent_audit.resolve()
        or binding.local_path(manifest["parent_final"]).resolve() != args.parent_final.resolve()
    ):
        raise ValueError("midarc own geometry belongs to another proof-time parent; never reset a newer current")
    candidate = binding.local_path(manifest["actual_candidate_source"])
    layer = identity.previous.gate(parent, parent_digest, candidate)
    accepted = binding.read(args.geometry / "VERIFIED.json")
    checker = args.geometry / accounting.CHECKER
    accounting.receipt_gate(
        parent, parent_digest, final_digest, accepted, binding.read(args.geometry_replay),
        accepted, binding.sha(checker), layer,
    )
    if binding.sha(args.geometry / "VERIFIED.json") != binding.sha(args.geometry_replay):
        raise ValueError("midarc actual own and same-main publication are not byte-identical")
    source = binding.read(args.geometry / "SOURCE-FRONTIER.json")
    frontier = binding.read(args.geometry / "FRONTIER.json")
    ledger = binding.read(args.geometry / "LOWER-LEDGER.json")
    constants = binding.read(args.geometry / "FAMILY-CONSTANTS.json")
    proof_names = {
        "cap": "UNIT-CAP-PROOF.md", "generic": "GENERIC-SLACK-PROOF.md",
        "bridge": "EMBEDDED-CORNER-SHADOW-BRIDGE-PROOF.md", "ear": "CLOSED-EAR-PROOF.md",
        "midarc": "MIDARC-SEVEN-SIX-FIVE-TARGET-PROOF.md",
    }
    proofs = {key: binding.sha(args.geometry / name) for key, name in proof_names.items()}
    result = accounting.source.partition_gate(source, frontier, ledger, constants, proofs)
    if result != accepted["independent_complete_actual_remaining_source_accounting"]:
        raise ValueError("midarc own geometry differs from fresh independent remaining-source accounting")
    regression = binding.read(args.regression)
    snapshot = regression["synthetic_actual_mixed_geometry_source_identity_snapshot_NOT_formal_parent"]
    if (
        regression["schema"] != "N26-midarc-current-synthetic-identity-and-accounting-controls-v1"
        or regression["verified"] is not False or regression["new_formal_geometric_payments"] != 0
        or regression["all_parent_current_final_and_geometry_receipt_headers_explicitly_SYNTHETIC"] is not True
        or regression["tested_identity_module_sha256"] != binding.sha(identity.__file__)
        or regression["tested_accounting_module_sha256"] != binding.sha(accounting.__file__)
        or regression["executed_test_sha256"] != binding.sha(
            Path(__file__).with_name("test_midarc_current_identity_and_accounting.py"))
        or regression["actual_independent_remaining_source_partition"] != result
        or len(regression["invalid_candidate_ancestry_controls_rejected"]) != 20
        or len(regression["synthetic_invalid_geometry_receipt_controls_rejected"]) != 15
        or len(regression["synthetic_invalid_current_scope_controls_rejected"]) != 11
        or any(snapshot[key] != layer[key] for key in (
            "actual_latest_candidate_acceptance", "actual_latest_candidate_acceptance_sha256",
            "actual_latest_candidate_pending_angles", "actual_latest_candidate_pending_angles_sha256",
            "actual_remaining_candidate_whole_roots",
        ))
    ):
        raise ValueError("midarc current lacks actual-source controls of its distinct interface")
    executors = [
        Path(__file__), Path(__file__).with_name("recheck_midarc_source_current.py"),
        Path(__file__).with_name("test_midarc_current_identity_and_accounting.py"),
        Path(__file__).with_name("run_midarc_source_serial_current_final_v1.ps1"),
        Path(__file__).with_name("run_midarc_current_after_live_source_pair_v1.ps1"),
        args.narrative, args.regression,
    ]
    work = Path(__file__).resolve().parent
    for module in list(sys.modules.values()):
        text = getattr(module, "__file__", None)
        if text:
            path = Path(text).resolve()
            if path.suffix == ".py" and path.parent == work:
                executors.append(path)
    executors = sorted({path.resolve() for path in executors})
    executor_digests = {linux(path): binding.sha(path) for path in executors}
    command = [
        sys.executable, str(checker), "--input", str(args.geometry), "--report", str(semantic_path),
    ]
    print("Executing the ENTIRE frozen NEW midarc main for REAL complete-current geometry semantics.",
          flush=True)
    completed = subprocess.run(command, check=False)
    if completed.returncode:
        raise ValueError("actual midarc current geometry main failed; preserve partial evidence")
    accounting.receipt_gate(
        parent, parent_digest, final_digest, accepted, binding.read(args.geometry_replay),
        binding.read(semantic_path), binding.sha(checker), layer,
    )
    if (
        binding.sha(semantic_path) != binding.sha(args.geometry / "VERIFIED.json")
        or binding.sha(args.parent_audit) != parent_digest
        or binding.sha(args.parent_final) != final_digest
        or binding.read(args.geometry / "MANIFEST.json") != manifest
    ):
        raise ValueError("midarc actual full-current geometry replay or proof-time parent changed")
    result = accounting.source.partition_gate(
        binding.read(args.geometry / "SOURCE-FRONTIER.json"),
        binding.read(args.geometry / "FRONTIER.json"),
        binding.read(args.geometry / "LOWER-LEDGER.json"),
        binding.read(args.geometry / "FAMILY-CONSTANTS.json"), proofs,
    )
    old_sidecars = [args.parent_audit.with_name(args.parent_audit.stem + suffix) for suffix in suffixes]
    for path in old_sidecars:
        if parent["files"].get(linux(path)) != binding.sha(path):
            raise ValueError("midarc current lost old closed types, proof receipts or raw terminal ownership")
    pool = binding.read(old_sidecars[0])
    receipts = historical.retained_pool_gate(pool, parent, F(parent["r_strict_interval"][1]))
    if receipts != binding.read(old_sidecars[1]) or len(pool) != 87 or len(receipts) != 215:
        raise ValueError("midarc current changed original type/receipt closure")
    inventory = dict(accepted["source_files"])
    paths = [
        args.parent_audit, args.parent_final, args.geometry / "VERIFIED.json",
        args.geometry_replay, semantic_path, *executors,
        *(args.geometry / name for name in accepted["files"]),
    ]
    for suffix, original in zip(suffixes, old_sidecars):
        target = args.output.with_name(args.output.stem + suffix)
        with target.open("xb") as output:
            output.write(original.read_bytes())
        paths.append(target)
    for path in paths:
        text, digest = linux(path), binding.sha(path)
        if text in inventory and inventory[text] != digest:
            raise ValueError("midarc old and new accepted inventories disagree")
        inventory[text] = digest
    normalized = {str(binding.local_path(text).resolve()): value for text, value in inventory.items()}
    if len(normalized) != len(inventory):
        raise ValueError("midarc current has duplicate normalized dependency identities")
    print("Rehashing EVERY merged midarc current dependency after actual full semantics.", flush=True)
    for number, (text, digest) in enumerate(inventory.items(), 1):
        if binding.sha(text) != digest:
            raise ValueError("midarc merged current dependency changed: " + text)
        if number % 10000 == 0:
            print(json.dumps({
                "midarc_current_inventory_rehashed": number, "total": len(inventory),
            }), flush=True)
    if (
        any(binding.sha(text) != value for text, value in executor_digests.items())
        or binding.sha(args.parent_audit) != parent_digest
        or binding.sha(args.parent_final) != final_digest
        or binding.read(args.geometry / "FRONTIER.json") != frontier
        or identity.previous.gate(parent, parent_digest, candidate) != layer
    ):
        raise ValueError("midarc actual executor, parent, frontier or latest candidate source changed")
    report = {
        key: value for key, value in parent.items()
        if key != "files" and key not in identity.POINTERS
    }
    report.update({
        "schema": accounting.CURRENT_SCHEMA, "current_bound_bytes_rechecked": True,
        "prior_completed_full_chain_semantic_replay_still_bound": True,
        "prior_current_audit_sha256": parent_digest,
        "prior_current_file_digests_rechecked": len(parent["files"]),
        "midarc_parent_audit_file": linux(args.parent_audit),
        "midarc_parent_final_file": linux(args.parent_final),
        "midarc_parent_final_sha256": final_digest,
        "midarc_geometry_folder": linux(args.geometry),
        "midarc_geometry_publication_file": linux(args.geometry_replay),
        "midarc_geometry_semantic_replay_file": linux(semantic_path),
        "midarc_actual_own_publication_and_current_semantic_reports_equal": True,
        "midarc_full_current_semantic_command": command,
        "midarc_full_current_semantic_exit_code": completed.returncode,
        "midarc_independent_exact_source_accounting": result,
        "midarc_actual_prior_candidate_layer_identity": layer,
        "candidate_layer_and_all_latest_partial_histories_unchanged_by_midarc_rule": True,
        "midarc_candidate_whole_roots_removed": 0,
        "midarc_source_conditional_pending_subtrees": 5637,
        "midarc_new_strict_whole_source_prefixes": len(ledger),
        "Rstar_conditional_frontier_pending_subtrees": len(frontier["pending_states"]),
        "Rstar_conditional_frontier_families": frontier["families"],
        "current_frontier_actual_file": linux(args.geometry / "FRONTIER.json"),
        "inherited_mixed_candidate_admission_fields_are_historical_NOT_new_candidate_payments": True,
        "all_siblings_unresolved_terminals_OPEN_boundaries_and_old_proofs_retained": True,
        "midarc_current_admission_executor_file": linux(Path(__file__)),
        "midarc_current_admission_executor_sha256": executor_digests[linux(Path(__file__))],
        "midarc_identity_adapter_file": linux(Path(identity.__file__)),
        "midarc_identity_adapter_sha256": executor_digests[linux(Path(identity.__file__))],
        "midarc_current_controls_file": linux(args.regression),
        "midarc_independent_final_STILL_required_before_formal_head_adoption": True,
        "unrestricted_reduction_final_joint_acceptance": False,
        "full_catalog_complete": False, "global_lower_bound_proved": False,
        "global_optimality_proved": False, "n27_started": False, "files": inventory,
    })
    accounting.current_gate(report, parent, result, layer)
    payload = (json.dumps(report, indent=2) + "\n").encode("utf-8")
    future_digest = hashlib.sha256(payload).hexdigest()
    result_layer = identity.gate(report, future_digest, candidate)
    if result_layer["actual_remaining_candidate_whole_roots"] != 16:
        raise ValueError("midarc new enumeration interface lost the actual16-root source")
    with args.output.open("xb") as target:
        target.write(payload)
    print(json.dumps({
        "actual_midarc_complete_current_admission_passed": True,
        "proposed_frontier": 4957, "NEW_strict_whole_prefixes": 680,
        "candidate_whole_roots_RETAINED": 16, "independent_final_STILL_required": True,
        "global_optimality_proved": False,
    }), flush=True)


if __name__ == "__main__":
    main()
