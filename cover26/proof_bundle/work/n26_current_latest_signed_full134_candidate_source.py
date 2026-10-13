"""Complete adopted extended-forest source, not an identity or DATA cache.

The SAME frozen geometry main runs as a separate process. Its original model
is then rebuilt in memory and all latest forests are independently rederived.
No older source dispatcher or live frozen geometry code is changed.
"""

from fractions import Fraction as F
from pathlib import Path
import subprocess
import sys

from audit_prefix_partition import linux
import n26_candidate_identity_with_latest_signed_forests as identity
import n26_latest_signed_full134_current_accounting as accounting
import n26_latest_candidate_complete_source_replay as prior_source
import recheck_latest_signed_full134_candidate_current as independent_final
import verify_conditional_force_stage as binding
import verify_latest_candidate_signed_full134rod_forests as checker


SCHEMA = "N26-complete-adopted-latest-signed-grown-full134rod-source-replay-v1"


def receipt_gate(owner, owner_final, owner_digest, accepted, publication, semantic, checker_digest):
    """Receipt association ONLY; no model or geometry replay."""
    prior_source.pair_gate(owner, owner_final, owner_digest)
    independent_final.acceptance_gate(owner, accepted, publication, semantic, checker_digest)
    if (owner_final["schema"] != "N26-independent-latest-signed-grown-full134rod-current-final-rehash-v1"
            or owner_final["actual_own_geometry_publication_and_current_semantic_replays_equal"] is not True
            or owner_final["candidate_angle_unresolved_closed_boxes"]
            != accepted["unresolved_closed_angle_boxes"]
            or owner_final["remaining_latest_partial_root_histories"]
            != accepted["remaining_root_partial_histories_retained"]
            or owner_final["independent_exact_root_and_newest_history_accounting"][
                "exact_source_root_partition_and_all_latest_histories_checked"] is not True):
        raise ValueError("extended source needs actual completed latest-current AND independent final")
    return {
        "receipt_association_ONLY_not_complete_source_model_history_replay": True,
        "new_geometric_payments": 0,
    }


def gate(folder, replay_path, formal_path, formal_final_path, owner_path, owner_final_path,
         *, semantic_report_path):
    """Fresh full source/forest replay; require a new explicit real report target."""
    folder, replay_path, formal_path, formal_final_path, owner_path, owner_final_path, semantic_report_path = (
        binding.local_path(path) for path in
        (folder, replay_path, formal_path, formal_final_path,
         owner_path, owner_final_path, semantic_report_path))
    if semantic_report_path.exists() or not semantic_report_path.parent.is_dir():
        raise FileExistsError("preserve source semantic evidence;provide an explicit existing parent/fresh report")
    self_digest, identity_digest, checker_digest = (
        binding.sha(__file__), binding.sha(identity.__file__), binding.sha(checker.__file__))
    formal_digest, owner_digest = binding.sha(formal_path), binding.sha(owner_path)
    formal, formal_final = binding.read(formal_path), binding.read(formal_final_path)
    owner, owner_final = binding.read(owner_path), binding.read(owner_final_path)
    prior_source.pair_gate(formal, formal_final, formal_digest)
    layer = identity.gate(formal, formal_digest, folder)
    owner_layer = identity.gate(owner, owner_digest, folder)
    if (layer["latest_candidate_current_audit_sha256"] != owner_digest
            or owner_layer["latest_candidate_current_audit_sha256"] != owner_digest
            or formal["r_strict_interval"] != owner["r_strict_interval"]
            or formal["candidate_angle_unresolved_closed_boxes"] != owner["candidate_angle_unresolved_closed_boxes"]
            or any(formal["files"].get(text) != digest for text, digest in owner["files"].items())):
        raise ValueError("extended source owner is not the genuinely latest identically bound current layer")
    if formal_path.resolve() != owner_path.resolve():
        for path in (owner_path, owner_final_path):
            if formal["files"].get(linux(path)) != binding.sha(path):
                raise ValueError("extended candidate-owner current/final ancestor is unbound")
    elif formal_final_path.resolve() != owner_final_path.resolve():
        raise ValueError("same extended owner supplied with a different final snapshot")
    accepted, inventory = binding.bound(folder)
    checker_path = folder / checker.CHECKER
    semantic_current_path = binding.local_path(owner["latest_forest_semantic_replay_file"])
    receipt_gate(
        owner, owner_final, owner_digest, accepted, binding.read(replay_path),
        binding.read(semantic_current_path), binding.sha(checker_path))
    if (binding.sha(checker_path) != checker_digest
            or formal["files"].get(linux(replay_path)) != binding.sha(replay_path)
            or owner["files"].get(linux(replay_path)) != binding.sha(replay_path)
            or formal["files"].get(linux(semantic_current_path)) != binding.sha(semantic_current_path)):
        raise ValueError("extended source actual frozen checker/publication/current semantic receipts changed")
    for number, (text, digest) in enumerate(formal["files"].items(), 1):
        if binding.sha(text) != digest:
            raise ValueError("extended source formal dependency changed: "+text)
        inventory.append(binding.local_path(text))
        if number % 10000 == 0:
            print({"extended_source_formal_dependencies_rehashed": number,
                   "total": len(formal["files"])}, flush=True)
    manifest = binding.read(folder / "MANIFEST.json")
    manifest_digest = binding.sha(folder / "MANIFEST.json")
    # Isolate the frozen executor's original import universe. Do not bypass
    # its metadata/import gates or add caller modules to an old frozen file.
    command = [sys.executable, str(checker_path), "--input", str(folder),
               "--report", str(semantic_report_path)]
    print("Executing SAME frozen ENTIRE extended source/model/history/forest geometry main.", flush=True)
    executed = subprocess.run(command, check=False)
    if executed.returncode:
        raise ValueError("extended actual full source geometry failed;preserve partial semantic evidence")
    if binding.read(semantic_report_path) != accepted:
        raise ValueError("extended source actual SAME-main semantic report differs from own acceptance")
    prior_paths = tuple(binding.local_path(manifest[name]) for name in (
        "source", "source_replay", "formal_current", "formal_final",
        "candidate_owner_current", "candidate_owner_final"))
    for path in (prior_paths[0] / "VERIFIED.json", prior_paths[1], *prior_paths[2:]):
        if formal["files"].get(linux(path)) != binding.sha(path):
            raise ValueError("extended original full source/proof-time pair is not an identically bound ancestor")
    # A successful report does NOT deserialize a model. Actually reconstruct
    # the complete prior geometry model/source/all old payments/history now.
    prior_accepted, original_values, incoming, paths, old_payments, old_history, prior_layer = prior_source.gate(
        *prior_paths)
    if (prior_accepted != binding.read(folder / "SOURCE-ACCEPTANCE.json")
            or incoming != binding.read(folder / "SOURCE-PENDING-ANGLES.json")
            or [old_history[index] for index in sorted(old_history)]
            != binding.read(folder / "SOURCE-ROOT-HISTORY.json")):
        raise ValueError("extended source cannot reconstruct its actual original source/model/history")
    records = {index: binding.read(folder / checker.RECORDS[index][0]) for index in (25, 28)}
    controls = {index: binding.read(folder / checker.RECORDS[index][1]) for index in (25, 28)}
    seeds = {index: binding.read(folder / checker.RECORDS[index][2]) for index in (25, 28)}
    frozen = manifest["copied_files"]
    digests = {name: frozen[name] for name in (
        *(name for names in checker.RECORDS.values() for name in names), "ROOT28-V8-CONTROLS.json")}
    retained_counts = checker.records_gate(records, controls, seeds, digests, frozen, incoming)
    values = (manifest, records, controls, seeds, retained_counts, prior_accepted, original_values,
              incoming, paths, old_payments, old_history, prior_layer)
    payments, remaining, classified, ledgers, retained = checker.derive(values)
    positive, negatives = checker.controls(values)
    expected = {
        "ROOT-PAYMENTS.json": payments, "PENDING-ANGLES.json": remaining,
        "ROOT-CLASSIFICATION.json": classified, "LOWER-LEDGER.json": ledgers,
        "REMAINING-ROOT-HISTORY.json": retained, "POSITIVE-CONTROLS.json": positive,
    }
    if any(binding.read(folder / name) != data for name, data in expected.items()):
        raise ValueError("extended ENTIRE latest geometry/ledger/history outputs did not freshly reconstruct")
    if (negatives != accepted["negative_controls_rejected"]
            or len(remaining) != formal["candidate_angle_unresolved_closed_boxes"]
            or F(original_values[3]["radius"]) != F(formal["r_strict_interval"][1])):
        raise ValueError("extended actual control replay/radius/current root ownership changed")
    exact_accounting = accounting.gate(
        owner, accepted, incoming, [old_history[index] for index in sorted(old_history)],
        records, seeds, classified, payments, remaining, retained, ledgers)
    history = accounting.owners(retained, "source_OPEN_index")
    certificate = binding.read(folder / "CERTIFICATE.json")
    if certificate["discharged_actual_source_root_indices"] != [
            row["source_OPEN_index"] for row in payments]:
        raise ValueError("extended actual source certificate names different whole-root payments")
    inventory.extend(paths)
    inventory.extend((replay_path, semantic_current_path, semantic_report_path, formal_path,
                      formal_final_path, owner_path, owner_final_path, Path(__file__),
                      Path(identity.__file__), Path(accounting.__file__), Path(independent_final.__file__)))
    # Revalidate actual ORIGINAL dependencies,not just a fresh digest of
    # potentially changed data. This never turns receipt identity into geometry.
    binding.bound(folder)
    for text, digest in formal["files"].items():
        if binding.sha(text) != digest:
            raise ValueError("extended source dependency changed during full semantic reconstruction")
    if (binding.sha(formal_path) != formal_digest or binding.sha(owner_path) != owner_digest
            or binding.sha(folder / "MANIFEST.json") != manifest_digest
            or binding.read(folder / "MANIFEST.json") != manifest
            or binding.sha(__file__) != self_digest
            or binding.sha(identity.__file__) != identity_digest
            or binding.sha(checker.__file__) != checker_digest):
        raise ValueError("extended source actual snapshots or executed source adapter changed")
    return (
        accepted, original_values, remaining, inventory, payments, history,
        {"schema": SCHEMA, "actual_latest_candidate_identity": layer,
         "actual_entire_frozen_source_geometry_command": command,
         "actual_entire_frozen_source_geometry_exit_code": executed.returncode,
         "actual_entire_source_geometry_semantic_report": linux(semantic_report_path),
         "original_geometry_model_AND_all_latest_forests_freshly_reconstructed_in_memory": True,
         "all_actual_old_payments_and_newest_history_retained": True,
         "independent_exact_latest_root_history_accounting": exact_accounting,
         "receipt_identity_NOT_used_as_model_or_geometry_substitute": True,
         "new_geometric_payments_by_source_adapter": 0,
         "global_lower_bound_proved": False, "global_optimality_proved": False},
    )
