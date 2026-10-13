"""Complete source reconstruction for an explicitly admitted product candidate."""

from fractions import Fraction as F
from pathlib import Path

from audit_prefix_partition import linux
import n26_candidate_identity_with_product_forests as identity
import verify_conditional_force_stage as binding
import verify_current_candidate_product_forests as checker


def gate(folder, replay_path, audit_path, rehash_path):
    current_digest = binding.sha(audit_path)
    current, rehash = binding.read(audit_path), binding.read(rehash_path)
    if (rehash["current_audit_sha256"] != current_digest
            or rehash["all_current_file_digests_rehashed"] is not True
            or rehash["current_file_digests_rechecked"] != len(current["files"])
            or rehash["candidate_angle_unresolved_closed_boxes"]
            != current["candidate_angle_unresolved_closed_boxes"]
            or current["original_52_coordinate_local_allowance_unchanged"] != "7/800000"):
        raise ValueError("product source requires actual completed current/final pair")
    layer = identity.gate(current, current_digest, folder)
    inventory = []
    for text, digest in current["files"].items():
        if binding.sha(text) != digest:
            raise ValueError("product actual current dependency changed: "+text)
        inventory.append(binding.local_path(text))
    accepted, paths = binding.bound(folder)
    inventory.extend(paths)
    if (accepted["schema"] != checker.SCHEMA
            or binding.read(replay_path) != accepted
            or current["files"].get(linux(replay_path)) != binding.sha(replay_path)
            or binding.sha(checker.__file__) != accepted["executed_checker_sha256"]):
        raise ValueError("product source lacks actual own-executor acceptance/publication replay")
    values = checker.input_gate(folder)
    payments, remaining, classified, ledgers, retained = checker.derive(values)
    positive, negative = checker.controls(values)
    expected = {
        "ROOT-PAYMENTS.json": payments, "PENDING-ANGLES.json": remaining,
        "ROOT-CLASSIFICATION.json": classified, "LOWER-LEDGER.json": ledgers,
        "REMAINING-ROOT-HISTORY.json": retained, "POSITIVE-CONTROLS.json": positive,
    }
    if any(binding.read(folder / name) != data for name, data in expected.items()):
        raise ValueError("product source model, old modes, new forest or remaining histories failed reconstruction")
    certificate = binding.read(folder / "CERTIFICATE.json")
    indices = [row["source_OPEN_index"] for row in payments]
    incoming = values[4]
    if (negative != accepted["negative_controls_rejected"]
            or certificate["discharged_actual_source_root_indices"] != indices
            or len(set(indices)) != len(indices)
            or [row for row in incoming if row["index"] not in indices] != remaining
            or len(payments)+len(remaining) != len(incoming)
            or len(incoming) != accepted["source_actual_remaining_candidate_roots"]
            or len(payments) != accepted["new_whole_candidate_source_roots_lower_bounded"]
            or len(remaining) != accepted["unresolved_closed_angle_boxes"]
            or len(remaining) != current["candidate_angle_unresolved_closed_boxes"]
            or len(retained) != accepted["remaining_root_partial_histories_retained"]
            or any(row["source_candidate_root_strictly_empty"] for row in payments)
            or F(values[3][3]["radius"]) != F(current["r_strict_interval"][1])):
        raise ValueError("product source lost whole roots, original LOCAL equality or exact radius")
    history = {row["source_OPEN_index"]: row for row in retained}
    if len(history) != len(retained):
        raise ValueError("product source contains duplicate newest remaining histories")
    proof_path = binding.local_path(values[0]["parent_current_audit"])
    proof_parent = values[1]
    if (current["files"].get(linux(proof_path)) != binding.sha(proof_path)
            or any(current["files"].get(text) != digest for text, digest in proof_parent["files"].items())
            or proof_parent["r_strict_interval"] != current["r_strict_interval"]):
        raise ValueError("product source lost its identically retained completed mixed ancestor")
    inventory.extend(values[7])
    inventory.extend((audit_path, rehash_path, replay_path, Path(__file__), Path(identity.__file__)))
    if binding.sha(audit_path) != current_digest:
        raise ValueError("product current snapshot changed during full source reconstruction")
    return accepted, values[3], remaining, inventory, payments, history, layer
