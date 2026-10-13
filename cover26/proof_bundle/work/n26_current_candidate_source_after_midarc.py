"""Full model/history source through explicit NEW midarc enumeration ancestry.

Old mixed/owned dispatchers are not patched. Identity alone does not replace
the complete original model/forest/mixed-cover replay below. The new branch
requires a REAL completed midarc current/final pair, not unit header fixtures.
"""

from fractions import Fraction as F
from pathlib import Path

from audit_prefix_partition import linux
import n26_candidate_identity_after_midarc as identity
import n26_current_mixed_curvature_candidate_source as previous
import n26_midarc_current_accounting as current_accounting
import verify_conditional_force_stage as binding
import verify_current_candidate_mixed_curvature_covers as checker


def gate(folder, replay_path, audit_path, rehash_path):
    folder = binding.local_path(folder)
    current, final = binding.read(audit_path), binding.read(rehash_path)
    if current["schema"] != identity.CURRENT_SCHEMA:
        return previous.gate(folder, replay_path, audit_path, rehash_path)
    digest = binding.sha(audit_path)
    if (
        final["schema"] != current_accounting.FINAL_SCHEMA
        or final["current_audit_sha256"] != digest
        or final["all_current_file_digests_rehashed"] is not True
        or final["current_file_digests_rechecked"] != len(current["files"])
        or final["candidate_angle_unresolved_closed_boxes"] != 16
        or final["Rstar_conditional_frontier_pending_subtrees"] != 4957
        or final["all_actual16_candidate_roots_histories_and_raw_terminal_obligations_retained"] is not True
        or current["original_52_coordinate_local_allowance_unchanged"] != "7/800000"
        or final["original_LOCAL_unchanged"] != "7/800000"
        or current["radius_scope"] != binding.SCOPE
        or any(record[field] is not False for record in (current, final) for field in (
            "full_catalog_complete", "global_lower_bound_proved", "global_optimality_proved", "n27_started"))
    ):
        raise ValueError("midarc candidate source requires actual completed4957/16 current/final scope")
    final_executor = Path(__file__).with_name("recheck_midarc_source_current.py")
    if (
        final["executed_checker_sha256"] != binding.sha(final_executor)
        or current["files"].get(linux(final_executor)) != binding.sha(final_executor)
    ):
        raise ValueError("midarc candidate source lacks actual bound independent final executor")
    layer = identity.gate(current, digest, folder)
    inventory = []
    for number, (text, value) in enumerate(current["files"].items(), 1):
        if binding.sha(text) != value:
            raise ValueError("midarc current candidate source dependency changed: " + text)
        inventory.append(binding.local_path(text))
        if number % 10000 == 0:
            print({"midarc_candidate_source_content_rehashed": number,
                   "total": len(current["files"])}, flush=True)
    accepted, paths = binding.bound(folder)
    inventory.extend(paths)
    if (
        accepted["schema"] != checker.SCHEMA
        or binding.read(replay_path) != accepted
        or current["files"].get(linux(replay_path)) != binding.sha(replay_path)
        or binding.sha(checker.__file__) != accepted["executed_checker_sha256"]
    ):
        raise ValueError("midarc candidate source changed actual original mixed checker/publication")
    # ENTIRE original source/model/history gate and all actual mode controls.
    values = checker.input_gate(folder)
    payments, remaining, classified, retained = checker.derive(values)
    positive, negative = checker.controls(values)
    expected = {
        "ROOT-PAYMENTS.json": payments, "PENDING-ANGLES.json": remaining,
        "ROOT-CLASSIFICATION.json": classified, "REMAINING-ROOT-HISTORY.json": retained,
        "POSITIVE-CONTROLS.json": positive,
    }
    if any(binding.read(folder / name) != result for name, result in expected.items()):
        raise ValueError("midarc candidate full original model/covers/latest histories did not reconstruct")
    certificate = binding.read(folder / "CERTIFICATE.json")
    indices = [row["source_OPEN_index"] for row in payments]
    incoming = values[4]
    if (
        negative != accepted["negative_controls_rejected"]
        or certificate["discharged_actual_source_root_indices"] != indices
        or len(set(indices)) != len(indices)
        or [row for row in incoming if row["index"] not in indices] != remaining
        or len(payments) + len(remaining) != len(incoming)
        or len(incoming) != accepted["source_actual_remaining_candidate_roots"]
        or len(payments) != accepted["new_whole_candidate_source_roots_lower_bounded"]
        or len(remaining) != accepted["unresolved_closed_angle_boxes"] or len(remaining) != 16
        or len(retained) != accepted["remaining_root_partial_histories_retained"]
        or any(row["source_candidate_root_strictly_empty"] for row in payments)
        or F(values[3][3]["radius"]) != F(current["r_strict_interval"][1])
    ):
        raise ValueError("midarc candidate source lost actual roots, original LOCAL equality or exact radius")
    history = {row["source_OPEN_index"]: row for row in retained}
    if len(history) != len(retained):
        raise ValueError("midarc candidate source duplicated a newest per-root history")
    proof_path = binding.local_path(values[0]["parent_current_audit"])
    proof_parent = values[1]
    if (
        current["files"].get(linux(proof_path)) != binding.sha(proof_path)
        or any(current["files"].get(text) != value for text, value in proof_parent["files"].items())
        or proof_parent["r_strict_interval"] != current["r_strict_interval"]
    ):
        raise ValueError("midarc candidate source lost its actual bound original full-model proof-time ancestor")
    inventory.extend(values[7])
    inventory.extend((
        audit_path, rehash_path, replay_path, Path(__file__), Path(identity.__file__),
        Path(current_accounting.__file__),
    ))
    if binding.sha(audit_path) != digest:
        raise ValueError("actual midarc current source changed during complete model/history replay")
    return accepted, values[3], remaining, inventory, payments, history, layer
