"""Explicit newest signed/grown forest identity; old dispatchers stay unchanged."""

from fractions import Fraction as F

from audit_prefix_partition import linux
import n26_candidate_identity_with_product_forests as prior
import n26_latest_signed_full134_current_accounting as accounting
import verify_conditional_force_stage as binding


CURRENT_SCHEMA = accounting.CURRENT_SCHEMA
ACCEPTANCE_SCHEMA = "N26-accepted-latest-signed-grown-full134rod-partial-forests-v1"
CHECKER = "verify_latest_candidate_signed_full134rod_forests.py"
MODES = ["latest-root25-extended-signed", "latest-root28-grown-full134rod"]
POINTERS = prior.prior.original.POINTERS


def gate(current, current_sha256, folder, *, reader=None, hasher=None):
    reader = binding.read if reader is None else reader
    hasher = binding.sha if hasher is None else hasher
    digest_gate = prior.prior.original.digest_gate
    inventory, count, radius = (
        current["files"], current["candidate_angle_unresolved_closed_boxes"], current["r_strict_interval"])
    if not isinstance(inventory, dict) or type(count) is not int or count < 0:
        raise ValueError("latest signed forest identity lacks exact inventory or integer root count")
    report, digest, seen, ancestry = current, digest_gate(current_sha256), set(), []
    while True:
        if digest in seen:
            raise ValueError("latest signed forest identity ancestry has a cycle")
        seen.add(digest)
        if (report["current_bound_bytes_rechecked"] is not True
                or report["prior_completed_full_chain_semantic_replay_still_bound"] is not True
                or report["radius_scope"] != binding.SCOPE
                or report["global_lower_bound_proved"] is not False
                or report["global_optimality_proved"] is not False
                or report["candidate_angle_unresolved_closed_boxes"] != count
                or report["r_strict_interval"] != radius
                or any(inventory.get(text) != value for text, value in report["files"].items())):
            raise ValueError("latest signed forest ancestor changed bound bytes, exact roots or radius")
        present = [name in report for name in POINTERS]
        if any(present):
            if not all(present):
                raise ValueError("latest signed forest ownership pointers are incomplete")
            if report["schema"] != CURRENT_SCHEMA:
                return prior.gate(current, current_sha256, folder, reader=reader, hasher=hasher)
            if (report["latest_forest_actual_published_replay_matched_and_semantics_replayed_here"] is not True
                    or report["latest_forest_source_is_actual_latest_candidate_layer"] is not True
                    or report["all_newest_owned_histories_retained_identically"] is not True):
                raise ValueError("latest forest current omitted actual semantic replay or newest history")
            break
        if report["schema"] != prior.prior.original.ENUMERATION_SCHEMA:
            raise ValueError("only explicit enumeration ancestry can omit candidate ownership")
        previous = digest_gate(report["prior_current_audit_sha256"])
        paths = sorted(text for text, value in inventory.items() if value == previous)
        if not paths:
            raise ValueError("latest signed forest parent is absent from actual bound inventory")
        path = binding.local_path(paths[0])
        if hasher(path) != previous:
            raise ValueError("latest signed forest parent bytes changed")
        ancestry.append({"bound_parent_path": paths[0], "sha256": previous})
        report, digest = reader(path), previous
    folder = binding.local_path(folder)
    acceptance_path, pending_path = folder / "VERIFIED.json", folder / "PENDING-ANGLES.json"
    history_path, checker_path = folder / "REMAINING-ROOT-HISTORY.json", folder / CHECKER
    expected = (linux(acceptance_path), linux(pending_path))
    if (tuple(report[name] for name in POINTERS) != expected
            or report["actual_current_candidate_remaining_history"] != linux(history_path)):
        raise ValueError("latest signed forest overlay would reset or clip the actual newest source")
    digests = tuple(hasher(path) for path in (acceptance_path, pending_path, history_path, checker_path))
    for path, value in zip((acceptance_path, pending_path, history_path, checker_path), digests):
        if inventory.get(linux(path)) != value or report["files"].get(linux(path)) != value:
            raise ValueError("latest signed forest source/history/executor is not identically bound")
    accepted, pending, history = reader(acceptance_path), reader(pending_path), reader(history_path)
    pending_owners = accounting.owners(pending, "index")
    history_owners = accounting.owners(history, "source_OPEN_index")
    if (accepted["schema"] != ACCEPTANCE_SCHEMA or accepted["verified"] is not True
            or accepted["radius_scope"] != "same-root-Rstar"
            or accepted["unresolved_closed_angle_boxes"] != count or len(pending) != count
            or F(accepted["radius_upper"]) != F(radius[1])
            or accepted["executed_checker_file"] != CHECKER
            or accepted["executed_checker_sha256"] != digests[3]
            or accepted["files"][CHECKER] != digests[3]
            or accepted["files"]["REMAINING-ROOT-HISTORY.json"] != digests[2]
            or accepted["accepted_forest_modes"] != MODES
            or len(accepted["negative_controls_rejected"]) != 21
            or accepted["actual_latest_root25_v3_and_root28_grown_v9_replayed_not_reset"] is not True
            or accepted["actual_old_baselines_and_every_strict_ledger_freshly_reconstructed"] is not True
            or accepted["actual_full_source_replay"][
                "ENTIRE_actual_source_model_old_payments_and_latest_history_replayed_here"] is not True
            or accepted["source_identity_and_arithmetic_controls_NOT_used_as_geometry_substitutes"] is not True
            or accepted["remaining_root_partial_histories_retained"] != len(history)
            or not set(history_owners) <= set(pending_owners)
            or any(row["actual_source_closed_box"] != pending_owners[index]
                   for index, row in history_owners.items())
            or accepted["global_lower_bound_proved"] is not False
            or accepted["global_optimality_proved"] is not False):
        raise ValueError("latest signed forest identity lacks actual own geometry,mode controls or exact history")
    return {
        "schema": "N26-explicit-latest-signed-grown-full134rod-candidate-layer-identity-v1",
        "actual_current_parent_sha256": current_sha256,
        "latest_candidate_current_audit_sha256": digest,
        "enumeration_only_bound_ancestors_followed": ancestry,
        "actual_latest_candidate_acceptance": expected[0],
        "actual_latest_candidate_acceptance_sha256": digests[0],
        "actual_latest_candidate_pending_angles": expected[1],
        "actual_latest_candidate_pending_angles_sha256": digests[1],
        "actual_latest_candidate_remaining_history": linux(history_path),
        "actual_latest_candidate_remaining_history_sha256": digests[2],
        "actual_remaining_candidate_whole_roots": count,
        "new_extended_forest_schema_not_relabelled_as_old_owned_mixed_or_product": True,
        "identity_only_NOT_entire_source_model_history_or_geometry_replay": True,
        "new_geometric_candidate_payments": 0,
    }
