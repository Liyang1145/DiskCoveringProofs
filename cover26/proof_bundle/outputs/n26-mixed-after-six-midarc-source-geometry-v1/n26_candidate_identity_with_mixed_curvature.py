"""Explicit latest-layer identity for the new mixed-curvature current schema.

Old sealed identity helpers remain unchanged. This is not a geometry replay;
complete new-source reconstruction is required by the separate source adapter.
"""

from fractions import Fraction as F

from audit_prefix_partition import linux
import n26_current_candidate_layer_identity as original
import verify_conditional_force_stage as binding


CURRENT_SCHEMA = "N26-complete-current-chain-with-mixed-curvature-root-covers-audit-v1"
ACCEPTANCE_SCHEMA = "N26-accepted-current-mixed-curvature-LOCAL-root-covers-v1"
CHECKER = "verify_current_candidate_mixed_curvature_covers.py"


def gate(current, current_sha256, folder, *, reader=None, hasher=None):
    reader = binding.read if reader is None else reader
    hasher = binding.sha if hasher is None else hasher
    inventory = current["files"]
    count, radius = current["candidate_angle_unresolved_closed_boxes"], current["r_strict_interval"]
    if not isinstance(inventory, dict) or type(count) is not int or count < 0:
        raise ValueError("mixed latest-layer identity lacks a valid inventory/root count")
    report, digest = current, original.digest_gate(current_sha256)
    seen, ancestry = set(), []
    while True:
        if digest in seen:
            raise ValueError("mixed latest-layer identity ancestry has a cycle")
        seen.add(digest)
        if (report["current_bound_bytes_rechecked"] is not True
                or report["prior_completed_full_chain_semantic_replay_still_bound"] is not True
                or report["radius_scope"] != binding.SCOPE
                or report["global_optimality_proved"] is not False
                or report["candidate_angle_unresolved_closed_boxes"] != count
                or report["r_strict_interval"] != radius
                or any(inventory.get(text) != value for text, value in report["files"].items())):
            raise ValueError("mixed latest-layer ancestor changed bound bytes, scope or root count")
        pointers = [name in report for name in original.POINTERS]
        if any(pointers):
            if not all(pointers):
                raise ValueError("mixed latest-layer ancestor has partial ownership pointers")
            if report["schema"] in original.CANDIDATE_SCHEMAS:
                return original.gate(current, current_sha256, folder, reader=reader, hasher=hasher)
            if report["schema"] != CURRENT_SCHEMA:
                raise ValueError("unsupported new candidate ownership schema")
            if (report["mixed_curvature_actual_published_replay_matched_and_semantics_replayed_here"] is not True
                    or report["mixed_curvature_source_is_actual_latest_candidate_layer"] is not True
                    or report["all_newest_owned_histories_retained_identically"] is not True):
                raise ValueError("mixed current report omitted semantic admission or history preservation")
            break
        if report["schema"] != original.ENUMERATION_SCHEMA:
            raise ValueError("only explicit enumeration-only ancestors may omit candidate ownership")
        prior = original.digest_gate(report["prior_current_audit_sha256"])
        paths = sorted(text for text, value in inventory.items() if value == prior)
        if not paths:
            raise ValueError("mixed latest-layer parent is not in the bound actual inventory")
        path = binding.local_path(paths[0])
        if hasher(path) != prior:
            raise ValueError("mixed latest-layer parent bytes changed")
        ancestry.append({"bound_parent_path": paths[0], "sha256": prior})
        report, digest = reader(path), prior
    folder = binding.local_path(folder)
    paths = (folder / "VERIFIED.json", folder / "PENDING-ANGLES.json")
    expected = tuple(linux(path) for path in paths)
    if tuple(report[name] for name in original.POINTERS) != expected:
        raise ValueError("mixed candidate continuation would reset the actual latest candidate source")
    digests = tuple(hasher(path) for path in paths)
    if any(inventory.get(text) != value or report["files"].get(text) != value
           for text, value in zip(expected, digests)):
        raise ValueError("mixed actual candidate acceptance/root rows are not identically bound")
    accepted, pending = reader(paths[0]), reader(paths[1])
    checker_key = linux(folder / CHECKER)
    if (accepted["schema"] != ACCEPTANCE_SCHEMA or accepted["verified"] is not True
            or accepted["radius_scope"] != "same-root-Rstar"
            or accepted["unresolved_closed_angle_boxes"] != count
            or F(accepted["radius_upper"]) != F(radius[1])
            or accepted["executed_checker_file"] != CHECKER
            or accepted["executed_checker_sha256"] != accepted["files"][CHECKER]
            or hasher(folder / CHECKER) != accepted["executed_checker_sha256"]
            or inventory.get(checker_key) != accepted["executed_checker_sha256"]
            or report["files"].get(checker_key) != accepted["executed_checker_sha256"]
            or accepted["accepted_curvature_modes"] != ["constant-hull", "integrated-Taylor"]
            or len(accepted["negative_controls_rejected"]) != 29
            or accepted["original_full_latest_model_source_all_old_payments_and_history_replayed"] is not True
            or accepted["actual_newest_per_root_owned_forests_retained_identically"] is not True
            or not isinstance(pending, list) or len(pending) != count
            or any(type(row["index"]) is not int for row in pending)
            or len({row["index"] for row in pending}) != count):
        raise ValueError("mixed latest source changed executor, mode controls or exact root ownership")
    return {
        "schema": "N26-explicit-mixed-curvature-latest-candidate-layer-identity-v1",
        "actual_current_parent_sha256": current_sha256,
        "latest_candidate_current_audit_sha256": digest,
        "enumeration_only_bound_ancestors_followed": ancestry,
        "actual_latest_candidate_acceptance": expected[0],
        "actual_latest_candidate_acceptance_sha256": digests[0],
        "actual_latest_candidate_pending_angles": expected[1],
        "actual_latest_candidate_pending_angles_sha256": digests[1],
        "actual_remaining_candidate_whole_roots": count,
        "new_schema_not_relabelled_as_old_owned_source": True,
        "identity_only_not_a_model_or_geometry_replay": True,
        "new_geometric_candidate_payments": 0,
    }
