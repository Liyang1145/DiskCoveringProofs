"""Identify the actual latest candidate layer through bound enumeration audits.

Equal remaining whole-root rows do not authorize replacing a newer partial
forest by an older source. Enumeration-only audits may omit candidate pointers;
their identically bound parent chain must lead to the actual candidate layer.
This is an ownership check, not a new geometric payment.
"""

from fractions import Fraction as F

from audit_prefix_partition import linux
import verify_conditional_force_stage as binding


ENUMERATION_SCHEMA = "N26-current-stage-catalogue-and-complete-historical-proof-pool-audit-v1"
CANDIDATE_SCHEMAS = {
    "N26-complete-current-chain-with-accepted-seed-candidate-refinement-audit-v1",
    "N26-complete-current-chain-with-per-root-owned-candidate-forests-audit-v1",
}
POINTERS = ("actual_current_candidate_acceptance", "actual_current_candidate_pending_angles")


def digest_gate(value):
    if not isinstance(value, str) or len(value) != 64 or any(
        char not in "0123456789abcdef" for char in value
    ):
        raise ValueError("latest candidate ancestry has an invalid digest")
    return value


def gate(current, current_sha256, source_folder, *, reader=None, hasher=None):
    reader = binding.read if reader is None else reader
    hasher = binding.sha if hasher is None else hasher
    inventory = current["files"]
    if not isinstance(inventory, dict):
        raise ValueError("latest candidate ancestry lacks an exact bound inventory")
    root_count = current["candidate_angle_unresolved_closed_boxes"]
    radius = current["r_strict_interval"]
    if type(root_count) is not int or root_count < 0:
        raise ValueError("latest candidate ancestry has an invalid whole-root count")
    report, digest = current, digest_gate(current_sha256)
    seen, ancestry = set(), []
    while True:
        if digest in seen:
            raise ValueError("latest candidate ancestry has a cycle")
        seen.add(digest)
        if (
            report["current_bound_bytes_rechecked"] is not True
            or report["prior_completed_full_chain_semantic_replay_still_bound"] is not True
            or report["radius_scope"] != binding.SCOPE
            or report["global_optimality_proved"] is not False
            or report["candidate_angle_unresolved_closed_boxes"] != root_count
            or report["r_strict_interval"] != radius
            or any(inventory.get(text) != value for text, value in report["files"].items())
        ):
            raise ValueError("latest candidate ancestor is not an unchanged bound current layer")
        present = [name in report for name in POINTERS]
        if any(present):
            if not all(present) or report["schema"] not in CANDIDATE_SCHEMAS:
                raise ValueError("latest candidate layer has incomplete or unsupported ownership pointers")
            break
        if report["schema"] != ENUMERATION_SCHEMA:
            raise ValueError("only explicitly enumeration-only audits may omit candidate ownership")
        prior_digest = digest_gate(report["prior_current_audit_sha256"])
        if prior_digest in seen:
            raise ValueError("latest candidate ancestry has a cycle")
        paths = sorted(text for text, value in inventory.items() if value == prior_digest)
        if not paths:
            raise ValueError("latest candidate parent is absent from the actual current inventory")
        parent_path = binding.local_path(paths[0])
        if hasher(parent_path) != prior_digest:
            raise ValueError("latest candidate parent bytes changed")
        report = reader(parent_path)
        ancestry.append({"bound_parent_path": paths[0], "sha256": prior_digest})
        digest = prior_digest

    source_folder = binding.local_path(source_folder)
    acceptance_path = source_folder / "VERIFIED.json"
    pending_path = source_folder / "PENDING-ANGLES.json"
    expected = (linux(acceptance_path), linux(pending_path))
    if tuple(report[name] for name in POINTERS) != expected:
        raise ValueError("candidate overlay would reset a newer actual candidate layer")
    acceptance_digest, pending_digest = hasher(acceptance_path), hasher(pending_path)
    if (
        inventory.get(expected[0]) != acceptance_digest
        or inventory.get(expected[1]) != pending_digest
        or report["files"].get(expected[0]) != acceptance_digest
        or report["files"].get(expected[1]) != pending_digest
    ):
        raise ValueError("latest actual candidate acceptance or whole-root rows are not bound")
    accepted, pending = reader(acceptance_path), reader(pending_path)
    if (
        accepted["verified"] is not True
        or accepted["radius_scope"] != "same-root-Rstar"
        or accepted["unresolved_closed_angle_boxes"] != root_count
        or F(accepted["radius_upper"]) != F(radius[1])
        or not isinstance(pending, list)
        or len(pending) != root_count
        or any(type(row["index"]) is not int for row in pending)
        or len({row["index"] for row in pending}) != len(pending)
    ):
        raise ValueError("latest candidate ownership, exact radius or whole-root accounting changed")
    return {
        "schema": "N26-bound-latest-candidate-layer-identity-v1",
        "actual_current_parent_sha256": current_sha256,
        "latest_candidate_current_audit_sha256": digest,
        "enumeration_only_bound_ancestors_followed": ancestry,
        "actual_latest_candidate_acceptance": expected[0],
        "actual_latest_candidate_acceptance_sha256": acceptance_digest,
        "actual_latest_candidate_pending_angles": expected[1],
        "actual_latest_candidate_pending_angles_sha256": pending_digest,
        "actual_remaining_candidate_whole_roots": root_count,
        "equal_whole_root_count_and_rows_are_not_a_source_identity_substitute": True,
        "new_geometric_candidate_payments": 0,
    }
