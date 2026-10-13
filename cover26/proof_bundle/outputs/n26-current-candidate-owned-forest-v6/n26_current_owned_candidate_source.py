"""Current root source with explicit per-root accepted forest history.

Unattempted current roots may start from one OPEN node. Previously attempted
roots must use their newest actually accepted incomplete forest, even when that
forest belongs to an older source layer. No earlier paid leaf can be reset.
"""

from fractions import Fraction as F
from pathlib import Path

from audit_prefix_partition import linux
import n26_current_seeded_candidate_source as older
import verify_conditional_force_stage as binding


read, sha, local_path = binding.read, binding.sha, binding.local_path
SCHEMA = "N26-accepted-current-owned-candidate-energy-LOCAL-forests-v1"
FOREST_SCHEMAS = {
    "N26-accepted-current-original-candidate-energy-LOCAL-forests-v1",
    "N26-accepted-current-candidate-energy-LOCAL-continuation-forests-v1",
    older.SEEDED_SCHEMA,
    SCHEMA,
}


def gate(folder, replay_path, audit_path, rehash_path):
    acceptance = read(folder / "VERIFIED.json")
    if acceptance["schema"] != SCHEMA:
        result = older.gate(folder, replay_path, audit_path, rehash_path)
        result[3].append(Path(__file__))
        return result
    import verify_owned_candidate_forests as checker

    current, rehash = read(audit_path), read(rehash_path)
    if (
        not current["current_bound_bytes_rechecked"]
        or not current["prior_completed_full_chain_semantic_replay_still_bound"]
        or current["radius_scope"] != binding.SCOPE
        or current["global_optimality_proved"] is not False
        or current["global_lower_bound_proved"] is not False
        or current["original_52_coordinate_local_allowance_unchanged"] != "7/800000"
        or rehash["current_audit_sha256"] != sha(audit_path)
        or rehash["all_current_file_digests_rehashed"] is not True
        or rehash["current_file_digests_rechecked"] != len(current["files"])
    ):
        raise ValueError("owned forest source lacks the actual current audit and final rehash")
    inventory = []
    for text, digest in current["files"].items():
        if sha(text) != digest:
            raise ValueError("owned forest current dependency changed: " + text)
        inventory.append(local_path(text))
    accepted, paths = binding.bound(folder)
    inventory.extend(paths)
    if (
        read(replay_path) != accepted
        or current["files"].get(linux(folder / "VERIFIED.json")) != sha(folder / "VERIFIED.json")
        or current["files"].get(linux(replay_path)) != sha(replay_path)
        or current["files"].get(linux(folder / "PENDING-ANGLES.json")) != sha(folder / "PENDING-ANGLES.json")
        or current.get("actual_current_candidate_acceptance") != linux(folder / "VERIFIED.json")
        or current.get("actual_current_candidate_pending_angles") != linux(folder / "PENDING-ANGLES.json")
        or sha(checker.__file__) != accepted["files"]["verify_owned_candidate_forests.py"]
    ):
        raise ValueError("owned forest source is not the actual current published candidate layer")
    values = checker.input_gate(folder)
    payments, pending, results, boxes, ledgers = checker.derive(values)
    positive = checker.base.source.tiny_control(values[3])
    expected = {
        "ROOT-PAYMENTS.json": payments, "PENDING-ANGLES.json": pending,
        "ROOT-CLASSIFICATION.json": results, "PENDING-FOREST-LEAVES.json": boxes,
        "LOWER-LEDGER.json": ledgers, "POSITIVE-CONTROLS.json": positive,
        "OWNERSHIP.json": checker.ownership(values),
    }
    if any(read(folder / name) != data for name, data in expected.items()):
        raise ValueError("owned forest source semantic outputs did not reconstruct")
    indices = [row["source_OPEN_index"] for row in payments]
    certificate = read(folder / "CERTIFICATE.json")
    if (
        accepted["source_actual_remaining_candidate_roots"] != len(values[4])
        or accepted["new_whole_candidate_source_roots_lower_bounded"] != len(payments)
        or accepted["unresolved_closed_angle_boxes"] != len(pending)
        or current["candidate_angle_unresolved_closed_boxes"] != len(pending)
        or rehash["candidate_angle_unresolved_closed_boxes"] != len(pending)
        or certificate["discharged_actual_source_root_indices"] != indices
        or len(set(indices)) != len(indices)
        or [row for row in values[4] if row["index"] not in indices] != pending
        or len(values[4]) != len(payments) + len(pending)
        or any(not row["source_candidate_root_fully_lower_bounded"] for row in payments)
        or any(row["source_candidate_root_strictly_empty"] and row["counts"]["LOCAL"] for row in payments)
        or positive["known_feasible_root_tiny_box_not_energy_excluded"] is not True
        or positive["original_LOCAL_leaf_and_52_coordinate_allowance_preserved"] is not True
    ):
        raise ValueError("owned forest source lost whole-root ownership or LOCAL equality feasibility")
    parent_path, proof_parent = local_path(values[0]["parent_current_audit"]), values[1]
    if (
        current["files"].get(linux(parent_path)) != sha(parent_path)
        or any(current["files"].get(text) != digest for text, digest in proof_parent["files"].items())
        or proof_parent["r_strict_interval"] != current["r_strict_interval"]
        or F(values[3][3]["radius"]) != F(current["r_strict_interval"][1])
        or F(accepted["radius_upper"]) != F(values[3][3]["radius"])
    ):
        raise ValueError("owned forest source lost its exact radius or identically bound proof-time ancestor")
    inventory.extend(values[-1])
    inventory.extend((audit_path, rehash_path, replay_path, Path(__file__)))
    return accepted, values[3], pending, inventory, payments


def history(folder, pending):
    """Newest accepted forest per still-current original whole-root index."""
    current = {row["index"]: row for row in pending}
    if len(current) != len(pending):
        raise ValueError("current owned source contains duplicate original root indices")
    result, inventory, visited = {}, [], set()
    while True:
        key = linux(folder)
        if key in visited:
            raise ValueError("accepted candidate forest history has a cycle")
        visited.add(key)
        accepted = read(folder / "VERIFIED.json")
        if accepted["schema"] not in FOREST_SCHEMAS:
            break
        _, paths = binding.bound(folder)
        inventory.extend(paths)
        proposal, classes = read(folder / "PROPOSAL.json"), read(folder / "ROOT-CLASSIFICATION.json")
        by_class = {row["source_OPEN_index"]: row for row in classes}
        if len(by_class) != len(classes):
            raise ValueError("accepted candidate history has duplicate root classifications")
        seen = set()
        for item in proposal["forests"]:
            index = item["source_OPEN_index"]
            if type(index) is not int or index in seen or index not in by_class:
                raise ValueError("accepted forest history lost exact root ownership")
            seen.add(index)
            if index not in current or index in result:
                continue
            row = current[index]
            if (
                item["actual_source_closed_box"] != row
                or by_class[index]["actual_source_closed_box"] != row
                or by_class[index]["source_candidate_root_fully_lower_bounded"] is not False
            ):
                raise ValueError("accepted incomplete forest was changed or a discharged root reopened")
            result[index] = {
                "source_OPEN_index": index, "actual_source_closed_box": row,
                "history_source": key, "history_acceptance_sha256": sha(folder / "VERIFIED.json"),
                "nodes": item["nodes"], "accepted_source_classification": by_class[index],
            }
        folder = local_path(read(folder / "MANIFEST.json")["source"])
    inventory.append(Path(__file__))
    return result, inventory
