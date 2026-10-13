"""Fold the accepted candidate forest into its exact current 34-root source.

The curvature source gate is never given a forest bundle.  Its actual
curvature source is reconstructed by the forest's own sealed input gate,
then every complete forest and its retained whole-root ownership is replayed.
This loader grants no new geometric payment.
"""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import verify_candidate_energy_local_forests as accepted_forest
import verify_conditional_force_stage as binding


read, sha, local_path = binding.read, binding.sha, binding.local_path


def folded_outputs_gate(folder, acceptance, values, derived):
    payments, pending, results, boxes, ledgers = derived
    incoming = values[4]
    positive = accepted_forest.source.tiny_control(values[3])
    expected = {
        "ROOT-PAYMENTS.json": payments,
        "PENDING-ANGLES.json": pending,
        "ROOT-CLASSIFICATION.json": results,
        "PENDING-FOREST-LEAVES.json": boxes,
        "LOWER-LEDGER.json": ledgers,
        "POSITIVE-CONTROLS.json": positive,
    }
    if any(read(folder / name) != data for name, data in expected.items()):
        raise ValueError("accepted candidate forest outputs did not semantically fold")
    paid_indices = [row["source_OPEN_index"] for row in payments]
    certificate = read(folder / "CERTIFICATE.json")
    if (
        acceptance["schema"] != "N26-accepted-current-original-candidate-energy-LOCAL-forests-v1"
        or not acceptance["verified"]
        or acceptance["radius_scope"] != "same-root-Rstar"
        or acceptance["source_actual_remaining_candidate_roots"] != len(incoming)
        or acceptance["new_whole_candidate_source_roots_lower_bounded"] != len(payments)
        or acceptance["unresolved_closed_angle_boxes"] != len(pending)
        or len(incoming) != len(payments) + len(pending)
        or certificate["discharged_actual_source_root_indices"] != paid_indices
        or certificate["LOCAL_lower_bound_is_not_an_emptiness_claim"] is not True
        or certificate["all_unattempted_or_incompletely_proved_source_roots_retained"] is not True
        or len(set(paid_indices)) != len(paid_indices)
        or any(row["index"] in paid_indices for row in pending)
        or [row for row in incoming if row["index"] not in paid_indices] != pending
        or any(not row["source_candidate_root_fully_lower_bounded"] for row in payments)
        or any(row["source_candidate_root_strictly_empty"] and row["counts"]["LOCAL"] for row in payments)
    ):
        raise ValueError("accepted forest root accounting lost or reopened a paid whole root")
    return positive


def gate(folder, replay_path, current_audit_path, digest_recheck_path):
    current, rehash = read(current_audit_path), read(digest_recheck_path)
    if (
        not current["current_bound_bytes_rechecked"]
        or not current["prior_completed_full_chain_semantic_replay_still_bound"]
        or current["radius_scope"] != binding.SCOPE
        or current["global_optimality_proved"] is not False
        or current["global_lower_bound_proved"] is not False
        or current["original_52_coordinate_local_allowance_unchanged"] != "7/800000"
        or rehash["current_audit_sha256"] != sha(current_audit_path)
        or rehash["all_current_file_digests_rehashed"] is not True
        or rehash["current_file_digests_rechecked"] != len(current["files"])
    ):
        raise ValueError("candidate continuation lacks the fully audited current chain and final rehash")
    print("Checking the current inventory before folding accepted candidate forests.", flush=True)
    inventory = []
    for text, digest in current["files"].items():
        if sha(text) != digest:
            raise ValueError("current candidate continuation dependency changed: " + text)
        inventory.append(local_path(text))
    acceptance, paths = binding.bound(folder)
    inventory.extend(paths)
    if (
        read(replay_path) != acceptance
        or current["files"].get(linux(folder / "VERIFIED.json")) != sha(folder / "VERIFIED.json")
        or current["files"].get(linux(replay_path)) != sha(replay_path)
        or current["files"].get(linux(folder / "PENDING-ANGLES.json")) != sha(folder / "PENDING-ANGLES.json")
        or sha(accepted_forest.__file__) != acceptance["files"]["verify_candidate_energy_local_forests.py"]
    ):
        raise ValueError("continuation source is not the actual bound published candidate forest")
    print("Reconstructing curvature payments and every accepted complete candidate forest.", flush=True)
    values = accepted_forest.input_gate(folder)
    derived = accepted_forest.derive(values)
    positive = folded_outputs_gate(folder, acceptance, values, derived)
    proof_parent, original_values = values[1], values[3]
    parent_path = local_path(values[0]["parent_current_audit"])
    if (
        current["files"].get(linux(parent_path)) != sha(parent_path)
        or any(current["files"].get(text) != digest for text, digest in proof_parent["files"].items())
        or proof_parent["r_strict_interval"] != current["r_strict_interval"]
        or F(original_values[3]["radius"]) != F(current["r_strict_interval"][1])
        or F(acceptance["radius_upper"]) != F(original_values[3]["radius"])
        or len(derived[1]) != current["candidate_angle_unresolved_closed_boxes"]
        or rehash["candidate_angle_unresolved_closed_boxes"] != len(derived[1])
        or acceptance["original_92_rod_kernel_and_52_coordinate_frame_preserved"] is not True
        or acceptance["known_exact_candidate_tiny_box_retained_in_proved_LOCAL_leaf"] is not True
        or positive["known_feasible_root_tiny_box_not_energy_excluded"] is not True
        or positive["original_LOCAL_leaf_and_52_coordinate_allowance_preserved"] is not True
    ):
        raise ValueError("folded forest lost its identical current ancestry, root radius or original frame")
    inventory.extend(values[-1])
    inventory.extend((current_audit_path, digest_recheck_path, replay_path, Path(__file__)))
    return acceptance, original_values, derived[1], inventory, derived[0]


def main():
    parser = argparse.ArgumentParser()
    for name in ("source", "source-replay", "current-audit", "current-digest-recheck", "report"):
        parser.add_argument("--" + name, type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    acceptance, values, pending, inventory, paid = gate(
        args.source, args.source_replay, args.current_audit, args.current_digest_recheck
    )
    report = {
        "schema": "N26-semantically-folded-accepted-candidate-forest-source-v1",
        "source_gate_passed": True,
        "current_audit_sha256": sha(args.current_audit),
        "actual_accepted_forest_sha256": sha(args.source / "VERIFIED.json"),
        "actual_accepted_forest_replay_sha256": sha(args.source_replay),
        "source_actual_candidate_roots": acceptance["source_actual_remaining_candidate_roots"],
        "already_paid_complete_source_indices": [row["source_OPEN_index"] for row in paid],
        "actual_remaining_candidate_roots": len(pending),
        "actual_remaining_candidate_indices": [row["index"] for row in pending],
        "actual_remaining_candidate_rows_sha256": sha(args.source / "PENDING-ANGLES.json"),
        "original_52_coordinate_local_allowance_unchanged": "7/800000",
        "original_92_rod_kernel_and_same_root_preserved": True,
        "r_strict_interval": read(args.current_audit)["r_strict_interval"],
        "new_candidate_roots_paid_by_this_source_loader": 0,
        "global_lower_bound_proved": False,
        "global_optimality_proved": False,
        "files": {linux(path): sha(path) for path in inventory},
        "executed_checker_sha256": sha(__file__),
    }
    args.report.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: val for key, val in report.items() if key != "files"}, indent=2), flush=True)


if __name__ == "__main__":
    main()
