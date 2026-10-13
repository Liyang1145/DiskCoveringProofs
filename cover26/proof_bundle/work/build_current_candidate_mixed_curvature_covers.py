"""Seal a fresh two-mode supplemental root-cover bundle, without admission."""

import argparse
import json
from pathlib import Path

from audit_prefix_partition import linux
import verify_conditional_force_stage as binding
import verify_current_candidate_mixed_curvature_covers as verifier


def main():
    parser = argparse.ArgumentParser()
    for name in (
        "source", "source-replay", "parent-current-audit", "parent-digest-recheck",
        "constant-diagnosis", "constant-arithmetic-controls",
        "integral-diagnosis", "integral-arithmetic-controls",
        "interface-guard-controls", "output",
    ):
        parser.add_argument("--" + name, type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    # Refuse an absent/incomplete parent before any costly historical rehash.
    parent, rehash = binding.read(args.parent_current_audit), binding.read(args.parent_digest_recheck)
    parent_digest = binding.sha(args.parent_current_audit)
    if (rehash["current_audit_sha256"] != parent_digest
            or rehash["all_current_file_digests_rehashed"] is not True
            or rehash["current_file_digests_rechecked"] != len(parent["files"])
            or rehash["candidate_angle_unresolved_closed_boxes"]
            != parent["candidate_angle_unresolved_closed_boxes"]
            or parent.get("actual_current_candidate_acceptance")
            != linux(args.source / "VERIFIED.json")
            or parent.get("actual_current_candidate_pending_angles")
            != linux(args.source / "PENDING-ANGLES.json")):
        raise ValueError("mixed builder needs the actual completed explicit owned parent/final pair")
    verifier.constant.identity.gate(parent, parent_digest, args.source)
    accepted, _ = binding.bound(args.source)
    if (accepted["schema"] != verifier.constant.owned.SCHEMA
            or binding.read(args.source_replay) != accepted):
        raise ValueError("mixed builder changed the actual owned source acceptance/replay")
    incoming = binding.read(args.source / "PENDING-ANGLES.json")
    first, second = binding.read(args.constant_diagnosis), binding.read(args.integral_diagnosis)
    if (first["schema"] not in verifier.constant.DIAGNOSES
            or second["schema"] != verifier.INTEGRAL_DIAGNOSIS
            or any(row["verified"] is not False or row["new_geometric_payments"] != 0
                   for row in (first, second))):
        raise ValueError("mixed builder changed unaccepted discovery scope")
    roots = verifier.selected_covers(first, second)
    verifier.modes_gate(roots)
    verifier.constant.root_gate(incoming, roots)
    guard = binding.read(args.interface_guard_controls)
    if (guard["tested_own_acceptance_executor_sha256"] != binding.sha(verifier.__file__)
            or guard["tested_integral_backend_sha256"] != binding.sha(verifier.integral.__file__)
            or guard["metadata_guard_controls_passed"] is not True
            or guard["verified"] is not False
            or guard["new_geometric_payments"] != 0
            or guard["complete_latest_model_source_history_gate_NOT_executed"] is not True):
        raise ValueError("mixed builder lacks actual guarded two-mode interface tests")
    history, _ = verifier.constant.owned.history(args.source, incoming)
    args.output.mkdir(parents=True)
    copies = [(args.source / name, name)
              for name in accepted["files"] if name.endswith(".py")]
    copies.extend((
        (args.source / "VERIFIED.json", "SOURCE-ACCEPTANCE.json"),
        (args.source / "PENDING-ANGLES.json", "SOURCE-PENDING-ANGLES.json"),
        (args.parent_current_audit, "SOURCE-CURRENT-AUDIT.json"),
        (args.parent_digest_recheck, "SOURCE-FINAL-DIGEST-RECHECK.json"),
        (args.constant_diagnosis, "CONSTANT-DIAGNOSIS.json"),
        (args.integral_diagnosis, "INTEGRAL-DIAGNOSIS.json"),
        (args.constant_arithmetic_controls, "CONSTANT-ARITHMETIC-CONTROLS.json"),
        (args.integral_arithmetic_controls, "INTEGRAL-ARITHMETIC-CONTROLS.json"),
        (args.interface_guard_controls, "INTERFACE-GUARD-CONTROLS.json"),
    ))
    for name in (
        "verify_current_candidate_mixed_curvature_covers.py",
        "build_current_candidate_mixed_curvature_covers.py",
        "verify_current_candidate_signed_hull_covers.py",
        "n26_current_candidate_layer_identity.py",
        "n26_signed_hull_local_cover.py", "n26_signed_hull_energy_minorant.py",
        "n26_integrated_hull_curvature.py", "n26_integrated_hull_local_cover.py",
        "test_signed_hull_local_cover_arithmetic.py",
        "test_integrated_hull_cover_arithmetic.py",
        "test_mixed_candidate_curvature_cover_interface.py",
        "n26-signed-hull-energy-minorant-proof.md",
        "n26-integrated-hull-curvature-proof.md",
        "n26-mixed-curvature-supplemental-acceptance-proof.md",
    ):
        copies.append((Path(__file__).with_name(name), name))
    for original, name in copies:
        target = args.output / name
        if target.exists():
            if target.read_bytes() != original.read_bytes():
                raise ValueError("mixed builder collided different frozen files under one name")
        else:
            target.write_bytes(original.read_bytes())
    for name, data in (
        ("COVERS.json", roots),
        ("SOURCE-ROOT-HISTORY.json", [history[index] for index in sorted(history)]),
    ):
        with (args.output / name).open("x", encoding="utf-8", newline="\n") as output:
            output.write(json.dumps(data, indent=2) + "\n")
    manifest = {
        "schema": verifier.INPUT_SCHEMA, "radius_scope": "same-root-Rstar",
        "source": linux(args.source), "source_replay": linux(args.source_replay),
        "source_acceptance_sha256": binding.sha(args.source / "VERIFIED.json"),
        "parent_current_audit": linux(args.parent_current_audit),
        "parent_current_audit_sha256": parent_digest,
        "parent_digest_recheck": linux(args.parent_digest_recheck),
        "parent_digest_recheck_sha256": binding.sha(args.parent_digest_recheck),
        "acceptance_checker_file": verifier.CHECKER,
        "supported_curvature_modes": verifier.MODES,
        "typed_resource_not_a_source_replay_substitute": True,
        "supplemental_cover_never_replaces_accepted_forest": True,
        "discovery_used_only_for_certificates_actual_latest_whole_root_rows_matched": True,
        "copied_files": {name: binding.sha(args.output / name) for name in dict.fromkeys(
            [name for _, name in copies] + ["COVERS.json", "SOURCE-ROOT-HISTORY.json"])},
        "executed_builder_sha256": binding.sha(__file__),
        "verified": False, "global_optimality_proved": False,
    }
    with (args.output / "MANIFEST.json").open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(manifest, indent=2) + "\n")
    print(json.dumps({
        "built": True, "verified": False, "supplemental_root_covers": len(roots),
        "supported_curvature_modes": verifier.MODES,
        "new_geometric_payments": 0,
        "actual_complete_latest_source_model_history_and_own_acceptance_still_required": True}),
        flush=True)


if __name__ == "__main__":
    main()
