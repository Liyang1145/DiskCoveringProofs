"""Seal a fresh supplemental root-cover bundle; perform no geometry payment."""

import argparse
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_current_candidate_layer_identity as identity
import n26_current_owned_candidate_source as owned
import verify_conditional_force_stage as binding
import verify_current_candidate_signed_hull_covers as verifier


def main():
    parser = argparse.ArgumentParser()
    for name in ("source", "source-replay", "parent-current-audit", "parent-digest-recheck",
                 "diagnosis", "arithmetic-controls", "output"):
        parser.add_argument("--" + name, type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    accepted, _ = binding.bound(args.source)
    parent, rehash = binding.read(args.parent_current_audit), binding.read(args.parent_digest_recheck)
    parent_digest = binding.sha(args.parent_current_audit)
    if (accepted["schema"] != owned.SCHEMA
            or binding.read(args.source_replay) != accepted
            or rehash["current_audit_sha256"] != parent_digest
            or rehash["all_current_file_digests_rehashed"] is not True
            or rehash["current_file_digests_rechecked"] != len(parent["files"])
            or rehash["candidate_angle_unresolved_closed_boxes"]
            != parent["candidate_angle_unresolved_closed_boxes"]):
        raise ValueError("supplemental cover builder needs the actual completed owned parent/final pair")
    identity.gate(parent, parent_digest, args.source)
    # The unchanged owned source gate requires its proof-time candidate audit,
    # not an enumeration-only descendant missing candidate ownership pointers.
    if (parent.get("actual_current_candidate_acceptance")
            != linux(args.source / "VERIFIED.json")
            or parent.get("actual_current_candidate_pending_angles")
            != linux(args.source / "PENDING-ANGLES.json")):
        raise ValueError("supplemental builder requires the explicit completed owned-candidate audit")
    incoming = binding.read(args.source / "PENDING-ANGLES.json")
    history, _ = owned.history(args.source, incoming)
    diagnosis = binding.read(args.diagnosis)
    regression = binding.read(args.arithmetic_controls)
    if (diagnosis["schema"] not in verifier.DIAGNOSES
            or diagnosis["verified"] is not False
            or diagnosis["new_geometric_payments"] != 0
            or diagnosis["current_candidate_whole_roots_removed"] != 0
            or regression["diagnosis_sha256"] != binding.sha(args.diagnosis)
            or regression["all_arithmetic_cover_reconstructions_passed"] is not True
            or regression["new_geometric_payments"] != 0):
        raise ValueError("supplemental builder changed zero-payment discovery/control scope")
    roots = [row for row in diagnosis["roots"] if row["all_arithmetic_cover_obligations_passed"]]
    verifier.root_gate(incoming, roots)
    args.output.mkdir(parents=True)
    copies = [(args.source / name, name)
              for name in accepted["files"] if name.endswith(".py")]
    copies.extend((
        (args.source / "VERIFIED.json", "SOURCE-ACCEPTANCE.json"),
        (args.source / "PENDING-ANGLES.json", "SOURCE-PENDING-ANGLES.json"),
        (args.parent_current_audit, "SOURCE-CURRENT-AUDIT.json"),
        (args.parent_digest_recheck, "SOURCE-FINAL-DIGEST-RECHECK.json"),
        (args.diagnosis, "DIAGNOSIS.json"),
        (args.arithmetic_controls, "ARITHMETIC-COVER-CONTROLS.json"),
    ))
    for name in (
        "verify_current_candidate_signed_hull_covers.py",
        "build_current_candidate_signed_hull_covers.py",
        "n26_current_candidate_layer_identity.py",
        "n26_signed_hull_local_cover.py", "n26_signed_hull_energy_minorant.py",
        "test_signed_hull_local_cover_arithmetic.py",
        "test_signed_hull_energy_arithmetic.py",
        "n26-signed-hull-energy-minorant-proof.md",
        "n26-signed-hull-supplemental-acceptance-proof.md",
    ):
        copies.append((Path(__file__).with_name(name), name))
    for original, name in copies:
        target = args.output / name
        if target.exists():
            if target.read_bytes() != original.read_bytes():
                raise ValueError("supplemental bundle copied two different modules under one name")
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
        "typed_resource_not_a_source_replay_substitute": True,
        "supplemental_cover_never_replaces_accepted_forest": True,
        "discovery_used_for_certificates_only_actual_latest_full_root_rows_matched": True,
        "copied_files": {name: binding.sha(args.output / name) for name in dict.fromkeys(
            [name for _, name in copies] + ["COVERS.json", "SOURCE-ROOT-HISTORY.json"])},
        "executed_builder_sha256": binding.sha(__file__),
        "verified": False, "global_optimality_proved": False,
    }
    with (args.output / "MANIFEST.json").open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(manifest, indent=2) + "\n")
    print(json.dumps({
        "built": True, "verified": False, "supplemental_root_covers": len(roots),
        "new_geometric_payments": 0,
        "actual_full_latest_model_source_history_replay_and_own_acceptance_still_required": True}),
        flush=True)


if __name__ == "__main__":
    main()
