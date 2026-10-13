"""Freeze a fresh product-only supplement of an actually admitted mixed source."""

import argparse
import json
from pathlib import Path

from audit_prefix_partition import linux
import verify_conditional_force_stage as binding
import verify_current_candidate_product_forests as checker


def main():
    parser = argparse.ArgumentParser()
    for name in ("source", "source-replay", "parent-current-audit", "parent-digest-recheck",
                 "seed", "diagnosis", "arithmetic-controls", "interface-guard-controls", "output"):
        parser.add_argument("--" + name, type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    parent, rehash = binding.read(args.parent_current_audit), binding.read(args.parent_digest_recheck)
    parent_digest = binding.sha(args.parent_current_audit)
    if (rehash["current_audit_sha256"] != parent_digest
            or rehash["all_current_file_digests_rehashed"] is not True
            or rehash["current_file_digests_rechecked"] != len(parent["files"])
            or rehash["candidate_angle_unresolved_closed_boxes"]
            != parent["candidate_angle_unresolved_closed_boxes"]
            or parent.get("actual_current_candidate_acceptance") != linux(args.source / "VERIFIED.json")
            or parent.get("actual_current_candidate_pending_angles") != linux(args.source / "PENDING-ANGLES.json")):
        raise ValueError("product builder requires the explicit actual completed mixed-source parent/final")
    checker.source.identity.gate(parent, parent_digest, args.source)
    accepted, _ = binding.bound(args.source)
    if accepted["schema"] != checker.prior.SCHEMA or binding.read(args.source_replay) != accepted:
        raise ValueError("product builder requires actual own-executor mixed-source acceptance/replay")
    seed, diagnosis = binding.read(args.seed), binding.read(args.diagnosis)
    proposed = checker.proposed_forests(seed, diagnosis)
    incoming = binding.read(args.source / "PENDING-ANGLES.json")
    checker.root_gate(incoming, proposed)
    retained = binding.read(args.source / "REMAINING-ROOT-HISTORY.json")
    history = {row["source_OPEN_index"]: row for row in retained}
    if len(history) != len(retained):
        raise ValueError("product builder actual mixed source has duplicate latest histories")
    arithmetic, guard = binding.read(args.arithmetic_controls), binding.read(args.interface_guard_controls)
    if (arithmetic["schema"] != checker.ARITHMETIC
            or arithmetic["diagnosis_sha256"] != binding.sha(args.diagnosis)
            or arithmetic["old_forest_sha256"] != binding.sha(args.seed)
            or arithmetic["actual_entire_closed_root_arithmetic_reconstruction_passed"] is not True
            or guard["schema"] != checker.GUARD
            or guard["tested_own_executor_sha256"] != binding.sha(checker.__file__)
            or guard["tested_pure_controls_sha256"] != binding.sha(checker.product_controls.__file__)
            or guard["metadata_guard_controls_passed"] is not True
            or guard["complete_latest_source_model_history_gate_NOT_executed"] is not True
            or guard["verified"] is not False or guard["new_geometric_payments"] != 0):
        raise ValueError("product builder lacks this actual diagnostic's guarded new executor")
    copies = [(args.source / name, name)
              for name in accepted["files"] if name.endswith(".py")]
    copies.extend((Path(module.__file__), Path(module.__file__).name)
                  for module in (checker, *checker.executed_modules()))
    copies.extend((
        (args.source / "VERIFIED.json", "SOURCE-ACCEPTANCE.json"),
        (args.source / "PENDING-ANGLES.json", "SOURCE-PENDING-ANGLES.json"),
        (args.parent_current_audit, "SOURCE-CURRENT-AUDIT.json"),
        (args.parent_digest_recheck, "SOURCE-FINAL-DIGEST-RECHECK.json"),
        (args.seed, "OLD-ARITHMETIC-FOREST.json"), (args.diagnosis, "DIAGNOSIS.json"),
        (args.arithmetic_controls, "ARITHMETIC-CONTROLS.json"),
        (args.interface_guard_controls, "INTERFACE-GUARD-CONTROLS.json"),
    ))
    for name in (
        "build_current_candidate_product_forests.py",
        "test_product_forest_own_executor_interface.py",
        "test_candidate_difference_product_forest_arithmetic.py",
        "n26-difference-product-curvature-proof.md",
        "n26-product-forest-supplemental-acceptance-proof.md",
    ):
        copies.append((Path(__file__).with_name(name), name))
    args.output.mkdir(parents=True)
    for original_path, name in copies:
        target = args.output / name
        if target.exists():
            if target.read_bytes() != original_path.read_bytes():
                raise ValueError("product builder collided different frozen files under one name")
        else:
            with target.open("xb") as output:
                output.write(original_path.read_bytes())
    for name, data in (
        ("FORESTS.json", proposed),
        ("SOURCE-ROOT-HISTORY.json", [history[index] for index in sorted(history)]),
    ):
        with (args.output / name).open("x", encoding="utf-8", newline="\n") as output:
            output.write(json.dumps(data, indent=2) + "\n")
    manifest = {
        "schema": checker.INPUT_SCHEMA, "radius_scope": "same-root-Rstar",
        "source": linux(args.source), "source_replay": linux(args.source_replay),
        "source_acceptance_sha256": binding.sha(args.source / "VERIFIED.json"),
        "parent_current_audit": linux(args.parent_current_audit),
        "parent_current_audit_sha256": parent_digest,
        "parent_digest_recheck": linux(args.parent_digest_recheck),
        "parent_digest_recheck_sha256": binding.sha(args.parent_digest_recheck),
        "acceptance_checker_file": checker.CHECKER, "supported_curvature_modes": [checker.MODE],
        "required_source_schema": checker.prior.SCHEMA,
        "typed_resource_not_a_source_replay_substitute": True,
        "supplemental_forest_never_resets_accepted_history": True,
        "discovery_is_only_certificate_DATA_current_whole_root_rows_matched": True,
        "copied_files": {name: binding.sha(args.output / name) for name in dict.fromkeys(
            [name for _, name in copies] + ["FORESTS.json", "SOURCE-ROOT-HISTORY.json"])},
        "executed_builder_sha256": binding.sha(__file__), "verified": False,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
    }
    with (args.output / "MANIFEST.json").open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(manifest, indent=2) + "\n")
    checker.metadata_gate(args.output)
    print(json.dumps({
        "built": True, "verified": False, "supplemental_product_roots": len(proposed),
        "new_geometric_payments": 0,
        "complete_actual_mixed_source_model_history_and_own_acceptance_still_required": True}),
        flush=True)


if __name__ == "__main__":
    main()
