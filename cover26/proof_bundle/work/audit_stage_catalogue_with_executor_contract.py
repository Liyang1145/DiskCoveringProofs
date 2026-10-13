"""Strict admission plus the unchanged complete stage/catalogue semantic audit.

The original auditor runs as a separate subprocess and publishes a preserved
core report. This wrapper adds the executor/control contract and proof-time
parent rehash to the final inventory. It creates no new geometric payments.
"""

import argparse
import json
from pathlib import Path
import subprocess
import sys

from audit_prefix_partition import linux
import audit_conditional_stage_acceptance_contract as contract
import verify_conditional_force_stage as binding


def main():
    parser = argparse.ArgumentParser()
    for name in (
        "parent-audit", "parent-digest-recheck", "stage", "stage-replay",
        "catalog", "catalog-replay", "narrative", "dependency-note",
        "family-scope", "contract-regression", "output",
    ):
        parser.add_argument("--" + name, type=Path, required=True)
    args = parser.parse_args()
    target = args.output
    core_path = target.with_name(target.stem + "-semantic-core.json")
    admission_path = target.with_name(target.stem + "-executor-admission.json")
    suffixes = (
        "-closed-type-pool.json", "-closed-receipt-checks.json",
        "-terminal-obligations.json",
    )
    fresh_paths = [
        target, core_path, admission_path,
        *(target.with_name(target.stem + suffix) for suffix in suffixes),
        *(core_path.with_name(core_path.stem + suffix) for suffix in suffixes),
    ]
    if any(path.exists() for path in fresh_paths):
        raise FileExistsError("strict current admission needs entirely fresh outputs")
    parent_digest = binding.sha(args.parent_audit)
    parent, rehash = binding.read(args.parent_audit), binding.read(args.parent_digest_recheck)
    if (
        rehash["current_audit_sha256"] != parent_digest
        or rehash["all_current_file_digests_rehashed"] is not True
        or rehash["current_file_digests_rechecked"] != len(parent["files"])
        or rehash["candidate_angle_unresolved_closed_boxes"]
        != parent["candidate_angle_unresolved_closed_boxes"]
    ):
        raise ValueError("strict admission lacks the complete parent and its independent rehash")
    acceptance = binding.read(args.stage / "VERIFIED.json")
    manifest = binding.read(args.stage / "MANIFEST.json")
    checker = contract.gate(acceptance, manifest)
    if (
        binding.sha(args.stage / checker) != acceptance["executed_checker_sha256"]
        or binding.read(args.stage_replay) != acceptance
    ):
        raise ValueError("actual own-executor publication replay differs or code bytes changed")
    regression = binding.read(args.contract_regression)
    if (
        regression["known_good_acceptance_sha256"]
        != binding.sha(args.stage / "VERIFIED.json")
        or regression["known_good_metadata_contract_passed"] is not True
        or regression["suspect_contract_rejected"] is not True
        or len(regression["guard_rejection_controls_passed"]) != 6
        or regression["executed_diagnostic_sha256"] != binding.sha(contract.__file__)
        or regression["metadata_only_not_a_geometric_replay"] is not True
        or regression["new_geometric_payments"] != 0
    ):
        raise ValueError("actual executor-contract regression is missing or not bound to this stage")
    executor = Path(__file__).with_name("audit_stage_catalogue_with_closed_pool.py")
    executor_digest = binding.sha(executor)
    command = [sys.executable, str(executor)]
    for name in (
        "parent-audit", "stage", "stage-replay", "catalog", "catalog-replay",
        "narrative", "dependency-note", "family-scope",
    ):
        command.extend(("--" + name, str(getattr(args, name.replace("-", "_")))))
    command.extend(("--output", str(core_path)))
    print("Executor contract passed; running the unchanged complete semantic audit.", flush=True)
    result = subprocess.run(command, check=False)
    if result.returncode:
        raise ValueError("strict current semantic core failed; partial outputs retained")
    core = binding.read(core_path)
    if (
        binding.sha(args.parent_audit) != parent_digest
        or binding.sha(executor) != executor_digest
        or core["prior_current_audit_sha256"] != parent_digest
        or core["current_bound_bytes_rechecked"] is not True
    ):
        raise ValueError("strict admission parent or semantic executor changed")
    inventory = dict(core["files"])
    for suffix in suffixes:
        source = core_path.with_name(core_path.stem + suffix)
        destination = target.with_name(target.stem + suffix)
        with source.open("rb") as input_stream, destination.open("xb") as output_stream:
            for block in iter(lambda: input_stream.read(1024 * 1024), b""):
                output_stream.write(block)
        inventory[linux(destination)] = binding.sha(destination)
    admission = {
        "schema": "N26-strict-conditional-current-executor-admission-v1",
        "accepted_stage_sha256": binding.sha(args.stage / "VERIFIED.json"),
        "actual_stage_replay_sha256": binding.sha(args.stage_replay),
        "sealed_acceptance_executor_file": checker,
        "sealed_acceptance_executor_sha256": acceptance["executed_checker_sha256"],
        "actual_conditional_rejection_controls": acceptance["negative_controls_rejected"],
        "actual_feasible_regular_ring_controls": 32,
        "contract_regression_sha256": binding.sha(args.contract_regression),
        "parent_current_sha256": parent_digest,
        "parent_independent_rehash_sha256": binding.sha(args.parent_digest_recheck),
        "preserved_semantic_core_sha256": binding.sha(core_path),
        "actual_semantic_audit_command": command,
        "actual_semantic_audit_exit_code": result.returncode,
        "actual_semantic_executor_sha256": executor_digest,
        "executed_admission_sha256": binding.sha(__file__),
        "new_geometric_payments_by_admission": 0,
        "global_optimality_proved": False,
    }
    with admission_path.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(admission, indent=2) + "\n")
    for path in (
        core_path, admission_path, args.parent_digest_recheck,
        args.contract_regression, Path(contract.__file__), Path(__file__),
        Path(__file__).with_name("n26-conditional-acceptance-admission-rule-v1.md"),
    ):
        key, digest = linux(path), binding.sha(path)
        if key in inventory and inventory[key] != digest:
            raise ValueError("strict admission changed an already bound dependency")
        inventory[key] = digest
    print("Binding the semantic core, actual admission executor and all current files.", flush=True)
    for number, (text, digest) in enumerate(inventory.items(), 1):
        if binding.sha(text) != digest:
            raise ValueError("strict current dependency changed during final binding: " + text)
        if number % 10000 == 0:
            print(json.dumps({"strict_current_digests_checked": number,
                              "total": len(inventory)}), flush=True)
    report = dict(core)
    report["files"] = inventory
    report["conditional_acceptance_executor_contract_enforced"] = True
    report["conditional_executor_contract_receipt"] = linux(admission_path)
    report["preserved_original_semantic_current_audit"] = linux(core_path)
    report["executed_current_admission_sha256"] = binding.sha(__file__)
    with target.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2) + "\n")
    print(json.dumps({
        "strict_current_admission_passed": True,
        "bound_current_files": len(inventory),
        "frontier": report["Rstar_conditional_frontier_pending_subtrees"],
        "candidate_whole_roots": report["candidate_angle_unresolved_closed_boxes"],
        "independent_final_rehash_still_required": True,
        "global_optimality_proved": False,
    }), flush=True)


if __name__ == "__main__":
    main()
