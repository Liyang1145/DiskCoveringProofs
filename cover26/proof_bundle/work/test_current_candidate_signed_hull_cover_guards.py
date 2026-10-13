"""Own-executor metadata/ownership guards and arithmetic-only controls.

This deliberately does NOT call the expensive complete latest source gate.
Its fixed diagnostic model can test arithmetic/control execution, but cannot
authorize geometric payments. A real standalone acceptance remains required.
"""

import argparse
from copy import deepcopy
import json
from pathlib import Path
from unittest.mock import patch

from audit_prefix_partition import linux
import n26_typed_arithmetic_context as codec
import probe_candidate_positive_curvature_hull as fixed
import verify_conditional_force_stage as binding
import verify_current_candidate_signed_hull_covers as checker


def main():
    parser = argparse.ArgumentParser()
    for name in ("resource", "resource-replay", "source", "diagnosis",
                 "arithmetic-controls", "fixture", "report"):
        parser.add_argument("--" + name, type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists() or args.fixture.exists():
        raise FileExistsError("fresh supplemental guard report and fixture required")
    resource = binding.read(args.resource / "VERIFIED.json")
    if (binding.sha(args.resource / "VERIFIED.json") != fixed.RESOURCE_SHA
            or binding.sha(args.resource_replay) != fixed.RESOURCE_SHA
            or binding.read(args.resource_replay) != resource
            or resource["resource_acceptance_is_not_a_faster_current_source_interface"] is not True
            or resource["context_is_not_a_current_candidate_source_or_a_seed_history_substitute"] is not True
            or binding.sha(args.resource / "CONTEXT.json") != resource["files"]["CONTEXT.json"]
            or binding.sha(codec.__file__) != resource["files"]["n26_typed_arithmetic_context.py"]):
        raise ValueError("supplemental guard test changed fixed arithmetic resource identity/scope")
    diagnosis = binding.read(args.diagnosis)
    regression = binding.read(args.arithmetic_controls)
    incoming = binding.read(args.source / "PENDING-ANGLES.json")
    history, _ = checker.owned.history(args.source, incoming)
    roots = [item for item in diagnosis["roots"]
             if item["all_arithmetic_cover_obligations_passed"]]
    checker.root_gate(incoming, roots)
    args.fixture.mkdir(parents=True)
    modules = [checker, checker.identity, checker.owned, checker.covers,
               checker.covers.hull, checker.covers.forest, checker.prior_checker]
    copies = [(Path(module.__file__), Path(module.__file__).name) for module in modules]
    copies.extend((
        (args.diagnosis, "DIAGNOSIS.json"),
        (args.arithmetic_controls, "ARITHMETIC-COVER-CONTROLS.json"),
        (Path(__file__).with_name("test_signed_hull_local_cover_arithmetic.py"),
         "test_signed_hull_local_cover_arithmetic.py"),
    ))
    for original, name in copies:
        with (args.fixture / name).open("xb") as output:
            output.write(original.read_bytes())
    manifest = {
        "schema": checker.INPUT_SCHEMA, "radius_scope": "same-root-Rstar",
        "acceptance_checker_file": checker.CHECKER,
        "typed_resource_not_a_source_replay_substitute": True,
        "supplemental_cover_never_replaces_accepted_forest": True,
        "synthetic_metadata_fixture_not_a_real_source_bundle": True,
        "copied_files": {name: binding.sha(args.fixture / name) for _, name in copies},
    }
    with (args.fixture / "MANIFEST.json").open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(manifest, indent=2) + "\n")
    checker.metadata_gate(args.fixture)
    negatives = []
    original_read = binding.read

    def reject_metadata(name, target_name, mutation):
        data = original_read(args.fixture / target_name)
        mutation(data)

        def reader(path):
            if binding.local_path(path).resolve() == (args.fixture / target_name).resolve():
                return deepcopy(data)
            return original_read(path)

        with patch.object(binding, "read", side_effect=reader):
            try:
                checker.metadata_gate(args.fixture)
            except (ValueError, KeyError, TypeError):
                negatives.append(name)
            else:
                raise AssertionError("invalid supplemental metadata accepted: " + name)

    for name, mutation in (
        ("acceptance-executor-relabelled-as-old-owned-checker",
         lambda bad: bad.update(acceptance_checker_file="verify_owned_candidate_forests.py")),
        ("candidate-radius-scope-promoted-to-original-U",
         lambda bad: bad.update(radius_scope="unconditional-original-U")),
        ("typed-resource-promoted-to-source-replay-cache",
         lambda bad: bad.update(typed_resource_not_a_source_replay_substitute=False)),
        ("new-cover-authorized-to-replace-old-forest",
         lambda bad: bad.update(supplemental_cover_never_replaces_accepted_forest=False)),
        ("own-sealed-executor-hash-forged",
         lambda bad: bad["copied_files"].update({checker.CHECKER: "0" * 64})),
    ):
        reject_metadata(name, "MANIFEST.json", mutation)
    reject_metadata("discovery-promoted-to-accepted-report", "DIAGNOSIS.json",
                    lambda bad: bad.update(verified=True))
    reject_metadata("discovery-paid-whole-roots", "DIAGNOSIS.json",
                    lambda bad: bad.update(current_candidate_whole_roots_removed=6))
    reject_metadata("arithmetic-regression-promoted-to-source-replay",
                    "ARITHMETIC-COVER-CONTROLS.json",
                    lambda bad: bad.update(full_source_model_history_replay_not_performed=False))
    reject_metadata("arithmetic-test-executor-hash-forged",
                    "ARITHMETIC-COVER-CONTROLS.json",
                    lambda bad: bad.update(executed_test_sha256="0" * 64))
    # Execute all thirteen controls against the diagnostic fixed model ONLY.
    # The test makes no claim that this model came through the full source gate.
    model = codec.gate(binding.read(args.resource / "CONTEXT.json")["typed_context"])
    original, kernel = model["original"], model["original_kernel"]
    arcs = binding.force.load_trig(args.resource)[0]
    original_values = (None, None, model["original_curvature_source_acceptance"],
                       original, None, kernel, arcs, None, None)
    values = (None, None, None, original_values, incoming, roots, history, [], [], None)
    payments, remaining, _, retained = checker.derive(values)
    positives, arithmetic_negatives = checker.controls(values)
    if len(arithmetic_negatives) != 13 or len(payments) + len(remaining) != len(incoming):
        raise AssertionError("supplemental actual arithmetic controls/accounting incomplete")
    report = {
        "schema": "N26-current-signed-hull-cover-guard-controls-v1",
        "synthetic_metadata_controls_passed": True,
        "metadata_rejection_controls": negatives,
        "actual_arithmetic_rejection_control_code_exercised": arithmetic_negatives,
        "arithmetic_root_covers_checked": len(payments),
        "arithmetic_remaining_root_rows": len(remaining),
        "arithmetic_retained_history_entries": len(retained),
        "signed_tiny_positive_controls": positives["fresh_signed_hull_feasible_tiny_controls"],
        "fixed_resource_used_only_for_arithmetic_control_execution": True,
        "complete_latest_source_model_and_history_gate_NOT_executed": True,
        "this_test_is_NOT_standalone_geometry_acceptance": True,
        "verified": False, "new_geometric_payments": 0,
        "candidate_whole_roots_removed": 0, "global_optimality_proved": False,
        "diagnosis_sha256": binding.sha(args.diagnosis),
        "tested_own_acceptance_executor_sha256": binding.sha(checker.__file__),
        "executed_test_sha256": binding.sha(__file__),
        "fixture": linux(args.fixture),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2), flush=True)


if __name__ == "__main__":
    main()
