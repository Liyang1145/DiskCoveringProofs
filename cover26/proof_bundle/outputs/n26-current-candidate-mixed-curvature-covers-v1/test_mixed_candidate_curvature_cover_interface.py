"""Synthetic mode/source-contract guards and actual arithmetic controls.

The fixed diagnostic model is arithmetic test data only. This test DOES NOT
execute the complete latest owned source/model gate and pays zero roots.
"""

import argparse
from copy import deepcopy
import json
from pathlib import Path
from unittest.mock import patch

from audit_prefix_partition import linux
import n26_typed_arithmetic_context as codec
import probe_candidate_positive_curvature_hull as fixed
import test_integrated_hull_cover_arithmetic as previous_integral_test
import verify_conditional_force_stage as binding
import verify_current_candidate_mixed_curvature_covers as checker


def main():
    parser = argparse.ArgumentParser()
    for name in (
        "resource", "resource-replay", "source", "constant-diagnosis",
        "constant-arithmetic-controls", "integral-diagnosis",
        "integral-arithmetic-controls", "fixture", "report",
    ):
        parser.add_argument("--" + name, type=Path, required=True)
    args = parser.parse_args()
    if args.fixture.exists() or args.report.exists():
        raise FileExistsError("fresh mixed-curvature guard fixture/report required")
    resource = binding.read(args.resource / "VERIFIED.json")
    if (binding.sha(args.resource / "VERIFIED.json") != fixed.RESOURCE_SHA
            or binding.sha(args.resource_replay) != fixed.RESOURCE_SHA
            or binding.read(args.resource_replay) != resource
            or resource["resource_acceptance_is_not_a_faster_current_source_interface"] is not True
            or resource["context_is_not_a_current_candidate_source_or_a_seed_history_substitute"] is not True
            or binding.sha(args.resource / "CONTEXT.json") != resource["files"]["CONTEXT.json"]
            or binding.sha(codec.__file__) != resource["files"]["n26_typed_arithmetic_context.py"]):
        raise ValueError("mixed test changed the fixed diagnostic model or zero-source scope")
    model = codec.gate(binding.read(args.resource / "CONTEXT.json")["typed_context"])
    original, kernel = model["original"], model["original_kernel"]
    arcs = binding.force.load_trig(args.resource)[0]
    first, second = binding.read(args.constant_diagnosis), binding.read(args.integral_diagnosis)
    roots = checker.selected_covers(first, second)
    accepted = binding.read(args.source / "VERIFIED.json")
    if (accepted["schema"] != checker.constant.owned.SCHEMA
            or accepted["verified"] is not True):
        raise ValueError("mixed test requires actual accepted owned-forest DATA, not a new source gate")
    for name in ("PENDING-ANGLES.json", "PROPOSAL.json", "ROOT-CLASSIFICATION.json"):
        if binding.sha(args.source / name) != accepted["files"][name]:
            raise ValueError("mixed arithmetic test source data changed")
    incoming = binding.read(args.source / "PENDING-ANGLES.json")
    classes = {row["source_OPEN_index"]: row for row in
               binding.read(args.source / "ROOT-CLASSIFICATION.json")}
    pending_indices = {row["index"] for row in incoming}
    history = {}
    # DATA-only latest-layer snapshot for unit controls, not a replacement for
    # owned.history or its complete semantic/source replay in real acceptance.
    for item in binding.read(args.source / "PROPOSAL.json")["forests"]:
        index = item["source_OPEN_index"]
        if index in pending_indices:
            history[index] = {
                "source_OPEN_index": index,
                "actual_source_closed_box": item["actual_source_closed_box"],
                "history_source": linux(args.source),
                "history_acceptance_sha256": binding.sha(args.source / "VERIFIED.json"),
                "nodes": item["nodes"], "accepted_source_classification": classes[index],
            }
    checker.modes_gate(roots)
    by_index = checker.constant.root_gate(incoming, roots)
    original_values = (None, None, model["original_curvature_source_acceptance"],
                       original, None, kernel, arcs, None, None)
    values = (None, None, None, original_values, incoming, roots, history, [], [], None)
    payments, remaining, classified, retained = checker.derive(values)
    positives, actual_negative = checker.controls(values)
    # Fresh pure backend must agree with the separately preserved earlier
    # independent arithmetic test on each valid integrated cover.
    for item in roots:
        if item["mode"] == checker.MODES[1]:
            expected = previous_integral_test.replay(
                original, kernel, arcs, by_index[item["source_OPEN_index"]], item["cover"])
            fresh = checker.integral.replay(
                original, kernel, arcs, by_index[item["source_OPEN_index"]], item["cover"])
            if fresh != expected:
                raise AssertionError("new pure integrated backend changed tested arithmetic semantics")
    args.fixture.mkdir(parents=True)
    guard = {
        "schema": "N26-mixed-curvature-cover-interface-guard-controls-v1",
        "metadata_guard_controls_passed": True,
        "actual_arithmetic_rejection_control_paths_exercised": actual_negative,
        "complete_latest_model_source_history_gate_NOT_executed": True,
        "verified": False, "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "tested_own_acceptance_executor_sha256": binding.sha(checker.__file__),
        "tested_integral_backend_sha256": binding.sha(checker.integral.__file__),
        "executed_test_sha256": binding.sha(__file__),
        "synthetic_metadata_fixture_NOT_a_geometry_bundle": True,
    }
    copies = [(Path(module.__file__), Path(module.__file__).name)
              for module in (checker, *checker.executed_modules())]
    copies.extend((
        (args.constant_diagnosis, "CONSTANT-DIAGNOSIS.json"),
        (args.integral_diagnosis, "INTEGRAL-DIAGNOSIS.json"),
        (args.constant_arithmetic_controls, "CONSTANT-ARITHMETIC-CONTROLS.json"),
        (args.integral_arithmetic_controls, "INTEGRAL-ARITHMETIC-CONTROLS.json"),
        (Path(__file__).with_name("test_signed_hull_local_cover_arithmetic.py"),
         "test_signed_hull_local_cover_arithmetic.py"),
        (Path(previous_integral_test.__file__), "test_integrated_hull_cover_arithmetic.py"),
        (Path(__file__), Path(__file__).name),
    ))
    for original_path, name in copies:
        target = args.fixture / name
        if target.exists():
            if target.read_bytes() != original_path.read_bytes():
                raise ValueError("mixed test fixture module-name collision")
        else:
            with target.open("xb") as output:
                output.write(original_path.read_bytes())
    with (args.fixture / "INTERFACE-GUARD-CONTROLS.json").open(
            "x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(guard, indent=2) + "\n")
    manifest = {
        "schema": checker.INPUT_SCHEMA, "radius_scope": "same-root-Rstar",
        "acceptance_checker_file": checker.CHECKER,
        "supported_curvature_modes": checker.MODES,
        "typed_resource_not_a_source_replay_substitute": True,
        "supplemental_cover_never_replaces_accepted_forest": True,
        "synthetic_metadata_fixture_NOT_a_complete_source_bundle": True,
        "copied_files": {name: binding.sha(args.fixture / name) for name in dict.fromkeys(
            [name for _, name in copies] + ["INTERFACE-GUARD-CONTROLS.json"])},
    }
    with (args.fixture / "MANIFEST.json").open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(manifest, indent=2) + "\n")
    checker.metadata_gate(args.fixture)
    metadata_negative = []
    real_read = binding.read

    def reject(name, target_name, mutation):
        bad = real_read(args.fixture / target_name)
        mutation(bad)

        def reader(path):
            if binding.local_path(path).resolve() == (args.fixture / target_name).resolve():
                return deepcopy(bad)
            return real_read(path)

        with patch.object(binding, "read", side_effect=reader):
            try:
                checker.metadata_gate(args.fixture)
            except (ValueError, KeyError, TypeError):
                metadata_negative.append(name)
            else:
                raise AssertionError("invalid mixed metadata accepted: " + name)

    for name, mutation in (
        ("own-executor-relabelled-as-old-constant-checker",
         lambda bad: bad.update(acceptance_checker_file=checker.constant.CHECKER)),
        ("integrated-mode-omitted",
         lambda bad: bad.update(supported_curvature_modes=[checker.MODES[0]])),
        ("unproved-mode-added",
         lambda bad: bad.update(supported_curvature_modes=[*checker.MODES, "unproved"])),
        ("radius-scope-promoted-to-U",
         lambda bad: bad.update(radius_scope="unconditional-original-U")),
        ("typed-resource-promoted-to-source-cache",
         lambda bad: bad.update(typed_resource_not_a_source_replay_substitute=False)),
        ("new-cover-authorized-to-reset-old-forest",
         lambda bad: bad.update(supplemental_cover_never_replaces_accepted_forest=False)),
        ("own-executed-code-hash-forged",
         lambda bad: bad["copied_files"].update({checker.CHECKER: "0" * 64})),
    ):
        reject(name, "MANIFEST.json", mutation)
    reject("constant-diagnosis-promoted-to-geometry", "CONSTANT-DIAGNOSIS.json",
           lambda bad: bad.update(verified=True))
    reject("integral-diagnosis-promoted-to-geometry", "INTEGRAL-DIAGNOSIS.json",
           lambda bad: bad.update(verified=True))
    reject("integral-arithmetic-controls-omitted", "INTEGRAL-ARITHMETIC-CONTROLS.json",
           lambda bad: bad.update(rejection_controls_passed=[]))
    reject("guard-test-promoted-to-complete-source-replay", "INTERFACE-GUARD-CONTROLS.json",
           lambda bad: bad.update(complete_latest_model_source_history_gate_NOT_executed=False))
    reject("guard-test-executor-hash-forged", "INTERFACE-GUARD-CONTROLS.json",
           lambda bad: bad.update(executed_test_sha256="0" * 64))
    if (len(payments) + len(remaining) != len(incoming)
            or len(actual_negative) != 29
            or not any(row["source_OPEN_index"] == 959 for row in retained)
            or [row for row in retained if row["source_OPEN_index"] == 959]
            != [history[959]]):
        raise AssertionError("mixed conservation or latest incomplete root959 history lost")
    report = {
        **guard, "metadata_rejection_controls": metadata_negative,
        "arithmetic_source_whole_roots": len(incoming),
        "arithmetic_root_covers_checked": len(payments),
        "arithmetic_remaining_whole_roots": len(remaining),
        "arithmetic_strict_slabs_checked": sum(row["strict_slabs"] for row in classified),
        "arithmetic_original_LOCAL_boxes_checked": len(classified),
        "mode_root_counts": {mode: sum(row["mode"] == mode for row in classified)
                             for mode in checker.MODES},
        "constant_tiny_positive_controls": positives["constant_hull_tiny_controls"],
        "integrated_tiny_positive_controls": positives["integrated_Taylor_tiny_controls"],
        "pure_integral_backend_matches_preserved_independent_arithmetic_tester": True,
        "latest_accepted_root959_partial_history_DATA_retained_identically": True,
        "history_data_from_owned_standalone_layer_NOT_current_source_admission": True,
        "fixed_resource_used_only_for_arithmetic_control_execution": True,
        "fixture": linux(args.fixture),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2), flush=True)


if __name__ == "__main__":
    main()
