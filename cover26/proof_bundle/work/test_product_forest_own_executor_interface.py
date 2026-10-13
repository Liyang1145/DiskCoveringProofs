"""Real product arithmetic and synthetic own-executor metadata controls.

The old fixed model and source DATA are used only for interface tests.
This never invokes the complete latest source/model/history gate.
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
import verify_current_candidate_product_forests as checker


def main():
    parser = argparse.ArgumentParser()
    for name in ("resource", "resource-replay", "source", "seed", "diagnosis",
                 "arithmetic-controls", "fixture", "report"):
        parser.add_argument("--" + name, type=Path, required=True)
    args = parser.parse_args()
    if args.fixture.exists() or args.report.exists():
        raise FileExistsError("fresh product interface fixture/report required")
    resource = binding.read(args.resource / "VERIFIED.json")
    if (binding.sha(args.resource / "VERIFIED.json") != fixed.RESOURCE_SHA
            or binding.sha(args.resource_replay) != fixed.RESOURCE_SHA
            or binding.read(args.resource_replay) != resource
            or resource["resource_acceptance_is_not_a_faster_current_source_interface"] is not True
            or resource["context_is_not_a_current_candidate_source_or_a_seed_history_substitute"] is not True
            or binding.sha(args.resource / "CONTEXT.json") != resource["files"]["CONTEXT.json"]
            or binding.sha(codec.__file__) != resource["files"]["n26_typed_arithmetic_context.py"]):
        raise ValueError("product interface test changed arithmetic DATA identity or zero-source scope")
    model = codec.gate(binding.read(args.resource / "CONTEXT.json")["typed_context"])
    original, kernel = model["original"], model["original_kernel"]
    arcs = binding.force.load_trig(args.resource)[0]
    accepted = binding.read(args.source / "VERIFIED.json")
    for name in ("PENDING-ANGLES.json", "PROPOSAL.json", "ROOT-CLASSIFICATION.json"):
        if binding.sha(args.source / name) != accepted["files"][name]:
            raise ValueError("product interface test changed real source/history DATA")
    incoming = binding.read(args.source / "PENDING-ANGLES.json")
    classes = {row["source_OPEN_index"]: row for row in
               binding.read(args.source / "ROOT-CLASSIFICATION.json")}
    current = {row["index"] for row in incoming}
    history = {}
    for item in binding.read(args.source / "PROPOSAL.json")["forests"]:
        index = item["source_OPEN_index"]
        if index in current:
            history[index] = {
                "source_OPEN_index": index, "actual_source_closed_box": item["actual_source_closed_box"],
                "history_source": linux(args.source),
                "history_acceptance_sha256": binding.sha(args.source / "VERIFIED.json"),
                "nodes": item["nodes"], "accepted_source_classification": classes[index],
            }
    seed, diagnosis = binding.read(args.seed), binding.read(args.diagnosis)
    proposed = checker.proposed_forests(seed, diagnosis)
    original_values = (None, None, model["original_curvature_source_acceptance"],
                       original, None, kernel, arcs, None, None)
    values = (None, None, None, original_values, incoming, proposed, history, [], [], None)
    payments, remaining, classified, ledgers, retained = checker.derive(values)
    if (len(payments) != 1 or classified[0]["counts"] != diagnosis["arithmetic_result"]["counts"]
            or ledgers[0]["exact_closed_leaf_ledger"] != diagnosis["arithmetic_ledger"]):
        raise AssertionError("new distinct product interface changed independently tested real arithmetic")
    positive, negative = checker.controls(values)
    arithmetic = binding.read(args.arithmetic_controls)
    if (negative[:13] != arithmetic["rejection_controls_passed"]
            or positive["actual_product_arithmetic_positive_controls"]
            != arithmetic["positive_arithmetic_controls"]):
        raise AssertionError("new pure product controls differ from independent actual arithmetic controls")
    args.fixture.mkdir(parents=True)
    guard = {
        "schema": checker.GUARD, "metadata_guard_controls_passed": True,
        "actual_arithmetic_rejection_paths_exercised": negative[:13],
        "actual_ownership_history_and_mode_rejection_paths_exercised": negative[13:],
        "complete_latest_source_model_history_gate_NOT_executed": True,
        "synthetic_metadata_fixture_NOT_a_geometry_bundle": True,
        "verified": False, "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "tested_own_executor_sha256": binding.sha(checker.__file__),
        "tested_pure_controls_sha256": binding.sha(checker.product_controls.__file__),
        "executed_test_sha256": binding.sha(__file__),
    }
    copies = [(Path(module.__file__), Path(module.__file__).name)
              for module in (checker, *checker.executed_modules())]
    copies.extend((
        (args.seed, "OLD-ARITHMETIC-FOREST.json"), (args.diagnosis, "DIAGNOSIS.json"),
        (args.arithmetic_controls, "ARITHMETIC-CONTROLS.json"),
        (Path(__file__), Path(__file__).name),
        (Path(__file__).with_name("test_candidate_difference_product_forest_arithmetic.py"),
         "test_candidate_difference_product_forest_arithmetic.py"),
    ))
    for original_path, name in copies:
        target = args.fixture / name
        if target.exists():
            if target.read_bytes() != original_path.read_bytes():
                raise ValueError("product interface test fixture has a module-name collision")
        else:
            with target.open("xb") as output:
                output.write(original_path.read_bytes())
    with (args.fixture / "INTERFACE-GUARD-CONTROLS.json").open(
            "x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(guard, indent=2) + "\n")
    manifest = {
        "schema": checker.INPUT_SCHEMA, "radius_scope": "same-root-Rstar",
        "acceptance_checker_file": checker.CHECKER,
        "supported_curvature_modes": [checker.MODE],
        "required_source_schema": checker.prior.SCHEMA,
        "typed_resource_not_a_source_replay_substitute": True,
        "supplemental_forest_never_resets_accepted_history": True,
        "synthetic_metadata_fixture_NOT_a_complete_source_bundle": True,
        "copied_files": {name: binding.sha(args.fixture / name) for name in dict.fromkeys(
            [name for _, name in copies] + ["INTERFACE-GUARD-CONTROLS.json"])},
    }
    with (args.fixture / "MANIFEST.json").open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(manifest, indent=2) + "\n")
    checker.metadata_gate(args.fixture)
    metadata_negative = []
    real_read = binding.read

    def reject(label, name, mutation):
        bad = real_read(args.fixture / name)
        mutation(bad)

        def reader(path):
            if binding.local_path(path).resolve() == (args.fixture / name).resolve():
                return deepcopy(bad)
            return real_read(path)

        with patch.object(binding, "read", side_effect=reader):
            try:
                checker.metadata_gate(args.fixture)
            except (ValueError, KeyError, TypeError, IndexError):
                metadata_negative.append(label)
            else:
                raise AssertionError("invalid product interface metadata accepted: " + label)

    for label, mutation in (
        ("product-executor-relabelled-as-mixed-checker",
         lambda bad: bad.update(acceptance_checker_file=checker.prior.CHECKER)),
        ("product-mode-relabelled-as-integrated-Taylor",
         lambda bad: bad.update(supported_curvature_modes=["integrated-Taylor"])),
        ("unadmitted-old-owned-source-substituted-for-mixed",
         lambda bad: bad.update(required_source_schema=checker.prior.constant.owned.SCHEMA)),
        ("product-radius-scope-promoted-to-U",
         lambda bad: bad.update(radius_scope="unconditional-original-U")),
        ("typed-model-promoted-to-source-cache",
         lambda bad: bad.update(typed_resource_not_a_source_replay_substitute=False)),
        ("product-authorized-to-reset-accepted-history",
         lambda bad: bad.update(supplemental_forest_never_resets_accepted_history=False)),
        ("product-own-executed-code-hash-forged",
         lambda bad: bad["copied_files"].update({checker.CHECKER: "0" * 64})),
    ):
        reject(label, "MANIFEST.json", mutation)
    reject("product-discovery-promoted-to-geometry", "DIAGNOSIS.json",
           lambda bad: bad.update(verified=True))
    reject("product-continuation-overwrites-old-closed-node", "DIAGNOSIS.json",
           lambda bad: bad["nodes"].__setitem__(0, {"kind": "OPEN"}))
    reject("product-independent-arithmetic-rejections-omitted", "ARITHMETIC-CONTROLS.json",
           lambda bad: bad.update(rejection_controls_passed=[]))
    reject("product-interface-test-promoted-to-full-source-gate", "INTERFACE-GUARD-CONTROLS.json",
           lambda bad: bad.update(complete_latest_source_model_history_gate_NOT_executed=False))
    reject("product-interface-executor-hash-forged", "INTERFACE-GUARD-CONTROLS.json",
           lambda bad: bad.update(tested_own_executor_sha256="0" * 64))
    report = {
        **guard, "metadata_invalid_controls_rejected": metadata_negative,
        "actual_root_arithmetic_nodes": len(proposed[0]["nodes"]),
        "actual_root_arithmetic_classification": classified[0],
        "actual_positive_arithmetic_controls_match_independent_test": True,
        "actual_data_test_source_is_owned_NOT_a_current_mixed_source_admission": True,
        "synthetic_remaining_count_NOT_formal_current": len(remaining),
        "synthetic_retained_partial_history_entries": len(retained),
        "diagnosis_sha256": binding.sha(args.diagnosis),
        "independent_arithmetic_controls_sha256": binding.sha(args.arithmetic_controls),
        "global_lower_bound_proved": False, "global_optimality_proved": False,
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2) + "\n")
    print(json.dumps({
        "product_interface_guard_tests_completed": True,
        "real_arithmetic_rejections": 13, "real_ownership_history_mode_rejections": 6,
        "synthetic_metadata_rejections": len(metadata_negative),
        "verified": False, "new_geometric_payments": 0}), flush=True)


if __name__ == "__main__":
    main()
