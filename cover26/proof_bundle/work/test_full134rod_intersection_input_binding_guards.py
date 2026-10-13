"""Read-only argument binding and OLD-fixture-as-latest rejection guards.

This does not run or validate the as-yet unfinished actual v8 successor.
"""

import argparse
from argparse import Namespace
import json
from pathlib import Path

import continue_checked_root28_full134rod_intersections as producer
import verify_conditional_force_stage as binding


def main():
    parser = argparse.ArgumentParser()
    for name in ("resource", "source", "seed", "seed-controls", "fixture-controls", "report"):
        parser.add_argument("--"+name, type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    original = {
        name.replace("-", "_"): args.fixture_controls
        for name in producer.PATH_ARGUMENTS
    }
    call_args = Namespace(**original)
    call_args.resource, call_args.source = args.resource, args.source
    digests = producer.argument_digests(call_args)
    expected = {args.resource / "VERIFIED.json", args.source / "VERIFIED.json",
                args.fixture_controls}
    if (set(digests) != expected or any(path.is_dir() for path in digests)
            or args.resource in digests or args.source in digests
            or any(binding.sha(path) != value for path, value in digests.items())):
        raise ValueError("bundle argument digest did not bind actual acceptance file bytes")
    seed, seed_controls = binding.read(args.seed), binding.read(args.seed_controls)
    if (seed["schema"] != producer.latest_controls.producer.previous.producer.SCHEMA
            or seed_controls["diagnosis_sha256"] != binding.sha(args.seed)
            or seed["verified"] is not False or seed["new_geometric_payments"] != 0):
        raise ValueError("input guards require the real preserved checked OLD v7 fixture")
    rejected = []
    call_args.seed, call_args.seed_controls = args.seed, args.seed_controls
    call_args.latest_forest, call_args.latest_controls = args.seed, args.seed_controls
    try:
        producer.latest_gate(seed, seed_controls, seed, call_args, {
            **digests, args.seed: binding.sha(args.seed),
            args.seed_controls: binding.sha(args.seed_controls),
        })
    except (ValueError, KeyError, TypeError, IndexError):
        rejected.append("actual-OLD-v7-fixture-refused-as-latest-v8-successor")
    else:
        raise AssertionError("actual OLD v7 fixture was accepted as the latest v8 producer")
    for label, name in (
        ("resource-bundle-file-not-directory-argument-rejected", "resource"),
        ("source-bundle-file-not-directory-argument-rejected", "source"),
    ):
        bad = Namespace(**vars(call_args))
        setattr(bad, name, args.fixture_controls)
        try:
            producer.argument_digests(bad)
        except (ValueError, OSError):
            rejected.append(label)
        else:
            raise AssertionError("bundle directory argument was laundered as a file")
    report = {
        "schema": "N26-independent-full134rod-intersection-input-binding-guards-v1",
        "verified": False,
        "actual_bundle_VERIFIED_files_bound_not_directory_paths": True,
        "fixture_argument_mapping_test_does_NOT_claim_all_production_inputs_checked": True,
        "actual_file_sha256": {str(path): digest for path, digest in digests.items()},
        "actual_OLD_v7_fixture_sha256": binding.sha(args.seed),
        "actual_input_guards_rejected": rejected,
        "actual_latest_v8_successor_or_controls_NOT_executed_here": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "executed_test_sha256": binding.sha(__file__),
        "tested_unexecuted_successor_producer_sha256": binding.sha(producer.__file__),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({
        "actual_bundle_argument_and_OLD_fixture_guards_passed": True,
        "actual_rejections": len(rejected),
        "NOT_actual_latest_v8_successor_or_geometry": True,
    }), flush=True)


if __name__ == "__main__":
    main()
