"""Reject insufficient conditional acceptance metadata before full composition.

This guard is NOT a geometry verifier. The unchanged sealed stage verifier,
its actual replay and the full current-chain replay remain required. In
particular, a compatibility report cannot claim another executor's identity.
"""

import argparse
from copy import deepcopy
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path


ORIGINAL_SCHEMA = "N26-successive-radius-conditional-force-angular-stage-acceptance-v1"
SPARSE_SCHEMA = "N26-successive-radius-conditional-sparse-stage-acceptance-v2"
SCOPE = "at-most-same-root-Rstar-not-original-U"
REJECTIONS = [
    "conditional-frontier-promoted-to-unconditional-U",
    "same-root-radius-endpoint-replaced-by-screen-threshold",
    "conditional-source-family-changed",
    "lost-conditional-pending-sibling",
    "missing-conditional-native-event",
    "changed-conditional-complete-sibling-count",
    "conditional-angular-closed-half-lost",
    "conditional-angular-hidden-node",
    "candidate-full-terminal-replaced-by-ancestor",
]


def sha(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as source:
        for block in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def read(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))


def gate(report, manifest):
    schema = report.get("schema")
    if schema == ORIGINAL_SCHEMA:
        checker = "verify_conditional_force_stage.py"
    elif schema == SPARSE_SCHEMA:
        checker = "verify_conditional_force_stage_sparse.py"
        if report.get("executed_checker_file") != checker:
            raise ValueError("sparse executor identity is missing or different")
        if manifest.get("sparse_event_control_policy", {}).get(
            "acceptance_checker_file"
        ) != checker:
            raise ValueError("sparse executor is not the sealed acceptance executor")
    else:
        raise ValueError("unsupported conditional acceptance executor/schema")
    if (
        report.get("verified") is not True
        or report.get("radius_scope") != SCOPE
        or report.get("inherited_source_is_unconditional_at_U") is not False
        or report.get("global_optimality_proved") is not False
        or report.get("global_lower_bound_proved") is not False
        or report.get("full_catalog_complete") is not False
        or report.get("negative_controls_rejected") != REJECTIONS
        or type(report.get("feasible_regular_ring_regression_controls")) is not int
        or report["feasible_regular_ring_regression_controls"] != 32
    ):
        raise ValueError("conditional acceptance lost its scope or actual required controls")
    if (
        report.get("executed_checker_sha256") != report.get("files", {}).get(checker)
        or report.get("executed_checker_sha256")
        != manifest.get("copied_files", {}).get(checker)
    ):
        raise ValueError("acceptance does not bind its own sealed executor")
    semantic = "verify_conditional_force_stage.py"
    if schema == SPARSE_SCHEMA and (
        report.get("original_exact_semantic_replayer_sha256")
        != report["files"].get(semantic)
        or report["files"].get(semantic) != manifest["copied_files"].get(semantic)
    ):
        raise ValueError("sparse acceptance relabels the unchanged semantic replayer")
    return checker


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--known-good-stage", type=Path, required=True)
    parser.add_argument("--suspect-stage", type=Path, required=True)
    parser.add_argument("--compat-producer", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    known_path = args.known_good_stage / "VERIFIED.json"
    suspect_path = args.suspect_stage / "VERIFIED.json"
    known, known_manifest = read(known_path), read(args.known_good_stage / "MANIFEST.json")
    suspect, suspect_manifest = read(suspect_path), read(args.suspect_stage / "MANIFEST.json")
    known_checker = gate(known, known_manifest)
    if sha(args.known_good_stage / known_checker) != known["executed_checker_sha256"]:
        raise ValueError("known good sealed checker bytes changed")
    rejected = []
    for label, change in (
        ("compat-schema-laundered-as-conditional", lambda row: row.update(schema=suspect["schema"])),
        ("missing-four-condition-specific-rejections", lambda row: row.update(
            negative_controls_rejected=suspect["negative_controls_rejected"])),
        ("executor-renamed-to-original-semantics", lambda row: row.update(
            executed_checker_file="verify_conditional_force_stage.py")),
        ("wrong-executor-hash", lambda row: row.update(executed_checker_sha256="0" * 64)),
        ("conditional-scope-promoted-to-U", lambda row: row.update(
            radius_scope="unconditional-original-U")),
        ("positive-control-omitted", lambda row: row.update(
            feasible_regular_ring_regression_controls=31)),
    ):
        changed = deepcopy(known)
        change(changed)
        try:
            gate(changed, known_manifest)
        except (ValueError, KeyError, TypeError):
            rejected.append(label)
        else:
            raise AssertionError("insufficient metadata accepted: " + label)
    try:
        gate(suspect, suspect_manifest)
    except (ValueError, KeyError, TypeError) as error:
        suspect_error = str(error)
    else:
        raise AssertionError("compatibility report unexpectedly passed the executor contract")
    producer_sha = sha(args.compat_producer)
    claimed_file = suspect.get("executed_checker_file")
    evidence = {
        "schema": "N26-conditional-executor-contract-diagnostic-v1",
        "observed_at_utc": datetime.now(timezone.utc).isoformat(),
        "known_good_acceptance_sha256": sha(known_path),
        "known_good_metadata_contract_passed": True,
        "suspect_acceptance_sha256": sha(suspect_path),
        "suspect_schema": suspect["schema"],
        "suspect_contract_rejected": True,
        "suspect_contract_error": suspect_error,
        "reported_executor_file": claimed_file,
        "reported_executor_sha256": suspect.get("executed_checker_sha256"),
        "actual_compat_producer_file": str(args.compat_producer.resolve()),
        "actual_compat_producer_sha256_now": producer_sha,
        "actual_producer_not_bound_as_own_executor": claimed_file != args.compat_producer.name,
        "reported_negative_controls": suspect.get("negative_controls_rejected"),
        "required_negative_controls": REJECTIONS,
        "missing_conditional_negative_controls": [
            label for label in REJECTIONS
            if label not in suspect.get("negative_controls_rejected", [])
        ],
        "guard_rejection_controls_passed": rejected,
        "metadata_only_not_a_geometric_replay": True,
        "old_files_modified": False,
        "new_geometric_payments": 0,
        "global_optimality_proved": False,
        "executed_diagnostic_sha256": sha(__file__),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(evidence, indent=2) + "\n")
    print(json.dumps(evidence, indent=2), flush=True)


if __name__ == "__main__":
    main()
