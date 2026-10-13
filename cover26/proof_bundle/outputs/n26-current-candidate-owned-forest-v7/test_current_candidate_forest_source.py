"""Accounting rejection controls on actual published forest snapshots.

The geometric forest is not paid by this test; its full semantic replay is
performed by n26_current_candidate_forest_source.gate during discovery.
"""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path
from unittest.mock import patch

import n26_current_candidate_forest_source as source


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    acceptance = source.read(args.source / "VERIFIED.json")
    names = ("ROOT-PAYMENTS.json", "PENDING-ANGLES.json", "ROOT-CLASSIFICATION.json",
             "PENDING-FOREST-LEAVES.json", "LOWER-LEDGER.json")
    snapshot = {name: source.read(args.source / name) for name in names}
    snapshot["CERTIFICATE.json"] = source.read(args.source / "CERTIFICATE.json")
    snapshot["POSITIVE-CONTROLS.json"] = source.read(args.source / "POSITIVE-CONTROLS.json")
    incoming = source.read(args.source / "SOURCE-PENDING-ANGLES.json")
    derived = tuple(snapshot[name] for name in names)
    values = (None, None, None, None, incoming, None, None)
    rejected = []

    def call(accepted, rows, outputs):
        with patch.object(source, "read", side_effect=lambda path: outputs[Path(path).name]), \
             patch.object(source.accepted_forest.source, "tiny_control",
                          return_value=snapshot["POSITIVE-CONTROLS.json"]):
            source.folded_outputs_gate(args.source, accepted, values, rows)

    call(acceptance, derived, snapshot)

    def reject(label, accepted, rows, outputs):
        try:
            call(accepted, rows, outputs)
        except (ValueError, KeyError, TypeError):
            rejected.append(label)
        else:
            raise AssertionError("invalid folded candidate accounting accepted: " + label)

    bad = deepcopy(snapshot)
    bad["ROOT-PAYMENTS.json"][0]["source_candidate_root_fully_lower_bounded"] = False
    reject("incomplete-root-claimed-paid", acceptance, tuple(bad[name] for name in names), bad)
    bad = deepcopy(snapshot)
    bad["ROOT-PAYMENTS.json"][0]["counts"]["LOCAL"] = 1
    reject("LOCAL-equality-region-falsely-emptied", acceptance, tuple(bad[name] for name in names), bad)
    bad = deepcopy(snapshot)
    bad["CERTIFICATE.json"]["discharged_actual_source_root_indices"][0] = -1
    reject("certificate-payment-owner-changed", acceptance, derived, bad)
    bad = deepcopy(snapshot)
    bad["CERTIFICATE.json"]["LOCAL_lower_bound_is_not_an_emptiness_claim"] = False
    reject("LOCAL-lower-bound-promoted-to-emptiness", acceptance, derived, bad)
    bad = deepcopy(snapshot)
    bad["PENDING-ANGLES.json"].pop()
    reject("unattempted-whole-root-lost", acceptance, tuple(bad[name] for name in names), bad)
    bad = deepcopy(snapshot)
    bad["PENDING-ANGLES.json"].append(deepcopy(incoming[0]))
    reject("retained-source-row-added-without-ownership", acceptance, tuple(bad[name] for name in names), bad)
    bad = deepcopy(snapshot)
    bad["PENDING-ANGLES.json"][0]["sharp_lower"][0] = str(
        F(bad["PENDING-ANGLES.json"][0]["sharp_lower"][0]) - 1
    )
    reject("retained-full-source-box-changed", acceptance, tuple(bad[name] for name in names), bad)
    bad_acceptance = deepcopy(acceptance)
    bad_acceptance["unresolved_closed_angle_boxes"] += 1
    reject("acceptance-current-root-count-changed", bad_acceptance, derived, snapshot)
    bad_acceptance = deepcopy(acceptance)
    bad_acceptance["radius_scope"] = "unconditional-original-U"
    reject("same-root-forest-promoted-to-U", bad_acceptance, derived, snapshot)
    report = {
        "schema": "N26-current-candidate-folded-forest-accounting-regression-v1",
        "actual_source_snapshot_sha256": source.sha(args.source / "VERIFIED.json"),
        "tested_source_loader_sha256": source.sha(source.__file__),
        "published_snapshot_accounting_control_passed": True,
        "invalid_folded_accounting_controls_rejected": rejected,
        "new_geometric_candidate_payments": 0,
        "source_snapshot_only_not_a_geometric_replay": True,
        "global_lower_bound_proved": False,
        "global_optimality_proved": False,
        "executed_test_sha256": source.sha(__file__),
    }
    args.report.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2), flush=True)


if __name__ == "__main__":
    main()
