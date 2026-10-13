"""Rejection tests on the actual accepted 957 seed snapshot, not geometry."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

import n26_candidate_seed_extension as contract
from verify_conditional_force_stage import read, sha


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--source-index", type=int, required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    row = next(row for row in read(args.source / "PENDING-ANGLES.json") if row["index"] == args.source_index)
    seed = next(item for item in read(args.source / "PROPOSAL.json")["forests"]
                if item["source_OPEN_index"] == args.source_index)
    contract.gate(row, seed, seed)
    rejected = []

    def reject(label, changed):
        try:
            contract.gate(row, seed, changed)
        except (ValueError, KeyError, TypeError, IndexError):
            rejected.append(label)
        else:
            raise AssertionError("invalid accepted-seed extension contract passed: " + label)

    bad = deepcopy(seed)
    bad["source_OPEN_index"] = 1151
    reject("previously-paid-current-root-substituted", bad)
    bad = deepcopy(seed)
    bad["source_OPEN_index"] = True
    reject("boolean-instead-of-original-root-index", bad)
    bad = deepcopy(seed)
    bad["actual_source_closed_box"]["sharp_lower"][0] = str(F(row["sharp_lower"][0]) - 1)
    reject("full-current-root-bound-changed", bad)
    bad = deepcopy(seed)
    bad["nodes"] = bad["nodes"][:-1]
    reject("accepted-node-truncated", bad)
    bad = deepcopy(seed)
    next(node for node in bad["nodes"] if node["kind"] == "SPLIT")["children"].reverse()
    reject("accepted-closed-sibling-ownership-rewired", bad)
    bad = deepcopy(seed)
    next(node for node in bad["nodes"] if node["kind"] == "SPLIT")["mid"] = "0"
    reject("accepted-shared-midpoint-changed", bad)
    bad = deepcopy(seed)
    paid = next(i for i, node in enumerate(bad["nodes"]) if node["kind"] == "ENERGY")
    bad["nodes"][paid] = {"kind": "OPEN"}
    reject("accepted-paid-leaf-reopened", bad)
    bad = deepcopy(seed)
    next(node for node in bad["nodes"] if node["kind"] == "ENERGY")["certificate"]["eta"] = "-1"
    reject("accepted-energy-certificate-changed", bad)
    # A contract may allow an OPEN leaf to be refined. Its geometry is still
    # rejected or proved independently by the original exact forest replayer.
    allowed = deepcopy(seed)
    opened = next(i for i, node in enumerate(allowed["nodes"]) if node["kind"] == "OPEN")
    children = [len(allowed["nodes"]), len(allowed["nodes"]) + 1]
    allowed["nodes"][opened] = {"kind": "SPLIT", "axis": 0, "mid": "1/2", "children": children}
    allowed["nodes"].extend([{"kind": "OPEN"}, {"kind": "OPEN"}])
    refined = contract.gate(row, seed, allowed)
    report = {
        "schema": "N26-accepted-candidate-seed-extension-contract-regression-v1",
        "actual_source_acceptance_sha256": sha(args.source / "VERIFIED.json"),
        "actual_seed_proposal_sha256": sha(args.source / "PROPOSAL.json"),
        "tested_seed_contract_sha256": sha(contract.__file__),
        "source_OPEN_index": args.source_index,
        "unchanged_accepted_seed_control_passed": True,
        "OPEN_only_structural_extension_control_passed": True,
        "allowed_OPEN_extension_contract": refined,
        "invalid_seed_extension_controls_rejected": rejected,
        "source_snapshot_and_structure_only_not_a_geometric_replay": True,
        "new_geometric_candidate_payments": 0,
        "global_lower_bound_proved": False,
        "global_optimality_proved": False,
        "executed_test_sha256": sha(__file__),
    }
    args.report.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2), flush=True)


if __name__ == "__main__":
    main()
