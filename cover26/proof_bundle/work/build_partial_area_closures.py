"""Rationalize two shallow B14 subtree dual proposals; preserve old queues."""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_origin import OriginReference
from verify_partial_area_closures import degree_bounds, partial_bound, rationalize, sha
import verify_multislope_area as area


WORK = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    folder = WORK.parent / "outputs/n26-multislope-area-lower-v1"
    accepted_path = folder / "VERIFIED.json"
    accepted = json.loads(accepted_path.read_text())
    if not accepted["verified"]:
        raise ValueError("multi-slope coefficients not accepted")
    for name, digest in accepted["files"].items():
        if sha(folder / name) != digest:
            raise ValueError("changed accepted area input")
    multi = json.loads((folder / "MULTISLOPE-CERTIFICATE.json").read_text())
    old = json.loads((folder / "CERTIFICATE.json").read_text())
    proposals = json.loads((WORK / "n26-B14-adaptive-area-proposals-v1.json").read_text())
    cases = []
    reference = OriginReference(26, 14, "dfs", caps=area.CAPS, scale=area.D)
    for event in proposals["events"]:
        if event["kind"] != "area":
            continue
        prefix = tuple(event["prefix"])
        state = reference.resolve(prefix)
        proposal = event["proposal"]
        case = {"B": 14, "prefix": list(prefix), **rationalize(proposal, 14),
                "degree_bounds": [list(row) for row in degree_bounds(state, 14)],
                "angle_constraints": [list(row) for row in area.angle_rows(14, state.adjacency)]}
        value = partial_bound(case, state, old, multi)
        if value >= 0:
            raise ValueError("rationalized proposal is not a strict exclusion")
        case["proposed_area_upper_rational"] = str(value)
        cases.append(case)
    initial = WORK.parent / "outputs/n26-new-scope-frontiers-v1/N26-B14-frontier.json"
    data = json.loads(initial.read_text())
    pending = {tuple(row["prefix"]) for row in data["frontier"]}
    for case in cases:
        target = tuple(case["prefix"])
        path = next(p for p in pending if target[:len(p)] == p)
        while path != target:
            pending.remove(path)
            children = reference.children(reference.resolve(path))
            pending.update(path + (i,) for i in range(len(children)))
            path = target[:len(path) + 1]
        pending.remove(target)
    args.output.mkdir(parents=True)
    cert = {"schema": "N26-B14-partial-area-dual-certificate-v1", "N": 26, "B": 14,
            "area_acceptance_sha256": sha(accepted_path), "initial_frontier_sha256": sha(initial),
            "cases": cases, "expected_pending_prefixes": [list(p) for p in sorted(pending)],
            "full_catalog_complete": False, "global_optimality_proved": False}
    (args.output / "PARTIAL-CERTIFICATE.json").write_text(json.dumps(cert, indent=2) + "\n", encoding="utf-8")
    for original, name in (
        (initial, "INITIAL-FRONTIER.json"),
        (WORK / "verify_partial_area_closures.py", "verify_partial_area_closures.py"),
        (folder / "verify_multislope_area.py", "verify_multislope_area.py"),
        (folder / "verify_degree_area.py", "verify_degree_area.py"),
        (WORK / "audit_prefix_origin.py", "audit_prefix_origin.py"),
        (WORK / "audit_prefix_partition.py", "audit_prefix_partition.py"),
        (WORK / "n26-partial-area-proof.md", "PROOF.md")):
        (args.output / name).write_bytes(original.read_bytes())
    print(json.dumps({"built": True, "verified": False, "whole_subtree_proposals": len(cases),
                      "pending_prefixes": cert["expected_pending_prefixes"]}), flush=True)


if __name__ == "__main__":
    main()
