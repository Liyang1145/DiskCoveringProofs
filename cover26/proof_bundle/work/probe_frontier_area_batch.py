"""Propose whole-subtree area exclusions for the CURRENT 282-state frontier."""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

import numpy as np

from audit_prefix_origin import OriginReference
from audit_prefix_partition import linux
from new_upper_scope import sha
from probe_partial_multislope_area import solve_state
from verify_partial_area_closures import degree_bounds, partial_bound, rationalize
import verify_multislope_area as area


WORK = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    outputs = WORK.parent / "outputs"
    path = outputs / "n26-current-cover-transport-frontier-v1.json"
    accepted = json.loads((outputs / "n26-multislope-current-bundle-audit-v1.json").read_text())
    if accepted["files"][linux(path)] != sha(path):
        raise ValueError("current transport frontier not bound by prior audit")
    frontier = json.loads(path.read_text())
    folder = outputs / "n26-multislope-area-lower-v1"
    report = json.loads((folder / "VERIFIED.json").read_text())
    for name, digest in report["files"].items():
        if sha(folder / name) != digest:
            raise ValueError("changed accepted multi-slope input")
    multi = json.loads((folder / "MULTISLOPE-CERTIFICATE.json").read_text())
    old = json.loads((folder / "CERTIFICATE.json").read_text())
    intercepts = np.array(multi["boundary_intercept_upper_integers"], dtype=float) / area.C
    interior = np.array(old["interior_area_upper_integers"], dtype=float) / area.C
    references = {b: OriginReference(26, b, "dfs", caps=area.CAPS, scale=area.D)
                  for b in (14, 15, 16, 17)}
    rows, counts = [], {b: {"probed": 0, "rationally_negative": 0, "unresolved": 0, "empty": 0}
                       for b in references}
    for index, descriptor in enumerate(frontier["pending_states"]):
        b = descriptor["B"]
        prefix = tuple(descriptor["prefix"])
        reference = references[b]
        state = reference.resolve(prefix)
        expected = reference.entry(prefix, state, reference.children(state))
        if expected != {key: value for key, value in descriptor.items() if key != "B"}:
            raise ValueError("state differs from current prefix reconstruction")
        counts[b]["probed"] += 1
        proposal = solve_state(b, descriptor, intercepts, interior)
        row = {"B": b, "prefix": list(prefix), "proposal": proposal}
        if proposal.get("floating_LP_success"):
            case = {"B": b, "prefix": list(prefix), **rationalize(proposal, b),
                    "degree_bounds": [list(pair) for pair in degree_bounds(state, b)],
                    "angle_constraints": [list(pair) for pair in area.angle_rows(b, state.adjacency)]}
            bound = partial_bound(case, state, old, multi)
            row["rational_area_bound_proposal"] = str(bound)
            if bound < 0:
                row["rational_case_proposal"] = case
                counts[b]["rationally_negative"] += 1
            else:
                counts[b]["unresolved"] += 1
        elif state.pending and not reference.children(state):
            counts[b]["empty"] += 1
            row["empty_combinatorial_subtree"] = True
        else:
            counts[b]["unresolved"] += 1
        rows.append(row)
        if (index + 1) % 25 == 0:
            print(json.dumps({"probed": index + 1, "of": len(frontier["pending_states"]),
                              "counts": counts}), flush=True)
    args.output.write_text(json.dumps({
        "verified": False, "source_frontier_sha256": sha(path),
        "area_acceptance_sha256": sha(folder / "VERIFIED.json"),
        "counts": counts, "rows": rows, "global_optimality_proved": False},
        separators=(",", ":")) + "\n", encoding="utf-8")
    print(json.dumps({"verified": False, "counts": counts}), flush=True)


if __name__ == "__main__":
    main()
