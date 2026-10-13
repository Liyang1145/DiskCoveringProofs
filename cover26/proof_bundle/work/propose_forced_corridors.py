"""Collapse only forced successors of a bound frontier, then propose area duals."""

import argparse
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
    out = WORK.parent / "outputs"
    source_path = out / "n26-current-cover-transport-frontier-v1.json"
    source = json.loads(source_path.read_text())
    gate = json.loads((out / "n26-multislope-current-bundle-audit-v1.json").read_text())
    if gate["files"][linux(source_path)] != sha(source_path):
        raise ValueError("source frontier not bound")
    folder = out / "n26-multislope-area-lower-v1"
    accepted = json.loads((folder / "VERIFIED.json").read_text())
    for name, digest in accepted["files"].items():
        if sha(folder / name) != digest:
            raise ValueError("changed area inputs")
    multi = json.loads((folder / "MULTISLOPE-CERTIFICATE.json").read_text())
    old = json.loads((folder / "CERTIFICATE.json").read_text())
    intercepts = np.array(multi["boundary_intercept_upper_integers"], dtype=float) / area.C
    interior = np.array(old["interior_area_upper_integers"], dtype=float) / area.C
    refs = {b: OriginReference(26, b, "dfs", caps=area.CAPS, scale=area.D) for b in (14, 15, 16, 17)}
    rows, counts = [], {b: {"starts": 0, "forced_steps": 0, "empty": 0,
                           "negative_area": 0, "branching": 0, "terminal": 0}
                       for b in refs}
    for index, seed in enumerate(source["pending_states"]):
        b = seed["B"]
        ref = refs[b]
        original = prefix = tuple(seed["prefix"])
        state = ref.resolve(prefix)
        children = ref.children(state)
        if ref.entry(prefix, state, children) != {k: v for k, v in seed.items() if k != "B"}:
            raise ValueError("seed state changed")
        counts[b]["starts"] += 1
        steps = 0
        while len(children) == 1 and state.pending:
            prefix += (0,)
            state = ref.normalize(children[0])
            children = ref.children(state)
            steps += 1
            if steps > 50:
                raise ValueError("nonterminating forced chain")
        counts[b]["forced_steps"] += steps
        row = {"B": b, "start_prefix": list(original), "end_prefix": list(prefix),
               "forced_steps": steps}
        if state.pending and not children:
            row["kind"] = "empty"
            counts[b]["empty"] += 1
        else:
            descriptor = ref.entry(prefix, state, children)
            proposal = solve_state(b, descriptor, intercepts, interior)
            row["floating_proposal"] = proposal
            if proposal.get("floating_LP_success"):
                case = {"B": b, "prefix": list(prefix), **rationalize(proposal, b),
                        "degree_bounds": [list(pair) for pair in degree_bounds(state, b)],
                        "angle_constraints": [list(pair) for pair in area.angle_rows(b, state.adjacency)]}
                bound = partial_bound(case, state, old, multi)
                row["rational_area_upper_proposal"] = str(bound)
                if bound < 0:
                    row["kind"] = "area"
                    row["rational_case_proposal"] = case
                    counts[b]["negative_area"] += 1
                else:
                    row["kind"] = "branching" if state.pending else "terminal"
                    counts[b][row["kind"]] += 1
            else:
                row["kind"] = "branching" if state.pending else "terminal"
                counts[b][row["kind"]] += 1
            row["end_descriptor"] = descriptor
        rows.append(row)
        if (index + 1) % 50 == 0:
            print(json.dumps({"corridors": index + 1, "counts": counts}), flush=True)
    args.output.write_text(json.dumps({"verified": False, "source_frontier_sha256": sha(source_path),
                                       "area_acceptance_sha256": sha(folder / "VERIFIED.json"),
                                       "counts": counts, "rows": rows,
                                       "global_optimality_proved": False}, separators=(",", ":")) + "\n")
    print(json.dumps({"verified": False, "counts": counts}), flush=True)


if __name__ == "__main__":
    main()
