"""Floating discovery of a prefix cover by area exclusions/empty subtrees."""

import argparse
import json
from pathlib import Path

import numpy as np

from audit_prefix_origin import OriginReference
from probe_partial_multislope_area import solve_state
from probe_multislope_area import CAPS, ANGLE_SCALE, numeric_intercepts


WORK = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--b", type=int, choices=(14, 15, 16, 17), required=True)
    parser.add_argument("--max-states", type=int, default=500)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    reference = OriginReference(26, args.b, "dfs", caps=CAPS, scale=ANGLE_SCALE)
    intercepts = numeric_intercepts()
    cert = json.loads((WORK.parent / "outputs/n26-degree-area-lower-v1/CERTIFICATE.json").read_text())
    interior = np.array(cert["interior_area_upper_integers"]) / 10**12
    pending, events = [()], []
    area_count = empty_count = 0
    for number in range(args.max_states):
        if not pending:
            break
        prefix = pending.pop()
        state = reference.resolve(prefix)
        children = reference.children(state)
        descriptor = reference.entry(prefix, state, children)
        if state.pending and not children:
            events.append({"prefix": list(prefix), "kind": "empty"})
            empty_count += 1
            continue
        result = solve_state(args.b, descriptor, intercepts, interior)
        if result.get("floating_LP_success") and result["floating_area_upper_proposal"] < -0.001:
            events.append({"prefix": list(prefix), "kind": "area", "proposal": result})
            area_count += 1
        elif children:
            events.append({"prefix": list(prefix), "kind": "split", "child_count": len(children)})
            pending.extend(prefix + (i,) for i in reversed(range(len(children))))
        else:
            pending.append(prefix)
            events.append({"prefix": list(prefix), "kind": "unresolved-terminal", "proposal": result})
            break
        if (number + 1) % 20 == 0:
            print(json.dumps({"B": args.b, "states": number + 1, "area_proposed": area_count,
                              "empty": empty_count, "pending": len(pending), "last_prefix": list(prefix)}),
                  flush=True)
    args.output.write_text(json.dumps({"verified": False, "B": args.b, "events": events,
                                       "pending": [list(p) for p in pending],
                                       "global_optimality_proved": False}, separators=(",", ":")) + "\n")
    print(json.dumps({"verified": False, "B": args.b, "states": len(events),
                      "area_proposed": area_count, "empty": empty_count, "pending": len(pending)}), flush=True)


if __name__ == "__main__":
    main()
