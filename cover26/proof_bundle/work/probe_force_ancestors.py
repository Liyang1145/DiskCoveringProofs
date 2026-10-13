"""Find a shallow positive rod-force proposal along an unresolved terminal path."""

import argparse
import json
from pathlib import Path

from audit_prefix_origin import OriginReference
from n26_force import CAPS, D, angular_domain, rootbox
from probe_n26_force import Solver


WORK = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    data = json.loads((WORK / "n26-B14-adaptive-area-proposals-v1.json").read_text())
    terminal = tuple(data["events"][-1]["prefix"])
    reference = OriginReference(26, 14, "dfs", caps=CAPS, scale=D)
    records = []
    first = None
    for depth in range(5, len(terminal) + 1):
        prefix = terminal[:depth]
        state = reference.resolve(prefix)
        spec = {"N": 26, "B": 14, "next": state.next_vertex, "faces": list(state.faces)}
        lower, upper = rootbox(angular_domain(spec))
        cert, status = Solver(spec).solve(lower, upper)
        records.append({"prefix": list(prefix), "spec": spec, "lower": list(map(str, lower)),
                        "upper": list(map(str, upper)), "certificate_proposal": cert, "status": status})
        print(json.dumps({"depth": depth, "prefix": list(prefix),
                          "proposed_radius": status["proposed_radius"],
                          "positive_force_proposal": cert is not None}), flush=True)
        if cert is not None:
            first = depth
            break
    args.output.write_text(json.dumps({"verified": False, "first_positive_depth": first,
                                       "records": records, "global_optimality_proved": False}, indent=2) + "\n")


if __name__ == "__main__":
    main()
