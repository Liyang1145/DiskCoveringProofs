"""Continue a bound accepted frontier using area, force and complete angle trees."""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

import numpy as np

from audit_prefix_origin import OriginReference
from audit_prefix_partition import linux
from new_upper_scope import sha
from n26_force import CAPS, D, U, angular_domain, force_check, rootbox
from n26_force_angles import verify_angular_tree
from probe_n26_force import Solver
from propose_force_angles import propose_angular_tree
from probe_partial_multislope_area import solve_state
from verify_partial_area_closures import degree_bounds, partial_bound, rationalize
import verify_multislope_area as area


WORK = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--source-acceptance", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--steps", type=int, default=600)
    parser.add_argument("--angle-checks", type=int, default=7)
    parser.add_argument("--candidate-control", type=Path)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    source = json.loads(args.source.read_text())
    accepted = json.loads(args.source_acceptance.read_text())
    # A bundle-level acceptance stores relative file keys.
    key = args.source.name if args.source.parent == args.source_acceptance.parent else linux(args.source)
    if not accepted["verified"] or accepted["files"][key] != sha(args.source):
        raise ValueError("source not bound by a successful exact acceptance")
    target = None
    if args.candidate_control:
        control = json.loads((args.candidate_control / "VERIFIED.json").read_text())
        if (not control["verified"] or not control["known_same_root_cover_survives_all_combinatorial_screens"]
                or control["B"] != 16):
            raise ValueError("candidate ordering has no accepted positive transport control")
        for path, digest in control["files"].items():
            if sha(path) != digest:
                raise ValueError("candidate ordering control bytes changed")
        target = tuple(json.loads((args.candidate_control / "CANDIDATE-PATH.json").read_text())["prefix"])
    folder = WORK.parent / "outputs/n26-multislope-area-lower-v1"
    area_report_path = folder / "VERIFIED.json"
    accepted_area = json.loads(area_report_path.read_text())
    for name, digest in accepted_area["files"].items():
        if sha(folder / name) != digest:
            raise ValueError("changed accepted area dependency")
    old = json.loads((folder / "CERTIFICATE.json").read_text())
    multi = json.loads((folder / "MULTISLOPE-CERTIFICATE.json").read_text())
    intercepts = np.array(multi["boundary_intercept_upper_integers"], dtype=float) / area.C
    interior = np.array(old["interior_area_upper_integers"], dtype=float) / area.C
    families = (14, 15, 16, 17)
    refs = {b: OriginReference(26, b, "dfs", caps=CAPS, scale=D) for b in families}
    pending = {b: {} for b in families}
    terminal = {b: set() for b in families}
    for row in source["pending_states"]:
        b, p = row["B"], tuple(row["prefix"])
        state = refs[b].resolve(p)
        if refs[b].entry(p, state, refs[b].children(state)) != {k: v for k, v in row.items() if k != "B"}:
            raise ValueError("source state disagrees with its prefix")
        pending[b][p] = state
    events = []
    counts = {b: dict.fromkeys(("split", "force", "force_tree", "area", "empty", "terminal"), 0) for b in families}
    for number in range(args.steps):
        b, ref = families[number % 4], refs[families[number % 4]]
        candidates = [p for p in pending[b] if p not in terminal[b]]
        if not candidates:
            continue
        owners = [p for p in candidates if b == 16 and target is not None and target[:len(p)] == p]
        if len(owners) > 1:
            raise ValueError("known candidate has overlapping pending owners")
        if b == 16 and target is not None and not owners and target not in terminal[b]:
            raise ValueError("known candidate owner disappeared during discovery")
        p = owners[0] if owners else min(
            candidates, key=lambda q: (len(ref.children(pending[b][q])), -len(q), q))
        state = pending[b][p]
        children = ref.children(state)
        event = {"B": b, "prefix": list(p)}
        kind = None
        if state.pending and not children:
            kind = "empty"
        elif len(children) != 1:
            try:
                proposal = solve_state(b, ref.entry(p, state, children), intercepts, interior)
                if proposal.get("floating_LP_success"):
                    cert = {"B": b, "prefix": list(p), **rationalize(proposal, b),
                            "degree_bounds": [list(pair) for pair in degree_bounds(state, b)],
                            "angle_constraints": [list(pair) for pair in area.angle_rows(b, state.adjacency)]}
                    if partial_bound(cert, state, old, multi) < 0:
                        kind, event["cert"] = "area", cert
            except ValueError:
                pass
            if kind is None:
                spec = {"N": 26, "B": b, "next": state.next_vertex, "faces": list(state.faces)}
                lower, upper = rootbox(angular_domain(spec))
                cert, status = Solver(spec).solve(lower, upper)
                if cert is not None:
                    kind, event["cert"] = "force", cert
                elif args.angle_checks > 0 and status["proposed_radius"] >= float(U) - .003:
                    tree = propose_angular_tree(spec, args.angle_checks, root_solution=(cert, status))
                    if tree["proposed_closed"]:
                        kind, event["nodes"] = "force_tree", tree["nodes"]
        if kind in ("force", "force_tree", "area", "empty"):
            pending[b].pop(p)
        elif not state.pending:
            kind = "terminal"
            terminal[b].add(p)
        else:
            kind = "split"
            pending[b].pop(p)
            for k, child in enumerate(children):
                pending[b][p + (k,)] = ref.normalize(child)
            event["all_child_count"] = len(children)
        event["kind"] = kind
        counts[b][kind] += 1
        events.append(event)
        if len(events) % 40 == 0:
            print(json.dumps({"new_events": len(events), "counts": counts,
                              "pending": {b: len(pending[b]) for b in families}}), flush=True)
    args.output.write_text(json.dumps({
        "verified": False, "N": 26, "radius_threshold": str(U),
        "source_frontier_sha256": sha(args.source),
        "source_acceptance_sha256": sha(args.source_acceptance),
        "source_acceptance_key": key, "source_acceptance_original_path": str(args.source_acceptance),
        "source_frontier_original_path": str(args.source),
        "area_acceptance_sha256": sha(area_report_path),
        "events": events, "counts": counts,
        "pending_prefixes": {str(b): [list(p) for p in sorted(pending[b])] for b in families},
        "terminal_pending_prefixes": {str(b): [list(p) for p in sorted(terminal[b])] for b in families},
        "full_catalog_complete": False, "global_optimality_proved": False},
        separators=(",", ":")) + "\n", encoding="utf-8")
    print(json.dumps({"verified": False, "events": len(events), "counts": counts,
                      "pending": {b: len(pending[b]) for b in families}}), flush=True)


if __name__ == "__main__":
    main()
