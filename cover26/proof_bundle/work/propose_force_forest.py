"""Bounded discovery: preserve every sibling, propose area/force subtree closures."""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

import numpy as np

from audit_prefix_origin import OriginReference
from audit_prefix_partition import linux
from new_upper_scope import sha
from n26_force import angular_domain, force_check, rootbox
from probe_n26_force import Solver
from probe_partial_multislope_area import solve_state
from verify_partial_area_closures import degree_bounds, partial_bound, rationalize
import verify_multislope_area as area


WORK = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--steps", type=int, default=120)
    parser.add_argument("--resume", type=Path)
    args = parser.parse_args()
    if args.output.exists() or args.steps < 1:
        raise ValueError("fresh output and positive budget required")
    out = WORK.parent / "outputs"
    source_path = out / "n26-current-cover-transport-frontier-v1.json"
    source = json.loads(source_path.read_text())
    previous_audit = json.loads((out / "n26-multislope-current-bundle-audit-v1.json").read_text())
    if previous_audit["files"][linux(source_path)] != sha(source_path):
        raise ValueError("source frontier changed")
    folder = out / "n26-multislope-area-lower-v1"
    area_report = json.loads((folder / "VERIFIED.json").read_text())
    for name, digest in area_report["files"].items():
        if sha(folder / name) != digest:
            raise ValueError("changed accepted area input")
    multi = json.loads((folder / "MULTISLOPE-CERTIFICATE.json").read_text())
    old = json.loads((folder / "CERTIFICATE.json").read_text())
    intercepts = np.array(multi["boundary_intercept_upper_integers"], dtype=float) / area.C
    interior = np.array(old["interior_area_upper_integers"], dtype=float) / area.C
    families = (14, 15, 16, 17)
    refs = {b: OriginReference(26, b, "dfs", caps=area.CAPS, scale=area.D) for b in families}
    pending = {b: {} for b in families}
    terminal = {b: set() for b in families}
    for descriptor in source["pending_states"]:
        b, prefix = descriptor["B"], tuple(descriptor["prefix"])
        state = refs[b].resolve(prefix)
        if refs[b].entry(prefix, state, refs[b].children(state)) != {k: v for k, v in descriptor.items() if k != "B"}:
            raise ValueError("source state differs from its prefix")
        pending[b][prefix] = state
    events = []
    counts = {b: {"split": 0, "force": 0, "area": 0, "empty": 0, "terminal": 0} for b in families}
    if args.resume:
        previous = json.loads(args.resume.read_text())
        if (previous["source_frontier_sha256"] != sha(source_path)
                or previous["area_acceptance_sha256"] != sha(folder / "VERIFIED.json")):
            raise ValueError("resume belongs to a different source domain")
        for event in previous["events"]:
            b, prefix, kind = event["B"], tuple(event["prefix"]), event["kind"]
            if prefix not in pending[b] or prefix in terminal[b]:
                raise ValueError("resume repeats or loses a task")
            state = pending[b][prefix]
            children = refs[b].children(state)
            if kind == "force":
                spec = {"N": 26, "B": b, "next": state.next_vertex, "faces": list(state.faces)}
                lower, upper = rootbox(angular_domain(spec))
                checked = force_check(spec, lower, upper, event["force_certificate_proposal"])
                if F(checked["strict_margin_above_U"]) <= 0:
                    raise ValueError("resume force certificate is not strict")
                pending[b].pop(prefix)
            elif kind == "area":
                if partial_bound(event["area_case_proposal"], state, old, multi) >= 0:
                    raise ValueError("resume area certificate is not strict")
                pending[b].pop(prefix)
            elif kind == "empty":
                if not state.pending or children:
                    raise ValueError("resume false emptiness")
                pending[b].pop(prefix)
            elif kind == "terminal":
                if state.pending:
                    raise ValueError("resume false terminal")
                terminal[b].add(prefix)
            elif kind == "split":
                if not children or event["all_child_count"] != len(children):
                    raise ValueError("resume incomplete sibling split")
                pending[b].pop(prefix)
                for index, child in enumerate(children):
                    pending[b][prefix + (index,)] = refs[b].normalize(child)
            else:
                raise ValueError("resume unknown event")
            counts[b][kind] += 1
            events.append(event)
        for b in families:
            if previous["pending_prefixes"][str(b)] != [list(p) for p in sorted(pending[b])]:
                raise ValueError("resume pending partition differs")
    start_event = len(events)
    for number in range(args.steps):
        b = families[(start_event + number) % 4]
        ref = refs[b]
        candidates = [p for p in pending[b] if p not in terminal[b]]
        if not candidates:
            continue
        prefix = min(candidates, key=lambda p: (len(ref.children(pending[b][p])), -len(p), p))
        state = pending[b][prefix]
        children = ref.children(state)
        event = {"B": b, "prefix": list(prefix)}
        kind = None
        if state.pending and not children:
            kind = "empty"
        elif len(children) != 1:
            descriptor = ref.entry(prefix, state, children)
            try:
                proposal = solve_state(b, descriptor, intercepts, interior)
                if proposal.get("floating_LP_success"):
                    case = {"B": b, "prefix": list(prefix), **rationalize(proposal, b),
                            "degree_bounds": [list(row) for row in degree_bounds(state, b)],
                            "angle_constraints": [list(row) for row in area.angle_rows(b, state.adjacency)]}
                    upper = partial_bound(case, state, old, multi)
                    if upper < 0:
                        kind = "area"
                        event["area_case_proposal"] = case
                        event["area_upper_proposal"] = str(upper)
            except ValueError:
                pass
            if kind is None:
                spec = {"N": 26, "B": b, "next": state.next_vertex, "faces": list(state.faces)}
                lower, upper = rootbox(angular_domain(spec))
                cert, status = Solver(spec).solve(lower, upper)
                if cert is not None:
                    kind = "force"
                    event["force_certificate_proposal"] = cert
                    event["force_check_proposal"] = status["exact_reconstruction_result"]
        if kind in ("force", "area", "empty"):
            pending[b].pop(prefix)
        elif not state.pending:
            kind = "terminal"
            terminal[b].add(prefix)
        else:
            kind = "split"
            pending[b].pop(prefix)
            for index, child in enumerate(children):
                pending[b][prefix + (index,)] = ref.normalize(child)
            event["all_child_count"] = len(children)
        event["kind"] = kind
        counts[b][kind] += 1
        events.append(event)
        if len(events) % 10 == 0:
            print(json.dumps({"events": len(events), "counts": counts,
                              "pending": {b: len(pending[b]) for b in families}}), flush=True)
    data = {
        "verified": False, "N": 26, "radius_threshold": str(area.base.U),
        "source_frontier_sha256": sha(source_path),
        "area_acceptance_sha256": sha(folder / "VERIFIED.json"),
        "events": events, "counts": counts,
        "pending_prefixes": {str(b): [list(p) for p in sorted(pending[b])] for b in families},
        "terminal_pending_prefixes": {str(b): [list(p) for p in sorted(terminal[b])] for b in families},
        "previous_proposal_sha256": sha(args.resume) if args.resume else None,
        "full_catalog_complete": False, "global_optimality_proved": False}
    args.output.write_text(json.dumps(data, separators=(",", ":")) + "\n", encoding="utf-8")
    print(json.dumps({"verified": False, "events": len(events), "counts": counts,
                      "pending": {b: len(pending[b]) for b in families}}), flush=True)


if __name__ == "__main__":
    main()
