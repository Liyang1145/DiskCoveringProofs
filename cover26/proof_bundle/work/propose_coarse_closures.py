"""Discover disjoint ancestor exclusions of the accepted 542-state frontier."""

import argparse
from collections import Counter
from fractions import Fraction as F
import json
from pathlib import Path

import numpy as np

from audit_prefix_origin import OriginReference
from audit_prefix_partition import linux
from new_upper_scope import sha
from n26_force import U, angular_domain, force_check, rootbox
from n26_force_angles import verify_angular_tree
from probe_n26_force import Solver
from propose_force_angles import propose_angular_tree
from probe_partial_multislope_area import solve_state
from verify_partial_area_closures import degree_bounds, partial_bound, rationalize
import verify_multislope_area as area


WORK = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--probes", type=int, default=256)
    parser.add_argument("--angle-checks", type=int, default=63)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    out = WORK.parent / "outputs"
    source_path = out / "n26-force-forest-v1/FRONTIER.json"
    source = json.loads(source_path.read_text())
    accepted = json.loads((out / "n26-force-current-bundle-audit-v1.json").read_text())
    if accepted["files"][linux(source_path)] != sha(source_path):
        raise ValueError("source frontier is not currently bound")
    folder = out / "n26-multislope-area-lower-v1"
    area_report_path = folder / "VERIFIED.json"
    area_report = json.loads(area_report_path.read_text())
    for name, digest in area_report["files"].items():
        if sha(folder / name) != digest:
            raise ValueError("accepted area input changed")
    multi = json.loads((folder / "MULTISLOPE-CERTIFICATE.json").read_text())
    old = json.loads((folder / "CERTIFICATE.json").read_text())
    intercepts = np.array(multi["boundary_intercept_upper_integers"], dtype=float) / area.C
    interior = np.array(old["interior_area_upper_integers"], dtype=float) / area.C
    families = (14, 15, 16, 17)
    refs = {b: OriginReference(26, b, "dfs", caps=area.CAPS, scale=area.D) for b in families}
    remaining = {b: {tuple(row["prefix"]) for row in source["pending_states"] if row["B"] == b}
                 for b in families}
    candidates = {}
    for b in families:
        counts = Counter()
        for prefix in remaining[b]:
            counts.update(prefix[:i] for i in range(len(prefix) + 1))
        candidates[b] = sorted((p for p, n in counts.items() if n >= 2),
                               key=lambda p: (-counts[p], len(p), p))
    positions = dict.fromkeys(families, 0)
    closures, diagnostics = [], []
    probed = 0
    for turn in range(args.probes):
        b = families[turn % 4]
        while positions[b] < len(candidates[b]):
            prefix = candidates[b][positions[b]]
            positions[b] += 1
            descendants = [p for p in remaining[b] if p[:len(prefix)] == prefix]
            if descendants:
                break
        else:
            continue
        state = refs[b].resolve(prefix)
        spec = {"N": 26, "B": b, "next": state.next_vertex, "faces": list(state.faces)}
        row = {"B": b, "prefix": list(prefix), "source_active_descendants": len(descendants)}
        closure = None
        try:
            proposal = solve_state(b, refs[b].entry(prefix, state, refs[b].children(state)),
                                   intercepts, interior)
            if proposal.get("floating_LP_success"):
                case = {"B": b, "prefix": list(prefix), **rationalize(proposal, b),
                        "degree_bounds": [list(pair) for pair in degree_bounds(state, b)],
                        "angle_constraints": [list(pair) for pair in area.angle_rows(b, state.adjacency)]}
                bound = partial_bound(case, state, old, multi)
                if bound < 0:
                    closure = {**row, "kind": "area", "cert": case}
        except ValueError:
            pass
        if closure is None:
            lower, upper = rootbox(angular_domain(spec))
            cert, status = Solver(spec).solve(lower, upper)
            row["floating_root_radius_proposal"] = status["proposed_radius"]
            if cert is not None:
                checked = force_check(spec, lower, upper, cert)
                if F(checked["strict_margin_above_U"]) <= 0:
                    raise ValueError("root force proposal lost strictness")
                closure = {**row, "kind": "force", "cert": cert}
            elif status["proposed_radius"] >= float(U) - .003:
                tree = propose_angular_tree(spec, args.angle_checks, root_solution=(cert, status))
                row["angular_checks"] = tree["checks"]
                row["unresolved_angular_boxes"] = tree["pending_boxes"]
                if tree["proposed_closed"]:
                    verify_angular_tree(spec, tree["nodes"])
                    closure = {**row, "kind": "force_tree", "nodes": tree["nodes"]}
        probed += 1
        if closure:
            if any(tuple(c["prefix"])[:len(prefix)] == prefix or prefix[:len(c["prefix"])] == tuple(c["prefix"])
                   for c in closures if c["B"] == b):
                raise ValueError("new coarse exclusions overlap")
            closures.append(closure)
            remaining[b].difference_update(descendants)
        diagnostics.append(row)
        if probed % 10 == 0 or closure:
            print(json.dumps({"probed": probed, "closures": len(closures),
                              "removed_source_leaves": len(source["pending_states"]) - sum(map(len, remaining.values())),
                              "pending": {b: len(remaining[b]) for b in families},
                              "last_B": b, "last_prefix": list(prefix),
                              "last_closure": closure["kind"] if closure else None}), flush=True)
    args.output.write_text(json.dumps({
        "verified": False, "N": 26, "source_frontier_sha256": sha(source_path),
        "source_acceptance_sha256": sha(out / "n26-force-current-bundle-audit-v1.json"),
        "area_acceptance_sha256": sha(area_report_path),
        "closures": closures, "diagnostics": diagnostics,
        "pending_prefixes": {str(b): [list(p) for p in sorted(remaining[b])] for b in families},
        "full_catalog_complete": False, "global_optimality_proved": False},
        separators=(",", ":")) + "\n")
    print(json.dumps({"verified": False, "probed": probed, "closures": len(closures),
                      "pending": {b: len(remaining[b]) for b in families}}), flush=True)


if __name__ == "__main__":
    main()
