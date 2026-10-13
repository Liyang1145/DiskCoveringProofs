"""Exact partial-subtree area duals and exhaustive prefix replacement."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path

from audit_prefix_origin import OriginReference
from audit_prefix_partition import check_frontier
import verify_multislope_area as area


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def degree_bounds(state, b):
    regions = state.pending
    if sum(j for boundary, j in regions) != 26 - state.next_vertex:
        raise ValueError("partial interior budget inconsistent")
    future = max((len(boundary) + j - 1 for boundary, j in regions if j), default=0)
    result = []
    for v, mask in enumerate(state.adjacency):
        current = mask.bit_count()
        lo = max(2 if v < b else 3, current)
        if v >= state.next_vertex:
            if current:
                raise ValueError("unintroduced vertex already adjacent")
            hi = min(25, future)
        else:
            extra = sum(j + sum(u != v and not (mask >> u & 1) for u in boundary)
                        for boundary, j in regions if v in boundary)
            hi = min(25, current + extra)
        if lo > hi:
            raise ValueError("no relaxed degree completion")
        result.append((lo, hi))
    return tuple(result)


def rationalize(proposal, b):
    q = 10**12
    weights = {row: F(round(F(str(value)) * q), q)
               for row, value in proposal["dual_nonzero_proposals"] if value > 0}
    for i in range(b):
        indices = [row for row in weights if row < b * len(area.SLOPES)
                   and row // len(area.SLOPES) == i]
        mass = sum((weights[row] for row in indices), F(0))
        if mass <= 0:
            raise ValueError("missing auxiliary-variable mass")
        for row in indices:
            weights[row] /= mass
    return {
        "rational_dual_weights": [[row, str(w)] for row, w in sorted(weights.items()) if w > 0],
        "degree_dual": str(F(round(F(str(proposal["degree_equality_multiplier_proposal"])) * q), q))}


def partial_bound(case, state, old_cert, multi_cert):
    b = case["B"]
    bounds = degree_bounds(state, b)
    angles = area.angle_rows(b, state.adjacency)
    if (case["degree_bounds"] != [list(row) for row in bounds]
            or case["angle_constraints"] != [list(row) for row in angles]):
        raise ValueError("partial dual uses different degree/angle domains")
    eta = [{d: F(0) for d in range(lo, hi + 1)} for lo, hi in bounds]
    gamma, mass = [F(0)] * b, [F(0)] * b
    rhs, seen = F(0), set()
    support_count = b * len(area.SLOPES)
    row_count = support_count + len(angles) + 2 * b
    for row, encoded in case["rational_dual_weights"]:
        w = F(encoded)
        if type(row) is not int or not 0 <= row < row_count or row in seen or w <= 0:
            raise ValueError("invalid partial nonnegative dual")
        seen.add(row)
        if row < support_count:
            owner, j = divmod(row, len(area.SLOPES))
            mass[owner] += w
            gamma[owner] -= w * area.SLOPES[j]
            for d in eta[owner]:
                eta[owner][d] -= w * F(multi_cert["boundary_intercept_upper_integers"][d - 2][j], area.C)
        elif row < support_count + len(angles):
            mask, cap = angles[row - support_count]
            rhs += w * F(cap, area.D)
            for i in range(b):
                if mask >> i & 1:
                    gamma[i] += w
        elif row < support_count + len(angles) + b:
            owner = row - support_count - len(angles)
            gamma[owner] += w
            rhs += w * F(area.CAPS[0], area.D)
        else:
            gamma[row - support_count - len(angles) - b] -= w
    if mass != [F(1)] * b:
        raise ValueError("partial auxiliary-variable masses are not exactly one")
    nu = F(case["degree_dual"])
    residue_minima = []
    for i, row in enumerate(eta):
        candidates = []
        for d, value in row.items():
            internal = F(old_cert["interior_area_upper_integers"][d - 2], area.C) if i >= b else F(0)
            candidates.append(value - internal - nu * d)
        residue_minima.append(min(candidates))
    return rhs - min(gamma) - nu * (150 - 2 * b) - sum(residue_minima, F(0))


def partition_for(cert, reference, initial):
    rows = check_frontier(initial, reference, (), 2)
    if not initial["origin_screen"]:
        raise ValueError("initial partition omitted origin condition")
    pending = {tuple(row["prefix"]): reference.resolve(tuple(row["prefix"])) for row in rows}
    excluded, splits = {}, []
    for case in cert["cases"]:
        target = tuple(case["prefix"])
        if any(target[:len(p)] == p or p[:len(target)] == target for p in excluded):
            raise ValueError("overlapping partial exclusions")
        ancestors = [p for p in pending if target[:len(p)] == p]
        if len(ancestors) != 1:
            raise ValueError("partial exclusion not within exactly one pending subtree")
        path = ancestors[0]
        while path != target:
            state = pending.pop(path)
            children = reference.children(state)
            if not children:
                raise ValueError("exclusion prefix extends past an empty/terminal state")
            for index, child in enumerate(children):
                pending[path + (index,)] = child
            splits.append({"prefix": list(path), "all_child_count": len(children)})
            path = target[:len(path) + 1]
            if path not in pending:
                raise ValueError("exclusion prefix child index invalid")
        excluded[target] = pending.pop(target)
    expected = [list(p) for p in sorted(pending)]
    if cert["expected_pending_prefixes"] != expected:
        raise ValueError("pending cover-transport frontier lost a sibling")
    return pending, excluded, splits


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--area-bundle", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    area_report_path = args.area_bundle / "VERIFIED.json"
    area_report = json.loads(area_report_path.read_text())
    if not area_report["verified"] or area_report["global_optimality_proved"]:
        raise ValueError("multi-slope area arithmetic unaccepted")
    for name, digest in area_report["files"].items():
        if area.base.sha(args.area_bundle / name) != digest:
            raise ValueError("changed accepted multi-slope input")
    old_cert = json.loads((args.area_bundle / "CERTIFICATE.json").read_text())
    multi_cert = json.loads((args.area_bundle / "MULTISLOPE-CERTIFICATE.json").read_text())
    area.parameter_gate(multi_cert)
    cert_path = args.input / "PARTIAL-CERTIFICATE.json"
    cert = json.loads(cert_path.read_text())
    b = cert["B"]
    if (cert["N"] != 26 or b != 14 or cert["area_acceptance_sha256"] != sha(area_report_path)
            or cert["full_catalog_complete"] or cert["global_optimality_proved"]):
        raise ValueError("wrong partial closure scope")
    initial_path = args.input / "INITIAL-FRONTIER.json"
    if sha(initial_path) != cert["initial_frontier_sha256"]:
        raise ValueError("changed initial root partition")
    initial = json.loads(initial_path.read_text())
    reference = OriginReference(26, b, "dfs", caps=area.CAPS, scale=area.D)
    pending, excluded, splits = partition_for(cert, reference, initial)
    bounds = []
    for case in cert["cases"]:
        if case["B"] != b:
            raise ValueError("mixed family dual")
        value = partial_bound(case, excluded[tuple(case["prefix"])], old_cert, multi_cert)
        if value >= 0:
            raise ValueError("partial subtree lacks a strict negative area bound")
        bounds.append({"prefix": case["prefix"], "area_dual_strict_upper": str(value)})
    negatives = []

    def reject(label, fn):
        try:
            fn()
        except (ValueError, KeyError, TypeError, IndexError):
            negatives.append(label)
        else:
            raise AssertionError("bad partial closure accepted: " + label)

    wrong = deepcopy(cert)
    wrong["expected_pending_prefixes"].pop()
    reject("lost-pending-sibling", lambda: partition_for(wrong, reference, initial))
    wrong = deepcopy(cert)
    wrong["cases"].append(wrong["cases"][0])
    reject("duplicate-exclusion", lambda: partition_for(wrong, reference, initial))
    wrong_case = deepcopy(cert["cases"][0])
    wrong_case["rational_dual_weights"].pop(0)
    state = excluded[tuple(wrong_case["prefix"])]
    reject("nonunit-partial-dual-mass", lambda: partial_bound(wrong_case, state, old_cert, multi_cert))
    wrong_case = deepcopy(cert["cases"][0])
    wrong_case["rational_dual_weights"][0][1] = "-1"
    reject("negative-partial-dual", lambda: partial_bound(wrong_case, state, old_cert, multi_cert))
    wrong_case = deepcopy(cert["cases"][0])
    wrong_case["degree_bounds"][0][1] = 25
    reject("changed-partial-degree-domain", lambda: partial_bound(wrong_case, state, old_cert, multi_cert))
    wrong_initial = deepcopy(initial)
    wrong_initial["frontier"].pop()
    reject("omitted-initial-subtree", lambda: partition_for(cert, reference, wrong_initial))
    frontier_data = {
        "schema": "N26-B14-area-filtered-cover-transport-frontier-v1",
        "N": 26, "B": b, "area_excluded_prefixes": [list(p) for p in sorted(excluded)],
        "all_splits": splits,
        "pending": [reference.entry(p, state, reference.children(state)) for p, state in sorted(pending.items())],
        "combinatorial_original_queue_unchanged": True,
        "family_exhausted": False, "global_optimality_proved": False}
    frontier_path = args.input / "COVER-TRANSPORT-FRONTIER.json"
    area.base.publish_or_match(frontier_path, frontier_data)
    files = [cert_path, initial_path, frontier_path, args.input / "PROOF.md",
             args.input / "verify_partial_area_closures.py", args.input / "verify_multislope_area.py",
             args.input / "verify_degree_area.py", args.input / "audit_prefix_origin.py",
             args.input / "audit_prefix_partition.py"]
    for name in ("verify_multislope_area.py", "verify_degree_area.py"):
        if sha(args.input / name) != area_report["files"][name]:
            raise ValueError("partial closure imports changed arithmetic code")
    report = {
        "schema": "N26-B14-exact-area-excluded-prefixes-v1",
        "verified": True, "N": 26, "B": b,
        "strictly_excluded_whole_transport_subtrees": len(excluded),
        "strict_area_bounds": bounds, "pending_cover_transport_subtrees": len(pending),
        "pending_prefixes": [list(p) for p in sorted(pending)],
        "all_sibling_replacements_independently_reconstructed": True,
        "all_future_degree_assignments_covered": True,
        "original_combinatorial_queues_preserved": True,
        "family_exhausted": False, "full_catalog_complete": False,
        "unrestricted_reduction_final_joint_acceptance": False,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "negative_controls_rejected": negatives,
        "area_bundle_acceptance_sha256": sha(area_report_path),
        "files": {p.name: sha(p) for p in files},
        "executed_checker_sha256": sha(__file__)}
    if report["executed_checker_sha256"] != report["files"]["verify_partial_area_closures.py"]:
        raise ValueError("executed and published partial checkers differ")
    args.report.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k: v for k, v in report.items() if k != "files"}, indent=2), flush=True)


if __name__ == "__main__":
    main()
