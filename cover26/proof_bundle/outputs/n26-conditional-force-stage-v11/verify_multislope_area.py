"""Exact multi-slope area envelopes and nonnegative graph-angle LP duals.

Standard library only. The floating solver is never imported or trusted here.
"""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

import verify_degree_area as base


SLOPES = tuple(F(q, 4) for q in (-12, -16, -18, -20, -21, -22, -23, -24,
                                -25, -26, -28, -32, -40, -48, -64, -96))
CAPS = (754112, 1555305, 2486507, 3880649)
D = 10**7
C = base.COEFFICIENT_SCALE


def base_gate(folder):
    path = folder / "BASE-ACCEPTANCE.json"
    report = json.loads(path.read_text(encoding="utf-8"))
    if not report["verified"] or report["global_optimality_proved"]:
        raise ValueError("unaccepted base area evidence")
    files = [path]
    for name, digest in report["files"].items():
        target = folder / ("BASE-PROOF.md" if name == "PROOF.md" else name)
        if target.parent != folder or base.sha(target) != digest:
            raise ValueError("changed base area dependency")
        files.append(target)
    if base.sha(base.__file__) != report["files"]["verify_degree_area.py"]:
        raise ValueError("executed base checker is not the published base code")
    cert = json.loads((folder / "CERTIFICATE.json").read_text())
    base.parameter_gate(cert)
    return cert, report, files


def parameter_gate(cert):
    if not (cert["N"] == 26 and tuple(map(F, cert["slopes"])) == SLOPES
            and cert["coefficient_scale"] == C and cert["angle_scale"] == D
            and cert["caps"] == list(CAPS)
            and cert["full_catalog_complete"] is False
            and cert["global_optimality_proved"] is False):
        raise ValueError("wrong multi-slope certificate scope")
    table = cert["boundary_intercept_upper_integers"]
    if (len(table) != 24 or any(len(row) != len(SLOPES) for row in table)
            or any(type(value) is not int for row in table for value in row)):
        raise ValueError("invalid multi-slope coefficient array")


def derive_tables(old_cert, arcs, progress=False):
    n, q = old_cert["bins"], old_cert["beta_grid_Q"]
    regular = [base.U**2 * F(d + 1, 2) * base.sin_iv(arcs, F(1, d + 1))[1]
               for d in range(2, 26)]
    maxima = [[None] * len(SLOPES) for _ in range(24)]
    for i in range(n):
        lo, hi = base.CAP * i / n, base.CAP * (i + 1) / n
        sine_lower = base.sin_iv(arcs, lo / 2)[0]
        if sine_lower > base.U:
            continue
        beta = None
        numerator = old_cert["beta_lower_numerators"][i]
        if 2 * sine_lower > base.U:
            beta = base.beta_gate(arcs, numerator, q, sine_lower)
        elif numerator:
            raise ValueError("unused beta lower entry")
        sine_gap = base.sin_iv(arcs, lo)[0]
        shifts = [-slope * hi for slope in SLOPES]
        for index, d in enumerate(range(2, 26)):
            polygon = regular[index]
            if beta is not None and beta >= F(1, 2 * (d + 1)):
                polygon = base.U**2 / 2 * (
                    base.sin_iv(arcs, 2 * beta)[1]
                    + d * base.sin_iv(arcs, (1 - 2 * beta) / d)[1])
            h_upper = polygon - sine_gap / 2
            for j, shift in enumerate(shifts):
                value = h_upper + shift
                if maxima[index][j] is None or value > maxima[index][j]:
                    maxima[index][j] = value
        if progress and (i + 1) % 1024 == 0:
            print(json.dumps({"multi_slope_continuous_bins_checked": i + 1, "of": n}), flush=True)
    return maxima


def table_claim_gate(cert, maxima):
    for proposed_row, row in zip(cert["boundary_intercept_upper_integers"], maxima):
        if any(F(proposed, C) < bound for proposed, bound in zip(proposed_row, row)):
            raise ValueError("multi-slope intercept understates a complete interval bound")


def adjacency_masks(faces):
    adjacency = [0] * 26
    for face in faces:
        for i in range(26):
            if face >> i & 1:
                adjacency[i] |= face ^ (1 << i)
    return adjacency


def angle_rows(b, adjacency):
    """Bitset path closure, independent of the proposal's shortest-path BFS."""
    one = [mask | (1 << i) for i, mask in enumerate(adjacency)]
    two, three = [], []
    for mask in one:
        value = 0
        for j in range(26):
            if mask >> j & 1:
                value |= one[j]
        two.append(value)
    for mask in two:
        value = 0
        for j in range(26):
            if mask >> j & 1:
                value |= one[j]
        three.append(value)
    result = set()
    for i in range(b):
        reach = [row[i] | row[(i + 1) % b] for row in (one, two, three)]
        for j in range(i + 1, b):
            ends = (1 << j) | (1 << ((j + 1) % b))
            distance = next((k for k, mask in enumerate(reach, 1) if mask & ends), None)
            if distance is None:
                continue
            cap = CAPS[distance]
            k = j - i
            if min(k, b - k) * CAPS[0] <= cap:
                continue
            forward, backward = k * CAPS[0] < D - cap, (b - k) * CAPS[0] < D - cap
            if forward and backward:
                raise ValueError("selected graph violates its initial angular screen")
            mask = sum(1 << v for v in range(i + 1, j + 1))
            if forward:
                result.add((mask, cap))
            elif backward:
                result.add((((1 << b) - 1) ^ mask, cap))
    return tuple(sorted(result))


def case_boundary_bound(case, cert):
    b = case["B"]
    degrees = case["boundary_degrees"]
    angles = case["angle_constraints"]
    if (b not in (14, 15, 16, 17) or len(degrees) != b
            or any(type(d) is not int or not 2 <= d <= 25 for d in degrees)
            or [list(row) for row in sorted(set(map(tuple, angles)))] != angles):
        raise ValueError("invalid boundary LP case")
    supports = b * len(SLOPES)
    total_rows = supports + len(angles) + 2 * b
    owner_weights = [F(0)] * b
    gamma = [F(0)] * b
    rhs, seen = F(0), set()
    for row, encoded in case["rational_dual_weights"]:
        w = F(encoded)
        if type(row) is not int or not 0 <= row < total_rows or row in seen or w <= 0:
            raise ValueError("invalid nonnegative dual weight")
        seen.add(row)
        if row < supports:
            owner, j = divmod(row, len(SLOPES))
            owner_weights[owner] += w
            gamma[owner] -= w * SLOPES[j]
            rhs += w * F(cert["boundary_intercept_upper_integers"][degrees[owner] - 2][j], C)
        elif row < supports + len(angles):
            mask, cap = angles[row - supports]
            if not (type(mask) is int and 0 < mask < 1 << b and cap in CAPS[1:]):
                raise ValueError("invalid angular window")
            rhs += w * F(cap, D)
            for i in range(b):
                if mask >> i & 1:
                    gamma[i] += w
        elif row < supports + len(angles) + b:
            owner = row - supports - len(angles)
            gamma[owner] += w
            rhs += w * F(CAPS[0], D)
        else:
            owner = row - supports - len(angles) - b
            gamma[owner] -= w
    if owner_weights != [F(1)] * b:
        raise ValueError("boundary auxiliary variable dual coefficient is not exactly one")
    return rhs - min(gamma)


def graph_case_gate(b, faces, case):
    adjacency = adjacency_masks(faces)
    if (case["B"] != b or case["boundary_degrees"] != [mask.bit_count() for mask in adjacency[:b]]
            or case["angle_constraints"] != [list(row) for row in angle_rows(b, adjacency)]):
        raise ValueError("graph does not belong to its claimed angular/degree case")
    return adjacency


def ceil_scaled(value):
    value *= C
    return -((-value.numerator) // value.denominator)


def graph_ledger(graphs, cases, cert, old_cert):
    mapping = cert["graph_to_case"]
    if len(mapping) != len(graphs) or any(type(k) is not int or not 0 <= k < len(cases) for k in mapping):
        raise ValueError("incomplete graph-to-dual mapping")
    boundary_bounds = [case_boundary_bound(case, cert) for case in cases]
    rows, counts = [], {"selected_graphs": len(graphs), "strictly_excluded_graphs": 0,
                       "still_unresolved_graphs": 0, "dual_cases": len(cases)}
    closest = None
    used = set()
    for index, ((b, faces), case_id) in enumerate(zip(graphs, mapping)):
        base.degrees(b, faces)
        adjacency = graph_case_gate(b, faces, cases[case_id])
        interior = sum(old_cert["interior_area_upper_integers"][adjacency[i].bit_count() - 2]
                       for i in range(b, 26))
        upper = ceil_scaled(boundary_bounds[case_id]) + interior
        excluded = upper < 0
        rows.append([index, case_id, upper, excluded])
        counts["strictly_excluded_graphs" if excluded else "still_unresolved_graphs"] += 1
        if excluded:
            closest = -upper if closest is None else min(closest, -upper)
        used.add(case_id)
    if used != set(range(len(cases))):
        raise ValueError("unused dual cases")
    counts["smallest_strict_area_margin"] = str(F(closest, C)) if closest is not None else None
    return rows, counts


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    old_cert, old_report, files = base_gate(args.input)
    path = args.input / "MULTISLOPE-CERTIFICATE.json"
    cert = json.loads(path.read_text())
    parameter_gate(cert)
    if cert["base_acceptance_sha256"] != base.sha(args.input / "BASE-ACCEPTANCE.json"):
        raise ValueError("unbound base acceptance")
    case_path = args.input / "CASE-CERTIFICATES.json"
    if cert["case_certificates_sha256"] != base.sha(case_path):
        raise ValueError("changed rational LP witnesses")
    cases = json.loads(case_path.read_text())
    arcs, _ = base.load_trig(args.input)
    maxima = derive_tables(old_cert, arcs, progress=True)
    table_claim_gate(cert, maxima)
    for index, d in enumerate(range(2, 26)):
        actual = base.U**2 * F(d, 2) * base.sin_iv(arcs, F(1, d))[1]
        if F(old_cert["interior_area_upper_integers"][index], C) < actual:
            raise ValueError("base interior area upper coefficient too small")
    graphs, _ = base.source_gate(args.input, old_cert)
    ledger, counts = graph_ledger(graphs, cases, cert, old_cert)
    negatives = []

    def reject(label, fn):
        try:
            fn()
        except (ValueError, KeyError, TypeError, IndexError):
            negatives.append(label)
        else:
            raise AssertionError("bad multi-slope certificate accepted: " + label)

    wrong = deepcopy(cert)
    wrong["boundary_intercept_upper_integers"][1][0] = 0
    reject("understated-envelope", lambda: table_claim_gate(wrong, maxima))
    wrong_case = deepcopy(cases[0])
    wrong_case["rational_dual_weights"].pop(0)
    reject("missing-unit-dual-mass", lambda: case_boundary_bound(wrong_case, cert))
    wrong_case = deepcopy(cases[0])
    wrong_case["rational_dual_weights"][0][1] = "-1"
    reject("negative-dual-weight", lambda: case_boundary_bound(wrong_case, cert))
    wrong_case = deepcopy(cases[0])
    wrong_case["boundary_degrees"][0] += 1
    reject("wrong-graph-degree-case", lambda: graph_case_gate(*graphs[0], wrong_case))
    wrong_case = deepcopy(cases[cert["graph_to_case"][0]])
    if not wrong_case["angle_constraints"]:
        raise AssertionError("regression needs a nontrivial angular case")
    wrong_case["angle_constraints"].pop()
    reject("omitted-angular-window", lambda: graph_case_gate(*graphs[0], wrong_case))
    wrong = deepcopy(cert)
    wrong["graph_to_case"].pop()
    reject("omitted-graph", lambda: graph_ledger(graphs, cases, wrong, old_cert))
    wrong = deepcopy(cert)
    wrong["global_optimality_proved"] = True
    reject("false-global-completion", lambda: parameter_gate(wrong))
    ledger_path = args.input / "MULTISLOPE-GRAPH-LEDGER.json"
    base.publish_or_match(ledger_path, ledger)
    files += [path, case_path, ledger_path, args.input / "verify_multislope_area.py",
              args.input / "PROOF.md"]
    report = {
        "schema": "N26-area-and-graph-angle-rational-dual-lower-v1",
        "verified": True, "all_continuous_gap_bins_checked": True,
        "rational_interval_bins": old_cert["bins"], "supporting_slopes": list(map(str, SLOPES)),
        "nonnegative_LP_duals_exactly_replayed": True,
        "graph_paths_independently_reconstructed_by_bitsets": True, **counts,
        "previous_single_slope_excluded_graphs": old_report["strictly_excluded_graphs"],
        "all_selected_graphs_excluded": counts["still_unresolved_graphs"] == 0,
        "exclusion_scope": "Selected generic irredundant Voronoi/star-padding transport types only",
        "full_catalog_complete": False, "any_family_exhausted": False,
        "unrestricted_reduction_final_joint_acceptance": False,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "negative_controls_rejected": negatives,
        "files": {p.name: base.sha(p) for p in files},
        "executed_checker_sha256": base.sha(__file__)}
    if report["executed_checker_sha256"] != report["files"]["verify_multislope_area.py"]:
        raise ValueError("executed and published multi-slope checkers differ")
    args.report.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k: v for k, v in report.items() if k != "files"}, indent=2), flush=True)


if __name__ == "__main__":
    main()
