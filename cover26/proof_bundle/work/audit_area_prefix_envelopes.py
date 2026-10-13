"""Exact degree-budget DP envelopes for every retained fresh-scope subtree.

No queue entry is deleted. A negative envelope is a separate geometric
transport exclusion, not a claim that the combinatorial subtree is empty.
"""

import argparse
from functools import lru_cache
from itertools import product
import json
from pathlib import Path

from audit_prefix_partition import WORK, publish
from run_new_scope_batch import audit
from verify_degree_area import COEFFICIENT_SCALE, SLOPE, parameter_gate
from new_upper_scope import local_path, sha


def degree_budget_dp(rows, total):
    """rows contain (minimum, maximum, coefficient sequence for d=2..25)."""
    minimum = sum(lo for lo, hi, coefficients in rows)
    extra = total - minimum
    if extra < 0 or total > sum(hi for lo, hi, coefficients in rows):
        return None
    best = [None] * (extra + 1)
    best[0] = 0
    for lo, hi, coefficients in rows:
        if not (2 <= lo <= hi <= 25 and len(coefficients) == 24):
            raise ValueError("invalid vertex degree interval")
        updated = [None] * (extra + 1)
        for used, value in enumerate(best):
            if value is None:
                continue
            for increase in range(min(hi - lo, extra - used) + 1):
                index = used + increase
                score = value + coefficients[lo + increase - 2]
                if updated[index] is None or score > updated[index]:
                    updated[index] = score
        best = updated
    return best[extra]


def completion_degree_bounds(n, b, state):
    adjacency = state["adjacency"]
    next_vertex = state["next"]
    regions = state["pending"]
    if len(adjacency) != n or sum(r["interior"] for r in regions) != n - next_vertex:
        raise ValueError("inconsistent partial-state budget")
    future_max = max((len(r["boundary"]) + r["interior"] - 1
                      for r in regions if r["interior"]), default=0)
    bounds = []
    for v in range(n):
        degree = adjacency[v].bit_count()
        minimum = max(2 if v < b else 3, degree)
        if v >= next_vertex:
            if degree:
                raise ValueError("unintroduced vertex already has edges")
            maximum = min(25, future_max)
        else:
            possible_new = 0
            for region in regions:
                boundary = region["boundary"]
                if v in boundary:
                    possible_new += sum(u != v and not (adjacency[v] >> u & 1)
                                        for u in boundary) + region["interior"]
            maximum = min(25, degree + possible_new)
        if maximum < minimum:
            # Empty completion domain, not a geometry conclusion.
            return None
        bounds.append((minimum, maximum))
    return tuple(bounds)


def regress_dp():
    # Exhaustive independent Cartesian-product oracle, including nonconcave,
    # signed coefficient tables so this does not silently assume greedy works.
    count = 0
    for case in range(30):
        rows = []
        for v in range(4):
            lo = 2 + (case + v) % 3
            hi = lo + (case * (v + 1) + v) % 3
            coefficients = tuple((d * d * (v + 2) + case * d) % 17 - 8 for d in range(2, 26))
            rows.append((lo, hi, coefficients))
        for total in range(sum(r[0] for r in rows) - 1, sum(r[1] for r in rows) + 2):
            oracle = [sum(row[2][d - 2] for row, d in zip(rows, ds))
                      for ds in product(*(range(row[0], row[1] + 1) for row in rows))
                      if sum(ds) == total]
            expected = max(oracle) if oracle else None
            if degree_budget_dp(rows, total) != expected:
                raise AssertionError("DP differs from independent exhaustive oracle")
            count += 1
    return count


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    folder = WORK.parent / "outputs/n26-degree-area-lower-v1"
    accepted_path = folder / "VERIFIED.json"
    accepted = json.loads(accepted_path.read_text())
    if not accepted["verified"] or accepted["global_optimality_proved"]:
        raise ValueError("area coefficients not accepted at the stated scope")
    for name, digest in accepted["files"].items():
        if sha(folder / name) != digest:
            raise ValueError("changed bound area input")
    cert_path = folder / "CERTIFICATE.json"
    cert = json.loads(cert_path.read_text())
    parameter_gate(cert)
    boundary_coefficients = tuple(cert["boundary_intercept_upper_integers"])
    interior_coefficients = tuple(cert["interior_area_upper_integers"])
    regression_cases = regress_dp()

    @lru_cache(None)
    def envelope(b, bounds):
        # Permuting vertices of the same class preserves the relaxed domain.
        bd, inside = bounds
        rows = [(lo, hi, boundary_coefficients) for lo, hi in bd]
        rows += [(lo, hi, interior_coefficients) for lo, hi in inside]
        value = degree_budget_dp(rows, 150 - 2 * b)
        return None if value is None else value + int(SLOPE * COEFFICIENT_SCALE)

    all_rows, families, inventory = [], [], [Path(__file__), accepted_path, cert_path]
    for b in (14, 15, 16, 17):
        report_path = WORK.parent / f"outputs/n26-new-B{b}-progress-v1.json"
        progress = json.loads(report_path.read_text())
        path = local_path(progress["latest_checkpoint"])
        if sha(path) != progress["checkpoint_sha256"]:
            raise ValueError("changed queue checkpoint")
        manifest = json.loads(path.read_text())
        result = audit(manifest)
        rows = []
        for prefix, state in sorted(result["pending"].items()):
            bounds = completion_degree_bounds(26, b, state)
            if bounds is None:
                value = None
            else:
                key = (tuple(sorted(bounds[:b])), tuple(sorted(bounds[b:])))
                value = envelope(b, key)
            rows.append({
                "B": b, "prefix": list(prefix),
                "degree_bounds": None if bounds is None else [list(row) for row in bounds],
                "degree_completion_domain_empty": value is None,
                "area_dual_upper_scaled_integer": value,
                "strictly_excluded_as_cover_transport_subtree": value is not None and value < 0,
            })
        families.append({"B": b, "pending_subtrees": len(rows),
                         "strict_area_excluded_subtrees": sum(row["strictly_excluded_as_cover_transport_subtree"] for row in rows),
                         "empty_relaxed_degree_domains": sum(row["degree_completion_domain_empty"] for row in rows),
                         "unresolved_subtrees": sum(not row["degree_completion_domain_empty"] and
                                                    not row["strictly_excluded_as_cover_transport_subtree"] for row in rows)})
        all_rows.extend(rows)
        inventory.extend((report_path, path))
        print(json.dumps(families[-1]), flush=True)
    report = {
        "schema": "N26-pending-subtree-area-degree-budget-envelopes-v1",
        "verified_exact_integer_DP": True, "independent_exhaustive_regression_cases": regression_cases,
        "coefficient_scale": COEFFICIENT_SCALE, "families": families,
        "subtree_envelopes": all_rows,
        "queues_unchanged": True, "not_a_combinatorial_exhaustion_claim": True,
        "written_partial_region_degree_bound_lemma_required": True,
        "full_catalog_complete": False, "global_lower_bound_proved": False,
        "global_optimality_proved": False,
        "files": {str(path): sha(path) for path in inventory}}
    publish(args.output, report)
    print(json.dumps({"area_excluded_subtrees": sum(r["strict_area_excluded_subtrees"] for r in families),
                      "unresolved_subtrees": sum(r["unresolved_subtrees"] for r in families),
                      "regression_cases": regression_cases}), flush=True)


if __name__ == "__main__":
    main()
