"""Regression evidence for the new partial adapter, not global acceptance."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from sympy import Matrix

import n26_partial_prefix_quadratic_kernel as partial
from verify_conditional_force_stage import sha


def integer_kernel(spec):
    vertices, edges = partial.graph(spec)
    b = spec["B"]
    weights = [1 + k % 5 for k in range(len(edges))]
    lap = [[0] * vertices for _ in range(vertices)]
    for (u, v), w in zip(edges, weights):
        lap[u][u] += w
        lap[v][v] += w
        lap[u][v] -= w
        lap[v][u] -= w
    inverse, denominator = Matrix([row[b:] for row in lap[b:]]).to_DM().inv_den()
    nums, den = [[int(x) for x in row] for row in inverse.to_Matrix().tolist()], int(denominator)
    if den < 0:
        nums, den = [[-x for x in row] for row in nums], -den
    return {"schema": partial.SCHEMA, "spec": spec, "weight_scale": 1,
            "weight_numerators": weights, "inverse_denominator": str(den),
            "inverse_numerators": [[str(x) for x in row] for row in nums]}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    controls = []
    for b in (14, 15, 16, 17):
        fixtures = [
            {"N": 26, "B": b, "next": b, "faces": []},
            {"N": 26, "B": b, "next": b + 1, "faces": [3 | (1 << b)]},
            {"N": 26, "B": b, "next": b + 2,
             "faces": [3 | (1 << b), 1 | (1 << b) | (1 << (b + 1))]},
        ]
        for spec in fixtures:
            certificate = integer_kernel(spec)
            kernel = partial.kernel_gate(spec, certificate)
            controls.append({"B": b, "next": spec["next"], "present_faces": len(spec["faces"]),
                             **partial.identity_control(kernel)})
    spec = fixtures[-1]
    certificate = integer_kernel(spec)
    negatives = []

    def reject(label, changed):
        try:
            partial.kernel_gate(spec, changed)
        except (ValueError, TypeError, KeyError):
            negatives.append(label)
        else:
            raise AssertionError("invalid partial kernel accepted: " + label)

    bad = deepcopy(certificate)
    bad["schema"] = "N26-full-type-positive-quadratic-ground-kernel-v1"
    reject("sealed-full-type-schema-reused-as-partial-proof", bad)
    bad = deepcopy(certificate)
    bad["spec"]["faces"][-1] ^= (1 << 2) | (1 << 0)
    reject("different-already-present-face-complex", bad)
    bad = deepcopy(certificate)
    bad["spec"]["next"] += 1
    reject("future-unintroduced-center-added", bad)
    bad = deepcopy(certificate)
    bad["weight_numerators"][0] = 0
    reject("zero-positive-rod-weight", bad)
    bad = deepcopy(certificate)
    bad["weight_numerators"][0] = -1
    reject("negative-positive-rod-weight", bad)
    bad = deepcopy(certificate)
    bad["weight_numerators"].append(1)
    reject("future-unpresent-rod-added", bad)
    bad = deepcopy(certificate)
    bad["inverse_numerators"][0][0] = str(int(bad["inverse_numerators"][0][0]) + 1)
    reject("changed-exact-ground-inverse", bad)
    bad = deepcopy(certificate)
    bad["inverse_numerators"][0][1] = str(int(bad["inverse_numerators"][0][1]) + 1)
    reject("asymmetric-exact-ground-inverse", bad)
    bad = deepcopy(certificate)
    bad["inverse_denominator"] = "-1"
    reject("negative-ground-inverse-denominator", bad)
    bad = deepcopy(certificate)
    bad["weight_scale"] = F(1)
    reject("noninteger-positive-weight-scale", bad)
    bad = deepcopy(certificate)
    bad["silently_paid"] = True
    reject("unknown-kernel-payment-field", bad)
    report = {"schema": "N26-partial-prefix-energy-adapter-regression-evidence-v1",
              "regression_controls_passed": len(controls), "controls": controls,
              "invalid_kernel_controls_rejected": negatives,
              "current_transport_subtrees_removed_by_this_test": 0,
              "current_source_prefix_and_full_closed_domain_acceptance_still_required": True,
              "global_lower_bound_proved": False, "global_optimality_proved": False,
              "tested_adapter_sha256": sha(partial.__file__),
              "executed_test_sha256": sha(__file__)}
    args.report.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in report.items() if key != "controls"}, indent=2), flush=True)


if __name__ == "__main__":
    main()
