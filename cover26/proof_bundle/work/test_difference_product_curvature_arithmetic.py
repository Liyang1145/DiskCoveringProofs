"""Exact algebra/guard controls, NOT geometry or current-source admission."""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

import n26_difference_product_curvature as product
from n26_sharp_radius_constraints import SCALE
import verify_conditional_force_stage as binding


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    matrix = [[0 if i == j else SCALE for j in range(3)] for i in range(3)]
    reference = [F(0), F(1, 10), F(1, 5)]
    definition = [{
        "first_constraint": [0, 1], "second_constraint": [2, 0],
        "multiplier": "3/2"}]
    values = product.product_data(matrix, reference, definition)
    minorant = [[F(4), F(1, 3)], [F(1, 3), F(5)]]
    corrected = product.corrected_matrix(minorant, values)
    if corrected[0][1] != F(11, 6) or corrected[1][0] != F(11, 6):
        raise AssertionError("nonnegative-slack-product matrix sign changed")
    constant = sum(multiplier * u * v for multiplier, u, _, v, _ in values)
    if constant != F(81, 50):
        raise AssertionError("nonzero reference product constant was omitted")
    samples = 0
    for numerator_x in range(-10, 11):
        for numerator_y in range(-10, 11):
            x = [F(0), F(numerator_x, 10), F(numerator_y, 10)]
            if any(x[j] - x[i] > F(matrix[i][j], SCALE)
                   for i in range(3) for j in range(3)):
                continue
            delta = [x[i] - reference[i] for i in (1, 2)]
            quadratic = sum(delta[i] * minorant[i][j] * delta[j]
                            for i in range(2) for j in range(2)) / 2
            modified_quadratic = sum(delta[i] * corrected[i][j] * delta[j]
                                     for i in range(2) for j in range(2)) / 2
            shifted_linear = -sum(
                multiplier * sum((v*a[i] + u*b[i]) * delta[i] for i in range(2))
                for multiplier, u, a, v, b in values)
            slack_product = sum(
                multiplier * (u + sum(a[i]*delta[i] for i in range(2)))
                * (v + sum(b[i]*delta[i] for i in range(2)))
                for multiplier, u, a, v, b in values)
            lower = modified_quadratic - constant + shifted_linear
            if slack_product < 0 or quadratic != lower + slack_product or lower > quadratic:
                raise AssertionError("exact slack-product minorant identity/inequality failed")
            samples += 1
    reversed_pair = [{
        "first_constraint": [2, 0], "second_constraint": [0, 1],
        "multiplier": "3/2"}]
    if product.corrected_matrix(
            minorant, product.product_data(matrix, reference, reversed_pair)) != corrected:
        raise AssertionError("commutative nonnegative product depends on pair order")
    rejected = []

    def reject(name, call):
        try:
            call()
        except (ValueError, KeyError, TypeError):
            rejected.append(name)
        else:
            raise AssertionError("invalid slack-product arithmetic accepted: " + name)

    reject("negative-product-multiplier",
           lambda: product.product_data(matrix, reference, [{
               **definition[0], "multiplier": "-1"}]))
    reject("reference-violates-necessary-slack",
           lambda: product.product_data(matrix, [F(0), F(2), F(0)], definition))
    reject("boolean-difference-index",
           lambda: product.difference_slack(matrix, reference, [False, 1]))
    reject("self-difference-constraint",
           lambda: product.difference_slack(matrix, reference, [1, 1]))
    reject("out-of-range-difference-index",
           lambda: product.difference_slack(matrix, reference, [0, 3]))
    reject("missing-product-fields",
           lambda: product.product_data(matrix, reference, [{"multiplier": "1"}]))
    reject("duplicate-product",
           lambda: product.product_data(matrix, reference, definition + definition))
    reject("reversed-duplicate-product",
           lambda: product.product_data(matrix, reference, definition + reversed_pair))
    reject("empty-product-certificate",
           lambda: product.product_data(matrix, reference, []))
    reject("generic-model-relabelled-as-original-92-rods",
           lambda: product.bound(
               {"B": 16, "vertices": 62, "weights": [1]*92},
               [[0]*16 for _ in range(16)], [F(0)]*15, [F(1)]*15,
               {"reference_turns": ["0"]*15, "parts": 16,
                "signed_eta": ["1"]*15, "products": definition},
               F(1, 4), None))
    report = {
        "schema": "N26-difference-product-Taylor-arithmetic-controls-v1",
        "exact_nonzero_reference_product_constant_and_linear_expansion_checked": True,
        "exact_rational_feasible_sample_identities_checked": samples,
        "nonnegative_product_matrix_sign_and_commutative_pair_order_checked": True,
        "invalid_arithmetic_controls_rejected": rejected,
        "arithmetic_only_NOT_geometry_or_complete_latest_source_model_replay": True,
        "verified": False, "new_geometric_payments": 0,
        "candidate_whole_roots_removed": 0, "global_optimality_proved": False,
        "tested_product_module_sha256": binding.sha(product.__file__),
        "executed_test_sha256": binding.sha(__file__),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2), flush=True)


if __name__ == "__main__":
    main()
