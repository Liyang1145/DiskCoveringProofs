"""Numerical support proposals followed by exact existing signed-leaf tests.

No source/model acceptance or geometric payment is performed. Existing pure
arithmetic backends remain unchanged. A caller owns the complete closed tree.
"""

from copy import deepcopy
from fractions import Fraction as F

import n26_broad_positive_support_suggestion as broader
import n26_extended_signed_support_forest as forest
import probe_robust_positive_support_references as robust


def step(original, box, tight, arcs, supports, kernel, tries, rounds, iterations, max_supports):
    lower, upper = box
    center = [(a+b)/2 for a, b in zip(lower, upper)]
    ordered = sorted(range(len(supports)), key=lambda support_index: sum(
        (float(a)-float(F(b)))**2 for a, b in zip(
            center, supports[support_index]["suggestion_point_turns"])))
    trials, alternations = [], 0
    for support_index in ordered[:tries]:
        trial = robust.test_reference(original, supports[support_index], box, center, tight, arcs)
        if trial["NEW_signed_certificate"] is not None:
            trials.append(trial)
        if trial["strict_actual_closed_leaf_exclusion"]:
            return (
                {"kind": forest.KIND, "support_index": support_index,
                 "certificate": deepcopy(trial["NEW_signed_certificate"])},
                None, alternations, None,
            )
    for round_index in range(rounds):
        if len(supports) >= max_supports:
            break
        best = None if not trials else max(trials, key=lambda trial: F(
            trial["signed_arithmetic_diagnosis"]["exact_arithmetic_result"]["strict_radius_margin"]))
        reference = center if best is None else list(map(F, best["reference_turns"]))
        alternations += 1
        strict = []
        for support, _, _ in broader.suggest(original, kernel, reference, iterations, 3):
            trial = robust.test_reference(original, support, box, reference, tight, arcs)
            if trial["NEW_signed_certificate"] is not None:
                trials.append(trial)
            if trial["strict_actual_closed_leaf_exclusion"]:
                strict.append(trial)
        if strict:
            trial = max(strict, key=lambda item: F(item["signed_arithmetic_diagnosis"][
                "exact_arithmetic_result"]["strict_radius_margin"]))
            return (
                {"kind": forest.KIND, "support_index": len(supports),
                 "certificate": deepcopy(trial["NEW_signed_certificate"])},
                trial["NEW_positive_support"], alternations, round_index+1,
            )
    best = None if not trials else max(trials, key=lambda trial: F(
        trial["signed_arithmetic_diagnosis"]["exact_arithmetic_result"]["strict_radius_margin"]))
    contributions = None if best is None else best["signed_arithmetic_diagnosis"][
        "exact_arithmetic_result"]["coordinate_contributions"]
    return {"kind": "OPEN"}, contributions, alternations, None
