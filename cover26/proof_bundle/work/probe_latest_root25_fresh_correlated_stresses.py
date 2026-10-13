"""Apply the freshly generated full134rod stresses to actual whole OPEN boxes."""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

import n26_pairwise_affine_energy as affine
import n26_typed_arithmetic_context as codec
import probe_balanced_full134rod_minimax as balanced
import verify_conditional_force_stage as binding


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    record_path = Path("outputs/n26-latest-root25-primal-versus-fresh-stress-v1.json")
    record = binding.read(record_path)
    digests = dict(record["input_sha256"])
    for text, digest in digests.items():
        if binding.sha(Path(text)) != digest:
            raise ValueError("fresh primal/stress source association changed")
    digests[str(record_path)] = binding.sha(record_path)
    digests[__file__] = binding.sha(__file__)
    resource = Path("outputs/n26-original-candidate-arithmetic-context-v1")
    original = codec.gate(binding.read(resource/"CONTEXT.json")["typed_context"])["original"]
    full = balanced.full
    model = full.model_gate(original["data"][0], original["reference"], original["data"][3])
    arcs = binding.force.load_trig(resource)[0]
    radius = F(original["radius"])
    helper = balanced.old.prior_producer
    numerical_helper = helper.previous.producer.old_probe
    contractor = helper.previous.producer.latest_controls.producer.BASE
    modules = (full, helper, numerical_helper, contractor, affine)
    digests.update({module.__file__: binding.sha(module.__file__) for module in modules})
    results = []
    for item in record["results"]:
        leaf = item["actual_latest_root25_v3_OPEN_leaf"]
        turns = list(map(F, item["actual_fixed_feasible_anchor_turns"]))
        kernel = full.kernel_gate(model, item["fresh_full134rod_positive_stress_kernel_certificate"])
        lower, upper = list(map(F, leaf["lower"])), list(map(F, leaf["upper"]))
        tight = [axis for axis, (a, b) in enumerate(zip(lower, upper)) if b-a <= F(1, 10**7)]
        targets = [("entire_actual_latest_OPEN_leaf", (lower, upper))]
        for width in (F(1, 500), F(1, 1000)):
            a = [max(x, t-width) for x, t in zip(lower, turns)]
            b = [min(x, t+width) for x, t in zip(upper, turns)]
            contracted = contractor.tighten(original["matrix"], a, b)
            independent = contractor.independently_contract(original["matrix"], a, b)
            if contracted is None or contracted != independent:
                raise ValueError("actual closed neighborhood contraction disagreed")
            targets.append(("proper_closed_halfwidth_"+str(width), contracted))
        trials = []
        for label, box in targets:
            full.hull.quadratic.reference_gate(turns, *box, original["matrix"])
            diagonal, diagonal_result = numerical_helper.suggest_bound(
                original, kernel, box, turns, tight, arcs, 16)
            certificate, result, numerical = None, None, None
            if diagonal is not None:
                certificate, result, numerical = helper.suggest(
                    kernel, original, {"lower": list(map(str, box[0])),
                                       "upper": list(map(str, box[1]))},
                    diagonal, arcs)
            data = affine.prepare(kernel, original["matrix"], *box, arcs)
            linear_certificate, linear_result, linear_numerical = affine.suggest(
                data, original["matrix"], radius)
            strict = (result is not None and result["arithmetic_strict_target_test_passed"]) or (
                linear_result is not None and linear_result["arithmetic_strict_entire_closed_leaf"])
            trials.append({
                "domain": label, "closed_lower": list(map(str, box[0])),
                "closed_upper": list(map(str, box[1])),
                "is_entire_actual_latest_OPEN_leaf": box == (lower, upper),
                "fresh_diagonal_certificate": diagonal, "fresh_diagonal_result": diagonal_result,
                "fresh_correlated_certificate": certificate, "fresh_correlated_result": result,
                "fresh_affine_certificate": linear_certificate, "fresh_affine_result": linear_result,
                "fresh_exact_closed_target_strict": strict,
                "numerical_correlated_suggestion_NOT_proof": numerical,
                "numerical_affine_suggestion_NOT_proof": linear_numerical,
            })
            print(json.dumps({"actual_latest_root25_OPEN_leaf": leaf["index"], "domain": label,
                              "fresh_exact_closed_target_strict": strict,
                              "entire_actual_OPEN_leaf": box == (lower, upper),
                              "verified": False, "new_geometric_payments": 0}), flush=True)
        results.append({"actual_latest_root25_v3_OPEN_leaf": leaf,
                        "fresh_full134rod_positive_stress_kernel_certificate":
                            item["fresh_full134rod_positive_stress_kernel_certificate"],
                        "trials": trials})
    for text, digest in digests.items():
        if binding.sha(Path(text)) != digest:
            raise ValueError("fresh closed-domain experiment input changed")
    report = {
        "schema": "N26-actual-latest-root25-fresh-correlated-stress-experiment-v1",
        "verified": False, "source_OPEN_index": 25, "results": results,
        "input_sha256": digests,
        "strict_entire_actual_OPEN_leaves": sum(
            trial["fresh_exact_closed_target_strict"] and trial["is_entire_actual_latest_OPEN_leaf"]
            for item in results for trial in item["trials"]),
        "strict_proper_closed_neighborhoods_NOT_whole_leaves": sum(
            trial["fresh_exact_closed_target_strict"] and not trial["is_entire_actual_latest_OPEN_leaf"]
            for item in results for trial in item["trials"]),
        "all_existing_forests_nodes_supports_ledgers_and_payments_UNMODIFIED": True,
        "arithmetic_DATA_NOT_complete_latest_geometry_source_interface": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "n27_started": False,
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")


if __name__ == "__main__":
    main()
